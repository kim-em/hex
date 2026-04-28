import HexArith.Bench.Random

/-!
# HexArith benchmark driver

Timing wrapper, online calibration loop, JSONL emission. Parameterised
over a `FamilySpec` so each family in
[Families.lean](./Families.lean) plugs in identically.
-/

namespace HexArith.Bench

/-- Status enum for a single recorded measurement. -/
inductive Status
  | ok
  | timeout
  | budgetSkip
  | comparatorUnavailable
  | error
  deriving Repr, BEq

def Status.toJsonString : Status → String
  | .ok => "ok"
  | .timeout => "timeout"
  | .budgetSkip => "budget_skip"
  | .comparatorUnavailable => "comparator_unavailable"
  | .error => "error"

/-- Origin of the chosen parameter. -/
inductive ParamOrigin
  | predicted
  | discovered
  deriving Repr, BEq, Inhabited

def ParamOrigin.toJsonString : ParamOrigin → String
  | .predicted => "predicted"
  | .discovered => "discovered"

/-- Spec for one benchmark family with a single Nat parameter. -/
structure FamilySpec where
  name : String
  familyVersion : Nat := 1
  paramName : String
  expectedSlope : Float
  paramFloor : Nat
  paramCeiling : Nat
  /-- target seconds → suggested param -/
  initialGuess : Float → Nat
  /-- run one trial; driver times the call and records the returned hash -/
  runOne : Nat → IO UInt64

/-- Process-wide metadata captured once at startup. -/
structure RunMeta where
  schemaVersion : Nat := 1
  library : String
  gitSha : String
  leanToolchain : String
  hostname : String
  cpuModel : Option String
  ts : String
  seed : UInt64
  deriving Inhabited

def envOr (key default : String) : IO String := do
  return (← IO.getEnv key).getD default

def envOpt (key : String) : IO (Option String) := do
  match ← IO.getEnv key with
  | some v => pure (if v.isEmpty then none else some v)
  | none => pure none

def collectMeta (library : String) (seed : UInt64) : IO RunMeta := do
  let gitSha ← envOr "BENCH_GIT_SHA" "unknown"
  let toolchain ← envOr "BENCH_TOOLCHAIN" "unknown"
  let hostname ← envOr "BENCH_HOSTNAME" "unknown"
  let cpu ← envOpt "BENCH_CPU_MODEL"
  let ts ← envOr "BENCH_TS" "unknown"
  pure { library, gitSha, leanToolchain := toolchain, hostname, cpuModel := cpu, ts, seed }

/-- Time an `IO` action, returning `(value, elapsed_nanos)`. -/
@[inline] def timeNanos (act : IO α) : IO (α × Nat) := do
  let t₀ ← IO.monoNanosNow
  let v ← act
  let t₁ ← IO.monoNanosNow
  pure (v, t₁ - t₀)

/-- Result of online calibration. -/
structure CalibratedParam where
  param : Nat
  origin : ParamOrigin
  observedNanos : Nat
  cappedDuringSearch : Bool := false
  deriving Inhabited

partial def pickParamSearch (f : FamilySpec) (lo hi capNanos : Nat)
    (p t : Nat) (tries : Nat) (cappedSoFar : Bool) : IO CalibratedParam := do
  if tries = 0 then
    return { param := p, origin := .discovered, observedNanos := t, cappedDuringSearch := cappedSoFar }
  let p' :=
    if t < lo then min f.paramCeiling (p * 2)
    else max f.paramFloor (p / 2)
  if p' = p then
    return { param := p, origin := .discovered, observedNanos := t, cappedDuringSearch := cappedSoFar }
  let (_, t') ← timeNanos (f.runOne p')
  if t' > capNanos then
    return { param := p, origin := .discovered, observedNanos := t, cappedDuringSearch := true }
  if lo ≤ t' ∧ t' ≤ hi then
    return { param := p', origin := .discovered, observedNanos := t', cappedDuringSearch := cappedSoFar }
  pickParamSearch f lo hi capNanos p' t' (tries - 1) cappedSoFar

/--
Pick a parameter that brings one trial into `[targetNanos/2, targetNanos*2]`,
refusing to spend more than `capNanos` on any single trial. Initial guess
from `f.initialGuess`; otherwise ×2 / ÷2 geometric search for up to 6 steps.
-/
def pickParam (f : FamilySpec) (targetNanos capNanos : Nat) : IO CalibratedParam := do
  let lo := targetNanos / 2
  let hi := targetNanos * 2
  let p₀ := min f.paramCeiling
              (max f.paramFloor (f.initialGuess (targetNanos.toFloat / 1.0e9)))
  let (_, t₀) ← timeNanos (f.runOne p₀)
  if t₀ > capNanos then
    return { param := p₀, origin := .discovered, observedNanos := t₀, cappedDuringSearch := true }
  if lo ≤ t₀ ∧ t₀ ≤ hi then
    return { param := p₀, origin := .predicted, observedNanos := t₀ }
  pickParamSearch f lo hi capNanos p₀ t₀ 6 false

/-- Build a parameter ladder for scaling-law fitting (×2 per rung). -/
def buildLadder (f : FamilySpec) (anchor : Nat) (rungs : Nat) : Array Nat := Id.run do
  let mut acc : Array Nat := #[]
  let halfRungs := rungs / 2
  let mut p := anchor
  for _ in [0:halfRungs] do
    p := max f.paramFloor (p / 2)
  for _ in [0:rungs] do
    if f.paramFloor ≤ p ∧ p ≤ f.paramCeiling then
      acc := acc.push p
    p := p * 2
  return acc

/-- One JSONL row to emit. -/
structure RowRecord where
  family : String
  familyVersion : Nat
  param : Nat
  paramOrigin : ParamOrigin
  runIndex : Nat
  wallNanos : Nat
  resultHash : UInt64
  status : Status
  errMsg? : Option String := none
  comparator? : Option String := none
  comparatorVersion? : Option String := none

def jsonStr (s : String) : String :=
  let escaped := s.foldl (init := "") fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | c => acc.push c
  "\"" ++ escaped ++ "\""

def jsonOptStr : Option String → String
  | none => "null"
  | some s => jsonStr s

def hex64 (n : UInt64) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 n.toNat)

def renderRow (runMeta : RunMeta) (r : RowRecord) : String :=
  "{" ++ String.intercalate ","
    [ "\"schema_version\":" ++ toString runMeta.schemaVersion
    , "\"library\":" ++ jsonStr runMeta.library
    , "\"family\":" ++ jsonStr r.family
    , "\"family_version\":" ++ toString r.familyVersion
    , "\"param\":" ++ toString r.param
    , "\"param_origin\":" ++ jsonStr r.paramOrigin.toJsonString
    , "\"seed\":" ++ toString runMeta.seed.toNat
    , "\"run_index\":" ++ toString r.runIndex
    , "\"wall_nanos\":" ++ toString r.wallNanos
    , "\"result_hash\":" ++ jsonStr (hex64 r.resultHash)
    , "\"status\":" ++ jsonStr r.status.toJsonString
    , "\"error\":" ++ jsonOptStr r.errMsg?
    , "\"git_sha\":" ++ jsonStr runMeta.gitSha
    , "\"lean_toolchain\":" ++ jsonStr runMeta.leanToolchain
    , "\"hostname\":" ++ jsonStr runMeta.hostname
    , "\"cpu_model\":" ++ jsonOptStr runMeta.cpuModel
    , "\"comparator\":" ++ jsonOptStr r.comparator?
    , "\"comparator_version\":" ++ jsonOptStr r.comparatorVersion?
    , "\"ts\":" ++ jsonStr runMeta.ts
    ] ++ "}"

def emitRow (h : IO.FS.Stream) (runMeta : RunMeta) (r : RowRecord) : IO Unit :=
  h.putStrLn (renderRow runMeta r)

structure RunSettings where
  totalSeconds : Float
  capNanos : Nat
  runs : Nat := 3
  ladder : Bool := false
  ladderRungs : Nat := 5

/-- Non-ladder mode: calibrate, warm, take `runs` samples. -/
def runFamilyMeasured (h : IO.FS.Stream) (runMeta : RunMeta) (settings : RunSettings)
    (familyShareSeconds : Float) (f : FamilySpec) : IO Unit := do
  let targetNanos := (familyShareSeconds * 1.0e9).toUInt64.toNat
  IO.eprintln s!"[bench] {f.name}: calibrating (target {targetNanos / 1000000} ms)"
  let cal ← pickParam f targetNanos settings.capNanos
  IO.eprintln s!"[bench] {f.name}: param={cal.param} observed={cal.observedNanos / 1000000} ms"
  let _ ← timeNanos (f.runOne cal.param)
  for i in [0:settings.runs] do
    let (hash, wall) ← timeNanos (f.runOne cal.param)
    let status :=
      if cal.cappedDuringSearch ∧ wall > settings.capNanos then Status.budgetSkip
      else Status.ok
    emitRow h runMeta
      { family := f.name
      , familyVersion := f.familyVersion
      , param := cal.param
      , paramOrigin := cal.origin
      , runIndex := i
      , wallNanos := wall
      , resultHash := hash
      , status := status }

/-- Ladder mode: sweep params around the calibration anchor. -/
def runFamilyLadder (h : IO.FS.Stream) (runMeta : RunMeta) (settings : RunSettings)
    (familyShareSeconds : Float) (f : FamilySpec) : IO Unit := do
  let targetNanos := (familyShareSeconds * 1.0e9).toUInt64.toNat
  let cal ← pickParam f targetNanos settings.capNanos
  let ladder := buildLadder f cal.param settings.ladderRungs
  let mut skipRest := false
  for i in [0:ladder.size] do
    let p := ladder[i]!
    if skipRest then
      emitRow h runMeta
        { family := f.name, familyVersion := f.familyVersion
        , param := p, paramOrigin := cal.origin, runIndex := 0
        , wallNanos := 0, resultHash := 0, status := .budgetSkip }
    else
      let (hash, wall) ← timeNanos (f.runOne p)
      let st := if wall > settings.capNanos then Status.budgetSkip else Status.ok
      emitRow h runMeta
        { family := f.name, familyVersion := f.familyVersion
        , param := p, paramOrigin := cal.origin, runIndex := 0
        , wallNanos := wall, resultHash := hash, status := st }
      if wall > settings.capNanos then
        skipRest := true

def runFamily (h : IO.FS.Stream) (runMeta : RunMeta) (settings : RunSettings)
    (familyShareSeconds : Float) (f : FamilySpec) : IO Unit :=
  if settings.ladder then
    runFamilyLadder h runMeta settings familyShareSeconds f
  else
    runFamilyMeasured h runMeta settings familyShareSeconds f

end HexArith.Bench
