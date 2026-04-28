import HexLLL.Bench.Driver
import HexLLL.Bench.Families

/-!
# `hex_lll_bench` — HexLLL benchmark CLI

Usage:

    hex_lll_bench <seconds> [--out PATH] [--ladder]
                              [--max-per-family-seconds N]
                              [--seed N] [--runs N]

Reads run metadata from environment variables (set by
`scripts/bench/run.sh`):

    BENCH_GIT_SHA, BENCH_TOOLCHAIN, BENCH_HOSTNAME,
    BENCH_CPU_MODEL, BENCH_TS

Emits one JSONL row per measurement to `--out` (default: stdout).
-/

open HexLLL.Bench
open HexLLL.Bench.Families

structure CliArgs where
  seconds : Float := 5.0
  out : Option String := none
  ladder : Bool := false
  smoke : Bool := false
  maxPerFamilySeconds : Float := 30.0
  seed : UInt64 := 0xC0FFEE
  runs : Nat := 3
  deriving Inhabited

def usage : String :=
  "usage: hex_lll_bench <seconds> [--out PATH] [--ladder] " ++
  "[--max-per-family-seconds N] [--seed N] [--runs N]"

partial def parseArgs (args : List String) (acc : CliArgs) : Except String CliArgs :=
  match args with
  | [] => .ok acc
  | "--out" :: p :: rest => parseArgs rest { acc with out := some p }
  | "--ladder" :: rest => parseArgs rest { acc with ladder := true }
  | "--smoke" :: rest => parseArgs rest { acc with smoke := true }
  | "--max-per-family-seconds" :: v :: rest =>
      match v.toNat? with
      | some n => parseArgs rest { acc with maxPerFamilySeconds := n.toFloat }
      | none => .error s!"invalid --max-per-family-seconds: {v}"
  | "--seed" :: v :: rest =>
      match v.toNat? with
      | some n => parseArgs rest { acc with seed := n.toUInt64 }
      | none => .error s!"invalid --seed: {v}"
  | "--runs" :: v :: rest =>
      match v.toNat? with
      | some n => parseArgs rest { acc with runs := n }
      | none => .error s!"invalid --runs: {v}"
  | s :: rest =>
      match s.toNat? with
      | some n => parseArgs rest { acc with seconds := n.toFloat }
      | none => .error s!"unrecognised argument: {s} (only integer seconds supported)"

def main (args : List String) : IO UInt32 := do
  IO.eprintln "[bench] main start"
  let cli ← match parseArgs args {} with
            | .ok c => pure c
            | .error e => do
              IO.eprintln e
              IO.eprintln usage
              return 1
  IO.eprintln s!"[bench] args parsed: seconds={cli.seconds} runs={cli.runs}"
  let runMeta ← collectMeta "HexLLL" cli.seed
  IO.eprintln s!"[bench] meta collected"
  let settings : RunSettings :=
    { totalSeconds := cli.seconds
    , capNanos := (cli.maxPerFamilySeconds * 1.0e9).toUInt64.toNat
    , runs := cli.runs
    , ladder := cli.ladder }
  let runWith (h : IO.FS.Stream) : IO Unit := do
    for (weight, fam) in Families.all cli.seed do
      runFamily h runMeta settings (cli.seconds * weight) fam
    if cli.smoke then
      for fam in Families.smokeOnly cli.seed do
        -- Tiny share so smoke runs are short. We still go through
        -- the full pickParam → measure pipeline for shape consistency.
        runFamily h runMeta settings 0.05 fam
  match cli.out with
  | some path =>
      IO.FS.withFile path .write fun handle => runWith (IO.FS.Stream.ofHandle handle)
  | none =>
      let h ← IO.getStdout
      runWith h
  return 0
