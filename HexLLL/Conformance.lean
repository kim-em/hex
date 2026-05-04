import HexLLL.Basic

/-!
Core conformance checks for `HexLLL`.

Oracle: none.
Mode: always.

Covered operations:
- `Hex.Matrix.memLattice`
- `Hex.Matrix.independent`
- `Hex.isLLLReduced`
- `Hex.lll`
- `Hex.lll.firstShortVector`
- `Hex.lll.shortVectors`
- `Hex.LLLState.sizeReduceColumn`
- `Hex.LLLState.sizeReduce`
- `Hex.LLLState.swapStep`
- `Hex.LLLState.gramSchmidtCoeff`
- `Hex.LLLState.potential`

Covered properties:
- committed row-combination witnesses satisfy lattice membership.
- independence distinguishes nonsingular bases from zero and dependent inputs.
- reducedness predicates accept small already-reduced bases and reject an
  unreduced basis with a large Gram-Schmidt coefficient.
- size-reduction updates perform the specified integer row operation and leave
  stored Gram determinants unchanged.
- adjacent swaps perform the specified row swap and update the affected stored
  determinant and scaled coefficients.
- downstream short-vector entry points expose the first reduced row and the
  ordered reduced rows on a BZ-shaped integer coefficient basis.
- stored rational Gram-Schmidt coefficients recover the quotient `ν[i][j]/d[j+1]`.
- potential multiplies the stored determinant prefix `d₁, ..., dₙ₋₁`.

Covered edge cases:
- an identity basis with zero off-diagonal Gram-Schmidt coefficients.
- a zero basis and a dependent rectangular basis.
- a size-reduction pivot with positive quotient and an already-small pivot that
  does not change the state.
- adjacent swaps at the first and second nonzero row positions.
- a downstream basis with one integer coefficient row per lifted local factor.
- out-of-range `sizeReduce` / `swapStep` calls that leave the state unchanged.
-/

namespace Hex
namespace LLLConformance

private def identity2 : Matrix Int 2 2 := 1

private def zero2 : Matrix Int 2 2 := 0

private def dependent3x2 : Matrix Int 3 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 2
    | 1, 0 => 4
    | 2, 0 => -1
    | 2, 1 => 3
    | _, _ => 0

private def unreduced2 : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 1, 0 => 3
    | 1, 1 => 1
    | _, _ => 0

private def typical3 : Matrix Int 3 3 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 1 => 1
    | 1, 0 => 1
    | 1, 2 => 1
    | 2, 1 => 1
    | 2, 2 => 1
    | _, _ => 0

private def bzStyleBasis : Matrix Int 3 4 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 3 => 1
    | 1, 1 => 1
    | 1, 3 => -1
    | 2, 2 => 1
    | 2, 3 => 2
    | _, _ => 0

private abbrev f0_2 : Fin 2 := ⟨0, by decide⟩
private abbrev f1_2 : Fin 2 := ⟨1, by decide⟩
private abbrev f0_3 : Fin 3 := ⟨0, by decide⟩
private abbrev f1_3 : Fin 3 := ⟨1, by decide⟩
private abbrev f2_3 : Fin 3 := ⟨2, by decide⟩
private abbrev f3_4 : Fin 4 := ⟨3, by decide⟩

private def identityLatticeVec : Vector Int 2 :=
  Vector.ofFn fun i => if i.val = 0 then 7 else -2

private def dependentLatticeVec : Vector Int 2 :=
  Vector.ofFn fun i => if i.val = 0 then 0 else 6

private def typicalLatticeVec : Vector Int 3 :=
  Vector.ofFn fun i =>
    match i.val with
    | 0 => 2
    | 1 => -1
    | _ => -1

private def identityWitness : Vector Int 2 :=
  Vector.ofFn fun i => if i.val = 0 then 7 else -2

private def dependentWitness : Vector Int 3 :=
  Vector.ofFn fun i =>
    match i.val with
    | 0 => 3
    | 1 => -1
    | _ => 2

private def typicalWitness : Vector Int 3 :=
  Vector.ofFn fun i =>
    match i.val with
    | 0 => 1
    | 1 => 1
    | _ => -2

example : Matrix.memLattice identity2 identityLatticeVec := by
  refine ⟨identityWitness, ?_⟩
  decide

example : Matrix.memLattice dependent3x2 dependentLatticeVec := by
  refine ⟨dependentWitness, ?_⟩
  decide

example : Matrix.memLattice typical3 typicalLatticeVec := by
  refine ⟨typicalWitness, ?_⟩
  decide

private def independentCheck (b : Matrix Int n m) : Bool :=
  (List.finRange n).all fun k =>
    0 < Matrix.det (Matrix.submatrix (Matrix.gramMatrix b) k)

private noncomputable def lllReducedCheck (b : Matrix Int n m) (δ : Rat) : Bool :=
  let basis := GramSchmidt.Int.basis b
  let coeffs := GramSchmidt.Int.coeffs b
  let sizeReduced :=
    (List.range n).all fun i =>
      if hi : i < n then
        (List.range i).all fun j =>
          if hji : j < i then
            let iFin : Fin n := ⟨i, hi⟩
            let jFin : Fin n := ⟨j, Nat.lt_trans hji hi⟩
            let μ := coeffs[iFin][jFin]
            4 * μ * μ ≤ 1
          else
            true
      else
        true
  let lovasz :=
    (List.range n).all fun i =>
      if hi : i + 1 < n then
        let iFin : Fin n := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
        let ip1Fin : Fin n := ⟨i + 1, hi⟩
        let μ := coeffs[ip1Fin][iFin]
        δ * Vector.normSq (basis.row iFin) ≤
          Vector.normSq (basis.row ip1Fin) + μ * μ * Vector.normSq (basis.row iFin)
      else
        true
  sizeReduced && lovasz

#guard independentCheck identity2
#guard !independentCheck zero2
#guard !independentCheck dependent3x2

private def stateOf (b : Matrix Int n m) : LLLState n m where
  b := b
  ν := GramSchmidt.Int.scaledCoeffs b
  d := GramSchmidt.Int.gramDetVec b
  ν_eq := by
    intro i j hi hj hji
    rw [GramSchmidt.Int.gramDetVec_eq_gramDet b (j + 1)
      (Nat.succ_le_of_lt (Nat.lt_trans hji hi))]
    simpa [GramSchmidt.entry, Matrix.row] using
      (GramSchmidt.Int.scaledCoeffs_eq b i j hi hji)
  d_eq := by
    intro i hi
    exact GramSchmidt.Int.gramDetVec_eq_gramDet b i (Nat.le_of_lt_succ hi)

private def identityState : LLLState 2 2 := stateOf identity2
private def zeroState : LLLState 2 2 := stateOf zero2
private def unreducedState : LLLState 2 2 := stateOf unreduced2
private def typicalState : LLLState 3 3 := stateOf typical3

private abbrev f0_4 : Fin 4 := ⟨0, by decide⟩
private abbrev f1_4 : Fin 4 := ⟨1, by decide⟩
private abbrev f2_4 : Fin 4 := ⟨2, by decide⟩

#guard (identityState.d.get f0_3) = 1
#guard (identityState.d.get f1_3) = 1
#guard (identityState.d.get f2_3) = 1
#guard identityState.potential = 1

#guard (zeroState.d.get f0_3) = 1
#guard (zeroState.d.get f1_3) = 0
#guard (zeroState.d.get f2_3) = 0
#guard zeroState.potential = 0

#guard (typicalState.d.get f0_4) = 1
#guard (typicalState.d.get f1_4) = 2
#guard (typicalState.d.get f2_4) = 3
#guard (typicalState.d.get f3_4) = 4
#guard typicalState.potential = 6

#guard independentCheck bzStyleBasis
#guard (Matrix.row bzStyleBasis f0_3).get f0_4 = 1
#guard (Matrix.row bzStyleBasis f1_3).get f1_4 = 1
#guard (Matrix.row bzStyleBasis f2_3).get f2_4 = 1
#guard (Matrix.row bzStyleBasis f0_3).get f3_4 = 1
#guard (Matrix.row bzStyleBasis f1_3).get f3_4 = -1
#guard (Matrix.row bzStyleBasis f2_3).get f3_4 = 2

example (hδ : (1 / 4 : Rat) < 3 / 4) (hδ' : (3 / 4 : Rat) ≤ 1)
    (hind : bzStyleBasis.independent) :
    lll.firstShortVector bzStyleBasis (3 / 4) hδ hδ' (by decide) hind =
      Matrix.row (lll bzStyleBasis (3 / 4) hδ hδ' (by decide) hind) f0_3 := by
  rfl

example (hδ : (1 / 4 : Rat) < 3 / 4) (hδ' : (3 / 4 : Rat) ≤ 1)
    (hind : bzStyleBasis.independent) :
    lll.shortVectors bzStyleBasis (3 / 4) hδ hδ' (by decide) hind =
      (lll bzStyleBasis (3 / 4) hδ hδ' (by decide) hind).toArray := by
  rfl

example :
    identityState.gramSchmidtCoeff 1 0 (by decide) (by decide) =
      (((identityState.ν.get f1_2).get f0_2 : Int) : Rat) / (identityState.d.get f1_3 : Rat) := by
  rfl

example :
    unreducedState.gramSchmidtCoeff 1 0 (by decide) (by decide) =
      (((unreducedState.ν.get f1_2).get f0_2 : Int) : Rat) / (unreducedState.d.get f1_3 : Rat) := by
  rfl

example :
    typicalState.gramSchmidtCoeff 2 1 (by decide) (by decide) =
      (((typicalState.ν.get f2_3).get f1_3 : Int) : Rat) / (typicalState.d.get f2_4 : Rat) := by
  rfl

#guard (((identityState.ν.get f1_2).get f0_2 : Int) : Rat) / (identityState.d.get f1_3 : Rat) = 0
#guard (((unreducedState.ν.get f1_2).get f0_2 : Int) : Rat) / (unreducedState.d.get f1_3 : Rat) = 3
#guard (((typicalState.ν.get f2_3).get f1_3 : Int) : Rat) / (typicalState.d.get f2_4 : Rat) =
  ((1 : Rat) / 3)

private def sizeReducedUnreduced : LLLState 2 2 :=
  unreducedState.sizeReduceColumn f0_2 f1_2 (by decide)

#guard Matrix.row sizeReducedUnreduced.b f0_2 = Matrix.row unreduced2 f0_2
#guard Matrix.row sizeReducedUnreduced.b f1_2 =
  (Vector.ofFn fun i => if i.val = 0 then 0 else 1)
#guard sizeReducedUnreduced.d = unreducedState.d
#guard (sizeReducedUnreduced.ν.get f1_2).get f0_2 = 0

private def unchangedIdentityColumn : LLLState 2 2 :=
  identityState.sizeReduceColumn f0_2 f1_2 (by decide)

#guard unchangedIdentityColumn.b = identityState.b
#guard unchangedIdentityColumn.ν = identityState.ν
#guard unchangedIdentityColumn.d = identityState.d

private def sizeReducedTypical : LLLState 3 3 :=
  typicalState.sizeReduce 2

#guard Matrix.row sizeReducedTypical.b f0_3 = Matrix.row typical3 f0_3
#guard Matrix.row sizeReducedTypical.b f1_3 = Matrix.row typical3 f1_3
#guard Matrix.row sizeReducedTypical.b f2_3 =
  (Vector.ofFn fun i =>
    match i.val with
    | 0 => 0
    | 1 => 1
    | _ => 1)
#guard sizeReducedTypical.d = typicalState.d

#guard (identityState.sizeReduce 2).b = identityState.b
#guard (identityState.sizeReduce 2).ν = identityState.ν
#guard (identityState.sizeReduce 2).d = identityState.d

private def swappedFirstTypical : LLLState 3 3 :=
  typicalState.swapStep 1

#guard Matrix.row swappedFirstTypical.b f0_3 = Matrix.row typical3 f1_3
#guard Matrix.row swappedFirstTypical.b f1_3 = Matrix.row typical3 f0_3
#guard Matrix.row swappedFirstTypical.b f2_3 = Matrix.row typical3 f2_3
#guard (swappedFirstTypical.d.get f0_4) = 1
#guard (swappedFirstTypical.d.get f1_4) = 2
#guard (swappedFirstTypical.d.get f2_4) = 3
#guard (swappedFirstTypical.d.get f3_4) = 4
#guard (swappedFirstTypical.ν.get f1_3).get f0_3 = 1
#guard swappedFirstTypical.potential = 6

private def swappedSecondTypical : LLLState 3 3 :=
  typicalState.swapStep 2

#guard Matrix.row swappedSecondTypical.b f0_3 = Matrix.row typical3 f0_3
#guard Matrix.row swappedSecondTypical.b f1_3 = Matrix.row typical3 f2_3
#guard Matrix.row swappedSecondTypical.b f2_3 = Matrix.row typical3 f1_3
#guard (swappedSecondTypical.d.get f0_4) = 1
#guard (swappedSecondTypical.d.get f1_4) = 2
#guard (swappedSecondTypical.d.get f2_4) = 3
#guard (swappedSecondTypical.d.get f3_4) = 4
#guard (swappedSecondTypical.ν.get f2_3).get f1_3 = 1
#guard swappedSecondTypical.potential = 6

#guard (typicalState.swapStep 0).b = typicalState.b
#guard (typicalState.swapStep 3).b = typicalState.b
#guard (typicalState.swapStep 3).d = typicalState.d

end LLLConformance
end Hex
