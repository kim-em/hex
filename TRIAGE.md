# Proof Triage

Scratch space for researching proof strategies. Once a proof is
understood and vetted, it gets incorporated into PLAN.md (under the
relevant library section) and deleted from here.

---

## Tier 1: Major Theorems

### 2. LLL short vector bound (`lll_short_vector`)

```lean
theorem lll_short_vector (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1)
    (hli : b.independent)
    (v : Vector Int m) :
    b.memLattice v → v ≠ 0 →
    (lll b δ hδ hδ' hli).row 0 |>.normSq ≤ α^(n-1) * v.normSq
  where α := 1 / (δ - 1/4)
```

**Hypotheses.** `δ ∈ (1/4, 1]` is required: `δ > 1/4` so that
`α = 1/(δ - 1/4)` is well-defined and positive; `δ ≤ 1` for
termination (the Lovász failure condition is strict, so each swap
gives `d_k^{new} < δ · d_k ≤ d_k`, strictly decreasing the potential
even at `δ = 1`).
Linear independence of the input basis ensures all Gram determinants
`d_k > 0`, which is needed for the GS orthogonalization to exist and
for the d-representation denominators to be nonzero.


---

#### 2a. Definitions

All indices are 0-based throughout (matching Lean and the Isabelle
formalization).

**Gram-Schmidt orthogonalization.** Given a basis b_0, ..., b_{n-1}
of a lattice L in Z^m, define orthogonal vectors gso_0, ..., gso_{n-1}
and coefficients μ_{i,j} by:

    gso_0 = b_0
    μ_{i,j} = <b_i, gso_j> / <gso_j, gso_j>     for j < i
    gso_i = b_i - sum_{j=0}^{i-1} μ_{i,j} * gso_j

Key property: gso_i is the projection of b_i onto the orthogonal
complement of span(b_0, ..., b_{i-1}). Size reduction does not
change the gso vectors (only column operations b_k <- b_k + c*b_j
with j < k are performed, which leave the Gram-Schmidt vectors
invariant).

**Gram determinants (d-values).** Define d_0 = 1 and for k >= 1:

    d_k = det(G_k)

where G_k is the k x k Gram matrix of b_0, ..., b_{k-1},
i.e., (G_k)_{i,j} = <b_i, b_j> for 0 <= i, j < k. For integer
lattices, d_k is always a positive integer (determinant of a
positive-definite integer Gram matrix).

**Theorem (GS norms = ratio of consecutive Gram determinants).**
By induction on the Gram-Schmidt recurrence:

    d_k = prod_{j=0}^{k-1} ||gso_j||^2

*Proof sketch.* The Gram matrix G_k factors as L D L^T where L is
lower-unitriangular with L_{i,j} = μ_{i,j} and D = diag(||gso_j||^2).
So det(G_k) = prod ||gso_j||^2.

This gives the crucial identity:

    ||gso_k||^2 = d_{k+1} / d_k

**Scaled GS coefficients (ν-values).** Define:

    ν_{i,j} = d_{j+1} * μ_{i,j}     for j < i

These are always integers (see Section 2d for the proof). The
algorithm works entirely with ν and d, never computing μ directly.

**delta-LLL-reduced.** A basis b_0, ..., b_{n-1} is delta-LLL-reduced
(for delta in (1/4, 1]) if it satisfies two conditions:

1. **Size-reduced:** |μ_{i,j}| <= 1/2 for all 0 <= j < i < n.

2. **Lovász condition:** For all 0 <= i < n-1:
       delta * ||gso_i||^2 <= ||gso_{i+1}||^2 + μ_{i+1,i}^2 * ||gso_i||^2

   Equivalently: (delta - μ_{i+1,i}^2) * ||gso_i||^2 <= ||gso_{i+1}||^2

---

#### 2b. The LLL algorithm and its loop invariant

**Algorithm.** The algorithm operates on a single integer state:
basis vectors, Gram determinants, and scaled GS coefficients. The
rational GS quantities (μ, gso norms) are never stored or computed
at runtime — they exist only as `noncomputable` projections for
use in proofs.

```lean
/-- Round to nearest integer (ties round up). -/
def Rat.round (q : Rat) : Int := (q + 1/2).floor
-- Key property: |q - q.round| ≤ 1/2 (from floor_le and lt_floor_add_one)
-- In the ν-representation, round(ν / d) is computed as pure integer
-- arithmetic: Int.fdiv (2 * ν + d) (2 * d), since d > 0.

/-- LLL state. All fields are integers; no rationals stored. -/
structure LLLState (n m : Nat) where
  b : Matrix Int n m            -- basis vectors
  ν : Matrix Int n n            -- ν[i][j] = d[j+1] * μ_{i,j} for j < i
  d : Vector Nat (n + 1)        -- Gram determinants d_0, ..., d_n
  ν_eq : ∀ i j, j < i → ν[i][j] = d[j + 1] * gramSchmidtMu b i j
  d_eq : ∀ i, d[i] = gramDet b i

/-- Recover rational GS coefficients from integer state.
    Marked noncomputable: exists only for the proof layer. -/
noncomputable def LLLState.μ (s : LLLState n m) (i j : Nat) : Rat :=
  s.ν[i][j] / s.d[j + 1]

def LLLState.potential (s : LLLState n m) : Nat :=
  s.d[1:n].foldl (· * ·) 1    -- d_1 * d_2 * ... * d_{n-1}
```

**Size reduction.** Size-reduce b[k] against b[k-1], ..., b[0].
Updates b and ν; d is unchanged (GS vectors are unchanged by size
reduction).

```lean
def LLLState.sizeReduce (s : LLLState n m) (k : Nat) : LLLState n m := sorry
```

For j = k-1 downto 0: if |ν[k][j]| > d[j+1] / 2 (i.e., |μ_{k,j}| > 1/2):

    r := Int.fdiv (2 * ν[k][j] + d[j+1]) (2 * d[j+1])
    b[k] := b[k] - r * b[j]
    ν[k][l] := ν[k][l] - r * ν[j][l]    for l < j
    ν[k][j] := ν[k][j] - r * d[j+1]

The rounding formula `Int.fdiv (2 * ν + d) (2 * d)` computes
`round(ν / d)` = `round(μ)` as pure integer arithmetic, since d > 0.

**Swap step.** Swap b[k] and b[k-1], updating ν and d.

```lean
def LLLState.swapStep (s : LLLState n m) (k : Nat) : LLLState n m := sorry
```

Let B = ν[k][k-1]. After swapping b[k] and b[k-1]:

*d update:*

    d[k]^{new} = (d[k+1] * d[k-1] + B^2) / d[k]

This division is exact (see Section 2d). All other d[i] are unchanged.

*ν updates* (Cohen Algorithm 2.6.3, 0-indexed):

For j < k-1: ν[k-1][j] and ν[k][j] simply swap.

For i > k, the two affected columns update simultaneously:

    ν[i][k-1]^{new} = (ν[i][k-1] * d[k]^{new} + ν[i][k] * B) / d[k]
    ν[i][k]^{new}   = (ν[i][k] * d[k-1] - ν[i][k-1] * B) / d[k]

(Verify precise formulas against Cohen Algorithm 2.6.3 or von zur
Gathen & Gerhard Algorithm 16.10 during implementation.) All
divisions are exact (see Section 2d). Only d[k] changes among
d-values, and only ν values with one index equal to k or k-1 change.

**Main loop.** The Lovász condition in integer form (see Section 2d
for derivation) is:

    d[k+1] * d[k-1] + ν[k][k-1]^2 >= δ * d[k]^2

For δ = p/q rational, this becomes a comparison of integers (no
division): `q * (d[k+1] * d[k-1] + ν[k][k-1]^2) >= p * d[k]^2`.

```lean
def lllAux (s : LLLState n m) (k : Nat) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hind : s.b.independent)
    (hk : 1 ≤ k) (hkn : k ≤ n) : Matrix Int n m :=
  if h : k = n then s.b
  else
    let s := s.sizeReduce k
    -- Check Lovász condition (integer arithmetic, no division):
    if δ.den * (s.d[k+1] * s.d[k-1] + s.ν[k][k-1]^2) ≥ δ.num * s.d[k]^2 then
      -- Lovász holds: advance
      lllAux s (k + 1) δ hδ hδ' ‹_› (by omega) (by omega)
    else
      -- Lovász fails: swap and decrement
      let s := s.swapStep k
      lllAux s (max (k - 1) 1) δ hδ hδ' ‹_› (by omega) (by omega)
termination_by (s.potential, n - k)
-- Termination uses only ν_eq, d_eq, and correctness of sizeReduce/swapStep.
-- Advance: sizeReduce preserves d (GS vectors unchanged), so potential
--   unchanged; n - k decreases.
-- Swap: the failing Lovász condition (read from d and ν via d_eq/ν_eq)
--   gives d[k]^new < δ * d[k] < d[k]; potential strictly decreases.

def lll (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hind : b.independent) : Matrix Int n m :=
  lllAux ⟨b, initNu b, gramDetVec b, sorry, sorry⟩ 1 δ hδ hδ' hind (by omega) (by omega)
```

The swap bound `potential_initial ≤ (maxNormSq b)^{n*(n-1)/2}` follows
from `d_k ≤ (maxNormSq b)^k` (each row of the Gram matrix has entries
≤ maxNormSq b, so the determinant is bounded by the product of row norms).

**Loop invariant.** At the top of the loop with current index k,
expressed in terms of the noncomputable projections `s.μ` and the
GS vectors (which are mathematical functions of `s.b`, not stored):

(I1) b_0, ..., b_{n-1} is a basis of the same lattice L as the input.
(I2) gso_0, ..., gso_{n-1} and μ_{i,j} are the correct Gram-Schmidt
     orthogonalization of the current basis. (This is captured by
     `s.ν_eq` and `s.d_eq`, which assert that the stored integer
     values track the mathematical GS quantities.)
(I3) **Size-reduced below k:** |s.μ i j| <= 1/2 for all j < i < k.
(I4) **Lovász condition below k:** for all 0 <= i < k-1,
     (delta - (s.μ (i+1) i)^2) * ||gso_i||^2 <= ||gso_{i+1}||^2.
(I5) 1 <= k <= n.

Together, (I3) and (I4) say: the first k vectors form a
delta-LLL-reduced basis of the sublattice they span.

**Size-reduction sub-invariant.** The inner loop
`for j in [k-1, k-2, ..., 0]` has its own invariant, parameterized
by the current column j.
After processing column j (and before processing j-1), the following
hold in addition to (I1)-(I5):

(SR1) |s.μ k l| <= 1/2 for all l with j <= l < k.
(SR2) s.μ k l is unchanged for l < j.
(SR3) All gso_i vectors are unchanged (size reduction preserves GS).
(SR4) The lattice is unchanged (integer column operations).

At entry (j = k-1), (SR1) is vacuous. At exit (j < 0), (SR1) gives
|s.μ k l| <= 1/2 for all l < k, establishing (I3) for the new k.

**Preservation of the outer invariant:**

- *Size reduction (full inner loop):* Preserves the lattice (I1) and
  all gso_i (I2) — these follow from (SR3)+(SR4). Establishes
  |s.μ k j| <= 1/2 for all j < k — this follows from (SR1) at
  exit. The Lovász conditions for indices < k-1 are unaffected (I4),
  since only μ values in row k change and the gso_i are unchanged.

- *Advance (k <- k+1):* Only happens when the Lovász condition holds
  at index k-1. Combined with the already-established conditions
  below k-1, we now have all conditions below k, so (I3)+(I4) hold
  for the new k.

- *Swap (b_k <-> b_{k-1}, k <- max(k-1, 1)):* Preserves the lattice
  (I1). Changes only gso_{k-1} and gso_k among the GS vectors (I2).
  The Lovász conditions for indices < k-2 are unaffected (I4). We
  lose the size-reduction guarantee at the new k (the swapped vector
  may not be size-reduced), so (I3) is only claimed for indices
  below the new k. We may need to re-check at the new k, hence
  decrementing k.

---

#### 2c. The short vector bound proof

The proof has three steps.

**Step 1: Consecutive GS norm bound.** From the Lovász condition
with the size-reduction guarantee |μ_{i+1,i}| <= 1/2:

    (delta - μ_{i+1,i}^2) * ||gso_i||^2 <= ||gso_{i+1}||^2
    (delta - 1/4) * ||gso_i||^2 <= ||gso_{i+1}||^2

Set alpha = 1 / (delta - 1/4). Then:

    ||gso_i||^2 <= alpha * ||gso_{i+1}||^2

By telescoping (induction on the gap):

    ||gso_0||^2 <= alpha^i * ||gso_i||^2     for all 0 <= i < n

More usefully:

    ||gso_0||^2 <= alpha^{n-1} * min_{0 <= i < n} ||gso_i||^2

**Step 2: Lower bound lemma.** For any nonzero lattice vector
v in L, we have:

    ||v||^2 >= min_{0 <= i < n} ||gso_i||^2

*Proof.* Write v = sum_{i=0}^{n-1} a_i * b_i with a_i in Z (not all
zero). Let k be the largest index with a_k != 0. Expand in the
GS basis:

    v = sum_{i=0}^{k} a_i * b_i
      = sum_{i=0}^{k} a_i * (gso_i + sum_{j<i} μ_{i,j} * gso_j)
      = sum_{i=0}^{k} c_i * gso_i

for some real coefficients c_i, where crucially c_k = a_k (because
b_k = gso_k + sum_{j<k} μ_{k,j} * gso_j, and no later b_i contributes
to the gso_k component). Since a_k is a nonzero integer, |c_k| >= 1.

By orthogonality of the gso_i:

    ||v||^2 = sum_{i=0}^{k} c_i^2 * ||gso_i||^2
            >= c_k^2 * ||gso_k||^2
            >= ||gso_k||^2
            >= min_{0 <= i < n} ||gso_i||^2     QED

**Step 3: Combining.** For any nonzero v in L:

    ||b_0||^2 = ||gso_0||^2              (b_0 = gso_0 by definition)
              <= alpha^{n-1} * min_i ||gso_i||^2    (Step 1)
              <= alpha^{n-1} * ||v||^2             (Step 2)

This gives the main theorem:

    ||b_0||^2 <= alpha^{n-1} * ||v||^2

for any nonzero lattice vector v, where alpha = 1/(delta - 1/4).

For the standard choice delta = 3/4, alpha = 2, and we get
||b_0|| <= 2^{(n-1)/2} * lambda_1(L).

---

#### 2d. Integrality and correctness of the integer representation

This section provides the proofs that the integer update formulas
used in Section 2b are correct and that all divisions are exact.

**Integrality of ν_{i,j}.** (Von zur Gathen & Gerhard, Lemma 16.7.)
ν_{i,j} = d_{j+1} * μ_{i,j} can be expressed as a (j+1) × (j+1)
determinant of a matrix of inner products:

    ν_{i,j} = det | <b_0,b_0>  ...  <b_0,b_j>   <b_0,b_i> |
                  | <b_1,b_0>  ...  <b_1,b_j>   <b_1,b_i> |
                  |   ...      ...    ...          ...     |
                  | <b_j,b_0>  ...  <b_j,b_j>   <b_j,b_i> |

Since the b_l are integer vectors, all inner products are integers,
so this determinant is an integer. (The formula follows from expanding
the Gram-Schmidt recurrence and using the cofactor expansion of d_{j+1}
along the last column.) This is the fundamental integrality lemma of
the d-representation.

Alternatively: by Cramer's rule on the system G_j * x = g (where
g is the column of inner products with b_i), μ_{i,j} has the form
(integer determinant) / d_j. Therefore d_j * μ_{i,j} is an integer.
Since d_{j+1} = d_j * ||gso_j||^2 and ||gso_j||^2 = d_{j+1}/d_j, we
need d_{j+1} * μ_{i,j} = (d_{j+1}/d_j) * (integer) to be an integer.
This requires showing d_j | d_{j+1} * (the Cramer numerator), which
follows from the determinant formula above.

**Derivation of the integer Lovász condition.** The rational Lovász
condition rearranged (following Cohen, section 2.6.3):

    ||gso_k||^2 + μ_{k,k-1}^2 * ||gso_{k-1}||^2 >= delta * ||gso_{k-1}||^2

Substitute ||gso_i||^2 = d_{i+1}/d_i and μ_{k,k-1} = ν_{k,k-1}/d_k:

    d_{k+1}/d_k + (ν_{k,k-1}/d_k)^2 * (d_k/d_{k-1}) >= delta * (d_k/d_{k-1})

Multiply through by d_k * d_{k-1} (both positive):

    d_{k+1} * d_{k-1} + ν_{k,k-1}^2 >= delta * d_k^2

So the Lovász condition in integer form is:

    d_{k+1} * d_{k-1} + ν_{k,k-1}^2 >= delta * d_k^2

(Negated for the swap trigger: swap when this fails.)

**Correctness of size-reduction updates.** The rational size-reduction
step sets μ_{k,j} <- μ_{k,j} - r (and μ_{k,l} <- μ_{k,l} - r * μ_{j,l}
for l < j). Multiplying through by d_{j+1} (resp. d_{l+1}) gives
the ν update formulas:

    ν_{k,l} <- ν_{k,l} - r * ν_{j,l}    for l < j
    ν_{k,j} <- ν_{k,j} - r * d_{j+1}

The d values are unchanged because size reduction preserves GS vectors.
The rounding value r = round(μ_{k,j}) = round(ν_{k,j} / d_{j+1}) is
computed as `Int.fdiv (2 * ν_{k,j} + d_{j+1}) (2 * d_{j+1})`, which
is pure integer arithmetic since d_{j+1} > 0.

**Correctness of swap updates.** When swapping b_k and b_{k-1},
let B = ν_{k,k-1}. The d update:

    d_k^{new} = (d_{k+1} * d_{k-1} + B^2) / d_k

follows from the determinant identity for the Gram matrix after the
swap. The ν updates for i > k:

    ν_{i,k-1}^{new} = (ν_{i,k-1} * d_k^{new} + ν_{i,k} * B) / d_k
    ν_{i,k}^{new}   = (ν_{i,k} * d_{k-1} - ν_{i,k-1} * B) / d_k

follow from substituting the definitions ν = d * μ into the rational
μ update formulas and simplifying. For j < k-1, ν_{k-1,j} and ν_{k,j}
simply swap.

**Why all divisions are exact.** ν_{i,j} = d_{j+1} * μ_{i,j} and
the μ values are always expressible as ratios of integer determinants
with denominator d_{j+1}. After a swap, the new μ values have the
same property with the new d values. The algebraic identities can
also be verified directly by substituting the definitions and using
the fact that Gram determinants of sub-lattices are always integers.

---

#### 2e. Termination

**Potential function.** Define:

    D = prod_{i=1}^{n-1} d_i

This is the product of the first n-1 Gram determinants. Equivalently:

    D = prod_{k=0}^{n-2} ||gso_k||^{2(n-1-k)}

(since d_i = prod_{j=0}^{i-1} ||gso_j||^2, each ||gso_k||^2 appears in
d_i for i = k+1, k+2, ..., n-1, contributing exponent n-1-k to the
product). Since each d_i is a positive integer for integer lattices,
D is a positive integer, so D >= 1.

**Size reduction preserves D.** The GS vectors gso_i are unchanged
by size reduction, so all d_i (and hence D) are unchanged.

**Each swap decreases D.** When b_k and b_{k-1} are swapped with
the Lovász condition failing:

    d_k^{new} = (d_{k+1} * d_{k-1} + ν_{k,k-1}^2) / d_k

The Lovász condition fails, meaning:

    d_{k+1} * d_{k-1} + ν_{k,k-1}^2 < delta * d_k^2

So d_k^{new} < delta * d_k. Since only d_k changes among the d_i
values, and d_k appears exactly once in the product D:

    D^{new} = D * (d_k^{new} / d_k) < D * delta

Since delta < 1, D strictly decreases. Since D >= 1 is a positive
integer (for integer lattices), the number of swaps is bounded by:

    #swaps <= log_{1/delta}(D_initial)

More precisely, using D_initial <= (max_i ||b_i||^2)^{n(n-1)/2}
(since d_i <= (max ||b_j||^2)^i and the product has n-1 terms):

    #swaps <= n(n-1)/2 * log(max_i ||b_i||^2) / log(1/delta)

This is polynomial in n and the bit-size of the input.

**Lean formalization strategy for termination:** Use well-founded
recursion on the pair (D, n - k), lexicographically ordered. Each
iteration either decreases D (swap) or increases k (advance), and
k is bounded by n.

---

#### 2f. Formalization strategy: single-state architecture

**Approach.** Unlike the Isabelle AFP formalization (Bottesch et al.,
ITP 2018, JAR 2020), which uses a two-layer bisimulation between a
rational specification and an integer implementation, we use a
single-state design. The `LLLState` stores only integers (b, ν, d).
The rational GS quantities are recovered via `noncomputable`
projections (`LLLState.μ`, and similarly for `||gso_k||^2 =
d_{k+1} / d_k`), which exist only for the proof layer.

The key advantage: no bisimulation proof is needed. There is one
state, one algorithm, and the correctness proofs unfold the
`noncomputable` definitions to connect integer update formulas
to their rational counterparts (Section 2d). The `noncomputable`
marker makes it syntactically impossible for the rational quantities
to leak into the executable code.

**Proof structure.** For each step (size-reduce, swap, advance):
1. Show the integer update formulas preserve `ν_eq` and `d_eq`
   (i.e., the stored integers still track the GS quantities of
   the new basis). This uses the derivations in Section 2d.
2. Show the loop invariant (I1)–(I5) is preserved. This uses the
   `noncomputable` projections to state conditions in their natural
   rational form.
3. The short vector bound (Section 2c) is proved purely in terms of
   mathematical GS properties. Termination (Section 2e) uses the
   integer state directly (the potential is a product of d-values,
   and the swap decrease follows from the integer Lovász failure).

**Gram-Schmidt API.** The GS machinery lives inside `lean-lll` (not a
separate library), organized as:

- `GramSchmidt.lean` — definitions of `gso`, `μ`, orthogonality,
  span preservation, the projection formula, and the norm-minimality
  lemma (Step 2 of the short vector bound)
- `GramSchmidtUpdate.lean` — how `gso` and `μ` change under size
  reduction (unchanged) and swap (explicit update formulas)
- `GramSchmidtInt.lean` — `gramDet`, `ν`, integrality of `ν`,
  exact division under swap

Mathlib's `gramSchmidt` works over inner product spaces and does not
track `μ` coefficients or update formulas, so it cannot be used in the
computational core. The `lean-lll-mathlib` bridge would later prove
that our `gso` corresponds to Mathlib's `gramSchmidt`.

**Highest-risk proof areas:**

- **Swap update formulas.** The explicit formulas for how `gso`, `μ`,
  `d`, and `ν` change under a swap (Sections 2b, 2d) are the most
  error-prone part. Each formula must be verified algebraically and
  the exact division proofs must be discharged.
- **Exact division under swap.** Proving that
  `(d_{k+1} * d_{k-1} + ν_{k,k-1}^2) / d_k` and the ν update
  divisions are exact requires the determinant-based integrality
  arguments from Section 2d.

**Prior art.** The Isabelle AFP formalization (~14,800 lines across
14 modules) uses a two-layer bisimulation: `LLL.thy` defines a
rational specification with loop invariant proofs, and `LLL_Impl.thy`
defines the d-representation implementation with a step-refinement
proof connecting the two. Their `upw` ("update needed") boolean in
the outer invariant avoids exposing the size-reduction inner-loop
index. We chose not to follow this architecture, instead using a
single integer state with `noncomputable` projections.

**References:**
- Lenstra, Lenstra, Lovász, "Factoring polynomials with rational
  coefficients," *Math. Ann.* 261, 1982, pp. 515-534 (original paper)
- Von zur Gathen & Gerhard, *Modern Computer Algebra*, 3rd ed., 2013,
  ch. 16 (primary reference for formalization)
- Cohen, *A Course in Computational Algebraic Number Theory*, 1993,
  section 2.6 (integral LLL algorithm)
- Galbraith, *Mathematics of Public Key Cryptography*, 2012, ch. 17
  (good exposition; free PDF at math.auckland.ac.nz/~sgal018/crypto-book/)
- Bottesch et al., "A Formalization of the LLL Basis Reduction
  Algorithm," ITP 2018 (Isabelle formalization, conference version)
- Bottesch et al., "Formalizing the LLL Basis Reduction Algorithm and
  the LLL Factorization Algorithm in Isabelle/HOL," *J. Automated
  Reasoning* 64, 2020, pp. 1-42 (Isabelle formalization, journal version)
- Nguyen & Stehlé, "Floating-Point LLL Revisited," EUROCRYPT 2005
  (L^2 algorithm; not needed for our formalization but relevant context)

---

---

### 4. Rabin's irreducibility test (`rabin_irreducible`)

```lean
theorem rabin_irreducible (f : FpPoly p) (hf : f.degree = n) :
    rabinTest f = true ↔ Irreducible f
```

Unlike Berlekamp's completeness proof (which avoids finite field
theory entirely), both directions of Rabin's theorem require the
theory of finite field extensions.

**(→) test passes ⟹ irreducible.** Contrapositive: if `f` is
reducible, `f = g * h` with `g` irreducible of degree `d < n`.
Then `d | n` (subfield containment), so `d ≤ n/q` for some prime
`q | n`, giving `g | X^(p^(n/q)) - X` and thus
`gcd(f, X^(p^(n/q)) - X) ≠ 1`.

**(←) irreducible ⟹ test passes.** Two parts:
- `f | X^(p^n) - X`: in `F_p[x]/(f)` (a field with `p^n` elements),
  every element satisfies `a^(p^n) = a` by Lagrange's theorem on the
  multiplicative group. So `f | X^(p^n) - X`.
- `gcd(f, X^(p^(n/q)) - X) = 1`: if nontrivial, `f` would share a
  root with `X^(p^(n/q)) - X`, placing it in `GF(p^(n/q))`. But
  the minimal polynomial of a root of `f` has degree `n`, and
  `n/q < n` — contradiction.

**Finite field theory needed** (not needed for Berlekamp):
1. Irreducible `f` of degree `n` ⟹ `F_p[x]/(f)` is a field
   (quotient by irreducible is integral domain, finite integral
   domain is a field)
2. `|F_p[x]/(f)| = p^n` (counting polynomials of degree `< n`)
3. `a^(p^n) = a` for all `a ∈ GF(p^n)` (Lagrange on the
   multiplicative group of order `p^n - 1`)
4. `GF(p^m) ⊆ GF(p^n)` iff `m | n`
5. If `g` is irreducible of degree `d` and `g | X^(p^n) - X`,
   then `d | n`

**Where this lives.** Rabin's test is implemented in `lean-berlekamp`
(computational black box). Both directions of the correctness proof
live in `lean-berlekamp-mathlib`, where Mathlib provides all the
finite field theory (steps 1-5 above).

---

### 5. Hensel uniqueness (`hensel_unique`)

```lean
theorem hensel_unique (f g h g' h' : ZPoly) (p k : Nat) :
    g.leadingCoeff = 1 →
    g * h ≡ f [MOD p^k] → g' * h' ≡ f [MOD p^k] →
    g ≡ g' [MOD p] → h ≡ h' [MOD p] →
    coprime_mod g h p →
    g = g' ∧ h = h'
```

**Why it's hard:** Induction on k. The base case (k=1) is immediate.
The inductive step requires showing that the coprimality condition
lifts: if g, h are coprime mod p and g*h ≡ f mod p^k, then the
Bezout coefficients can be adjusted to work mod p^(k+1). The
leading coefficient condition (g monic) pins down the factorization
uniquely — without it, you can redistribute units between g and h.

The plan labels this "the deep theorem." It's the key ingredient for
connecting linear and quadratic Hensel lifting (they produce the same
result, so quadratic is a valid optimization).

**Research needed:**
- Exact statement of the coprimality lifting lemma
- Whether the induction is on k or on the precision doubling steps
- The Isabelle proof structure for this

---

### 6. Mignotte bound validity

```lean
-- In lean-poly-z-mathlib
theorem mignotte_bound (f g : Polynomial ℤ) (hg : g ∣ f) (j : ℕ) :
    |(g.coeff j : ℤ)| ≤ Nat.choose g.natDegree j * ‖f‖₂
```

Mathlib has all the heavy analysis.
The Mahler measure library (`Mathlib.Analysis.Polynomial.MahlerMeasure`,
by Fabrizio Barroero, merged Sep–Nov 2025) provides:

- `mahlerMeasure_mul`: `M(p * q) = M(p) * M(q)`
- `norm_coeff_le_choose_mul_mahlerMeasure`: `‖p.coeff n‖ ≤ C(deg, n) * M(p)`
- `one_le_prod_max_one_norm_roots`: `∏ max(1, ‖αᵢ‖) ≥ 1`
- `mahlerMeasure_le_sum_norm_coeff`: `M(p) ≤ ‖p‖₁`
- `mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm`: goes through
  `M(p) ≤ ‖p‖₂` as an intermediate step (via Parseval)

The proof is short glue: map to `ℂ[X]`, use multiplicativity to get
`M(g) ≤ M(f)` (since `M(h) ≥ 1` for integer polynomials), apply the
coefficient bound, then bound `M(f)` by `‖f‖₂`.

**Upstreaming to Mathlib:**
https://github.com/leanprover-community/mathlib4/pull/37349 adds
Landau's inequality (`mahlerMeasure_le_sqrt_sum_sq_norm_coeff`),
the monotonicity lemma (`le_mahlerMeasure_mul_right`), and the
Mignotte bound (`norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure`)
to `Mathlib.Analysis.Polynomial.MahlerMeasure`. Once merged, the
lean-poly-z-mathlib proof reduces to mapping `ℤ[X] → ℂ[X]` and
applying these results.

**Other open Mathlib PR:** https://github.com/leanprover-community/mathlib4/pull/33463
(Mahler Measure for other rings) would simplify the `ℤ → ℂ` coercion
further.

---

## Tier 2: Substantial but More Tractable

### 7. Bareiss = det (`bareiss_eq_det`)

```lean
theorem bareiss_eq_det (M : Matrix Int n n) : bareiss M = det M
```

**Why it's hard:** Must track the determinant through fraction-free
Gaussian elimination. Each Bareiss step performs the recurrence
a_{ij}^{(k)} = (a_{kk} · a_{ij} − a_{ik} · a_{kj}) / a_{k−1,k−1}
where the division is exact. The proof shows this equals applying row
operations (which have known determinant effects) and then dividing
by the previous pivot — the key being that the division is always
exact (Sylvester's identity or direct induction).

**Research needed:**
- Whether to use the row-operation approach or the Sylvester identity
  approach (the plan mentions both)
- Sylvester's identity is listed as "further work" — is it needed for
  the primary proof?

---

### 8. Nullspace completeness

```lean
theorem nullspace_complete (E : IsEchelonForm M D) (v : Vector R m) :
    M * v = 0 → E.nullspace.toMatrix.spanContains v
```

**Why it's hard:** Must show the computed basis vectors (one per free
variable) span the entire kernel. The standard argument: any kernel
vector, when restricted to pivot columns, is determined by its free-
variable entries (back-substitution from RREF), so it's a linear
combination of the basis vectors. Formalizing the back-substitution
argument requires careful index manipulation.

---

### 9. Montgomery correctness (`toNat_mulMont`)

```lean
theorem MontCtx.toNat_mulMont (ctx : MontCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (ctx.fromMont (ctx.mulMont (ctx.toMont a) (ctx.toMont b))).toNat =
      (a.toNat * b.toNat) % p.toNat
```

**Why it's hard:** Montgomery reduction computes (T + (T · p' mod R) · p) / R
where R = 2^64. The proof requires: (1) the result is congruent to
T · R⁻¹ mod p, (2) it's in range [0, 2p), (3) a conditional
subtraction brings it into [0, p). All of this at the UInt64 / 2^64
level, where overflow semantics must be handled precisely. Lean's
`UInt64` arithmetic wraps mod 2^64, so every intermediate step needs
careful bounds tracking.

The Montgomery inverse p' satisfying p' · p ≡ −1 (mod 2^64) must
also be computed and verified (via Newton's method on UInt64, or
extended GCD).

**Research needed:**
- Lean 4's current `UInt64` lemma library — what's available for
  overflow reasoning?
- Whether to prove at the `Nat` level and cast down, or work directly
  with `UInt64`

---

### 10. Factor uniqueness up to associates (`factor_unique`)

```lean
theorem factor_unique (f : ZPoly) (gs hs : List ZPoly) :
    gs.prod = f → hs.prod = f →
    (∀ g ∈ gs, Irreducible g) → (∀ h ∈ hs, Irreducible h) →
    gs ~ hs  -- multiset equality up to associates
```

**Why it's hard:** This is unique factorization in Z[x]. Requires
Gauss's lemma (product of primitive polynomials is primitive) plus
unique factorization in F_p[x] (which follows from F_p[x] being a
Euclidean domain). The full proof chains: Z[x] is a UFD because Z
is a UFD and the polynomial ring over a UFD is a UFD (via Gauss).

**Research needed:**
- Whether to prove UFD for Z[x] directly or factor through a more
  general result
- The Isabelle approach to this

---

## Tier 3: Hard but Well-Understood Patterns

### 11. Barrett reduction correctness

```lean
theorem BarrettCtx.toNat_mulMod (ctx : BarrettCtx p) (a b : UInt64)
    (ha : a < p) (hb : b < p) :
    (ctx.mulMod a b).toNat = (a.toNat * b.toNat) % p.toNat
```

Similar to Montgomery but simpler: compute q ≈ (a*b) / p using the
precomputed reciprocal, then r = a*b − q*p, with at most one
corrective subtraction. Still requires 128-bit intermediate reasoning.

---

### 12. Gauss's lemma

```lean
theorem content_mul (f g : ZPoly) :
    content (f * g) = content f * content g
```

Classical proof: assume f, g primitive, show f*g primitive by
contradiction — if prime p divides all coefficients of f*g, reduce
mod p and use the fact that F_p[x] has no zero divisors.

---

### 13. Ring equivalences (Mathlib bridges)

```lean
def equiv : DensePoly R ≃+* Polynomial R          -- lean-poly-mathlib
def equiv : GFq p n ≃+* GaloisField p n           -- lean-gfq-mathlib
def equiv : ZMod64 p ≃+* ZMod p                   -- lean-mod-arith-mathlib
```

These are "glue" theorems — define the map (coefficient-by-coefficient),
show it's bijective, show it preserves + and *. Tedious but mechanical.
Difficulty depends on how cooperative Mathlib's API is.

---

## Summary Table

| # | Theorem | Library | Blocking? |
|---|---------|---------|-----------|
| 1 | `prod_berlekampFactor` / `irreducible_of_mem_berlekampFactor` | lean-berlekamp | Yes (factoring) |
| 2 | `lll_short_vector` | lean-lll | Yes (poly-time BZ) |
| 3 | `lll_swap_bound` | lean-lll | Yes (termination) |
| 4 | `rabin_irreducible` | lean-berlekamp | No (Berlekamp suffices) |
| 5 | `hensel_unique` | lean-hensel | Yes (quadratic lift) |
| 6 | Mignotte bound | lean-poly-z-mathlib | Yes (unconditional BZ) |
| 7 | `bareiss_eq_det` | lean-matrix | No (det not needed for BZ) |
| 8 | Nullspace completeness | lean-matrix | Yes (Berlekamp kernel) |
| 9 | Montgomery correctness | lean-arith | Yes (performance) |
| 10 | `factor_unique` | lean-bz-mathlib | No (correctness suffices) |
| 11 | Barrett correctness | lean-arith | Yes (performance) |
| 12 | Gauss's lemma | lean-poly-z | Yes (content machinery) |
| 13 | Ring equivalences | various -mathlib | No (bridges) |
