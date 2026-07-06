import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulModTo
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.InterpMulX
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.GroupedEqX
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.GroupedEqXV
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.GroupedEqXVCost
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.WindowCaps

/-!
# RSA fused square-multiply-mod equality (gadget "SqMulModTo")

`SqMulModTo` is `MulModTo` with the multiplicand `a` squared: given `a`, `b`, the
`modulus` `n`, and an *affine* target `em`, it asserts

    a² · b = q · n + em          (as natural numbers)

with a witnessed quotient `q` over `2m` limbs (tight-normalized: top limb
`< 2^tq`). Under the assumption `em < n` this pins `em = (a²·b) mod n`.

The `a²·b` side is built from a chain of two interpolation multiplications:
first `z1 = interpolatedMul a a` (the `2m-1` coefficients of `a²`), then
`z2 = interpolatedMulX z1 b` (the `(2m-1)+m-1` coefficients of `a²·b`). The
`q·n` side is `z3 = interpolatedMulX q n` (the `2m+m-1` coefficients of `q·n`,
`q` having `2m` limbs). Both sides are padded to the common length
`L = 2m+m-1` and compared via the parametric grouped equality `GroupedEqX`
(with `em`'s limbs added on the affine right-hand side, exactly where
`MulModTo` adds them to `EqViaCarries`'s right-hand side).
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537

instance nezero_3m1 {m : ℕ} [NeZero m] : NeZero (2 * m + m - 1) :=
  ⟨by have := Nat.pos_of_neZero m; omega⟩

open Specs.RSA

/-! ## Mixed-length Cauchy product over `ℕ`, at base `2^B`

Pure combinatorial generalization of `Theorems.lean`'s `cauchy_inner_reindex` /
`cauchy_base_pow` (there specialized to two equal-length-`m` operands) to two
operands of lengths `n₁`, `n₂`. This is the `ℕ`/`polyValue` counterpart of
`InterpMulX.lean`'s `cauchy_diag_mixed` (there stated at the level of a general
`CommRing`, used for the field-level interpolation soundness). -/

/-- Per-`i` reindex for the mixed Cauchy product: summing the guarded `k`-term
over `range (n₁+n₂-1)` collapses (via `j = k - i`) to a clean sum over
`range n₂`. Mirrors `cauchy_inner_reindex`. -/
lemma cauchy_inner_reindex_mixed (B n₁ n₂ : ℕ) (f g : ℕ → ℕ) (i : ℕ) (hi : i < n₁) :
    (∑ k ∈ Finset.range (n₁ + n₂ - 1),
        if i ≤ k ∧ k - i < n₂ then f i * g (k - i) * 2 ^ (B * k) else 0)
      = ∑ j ∈ Finset.range n₂, f i * g j * 2 ^ (B * (i + j)) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (i := fun k => k - i) (j := fun j => i + j)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    omega
  · intro j hj
    simp only [Finset.mem_range, Finset.mem_filter] at hj ⊢
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    rw [show i + (k - i) = k by omega]

/-- Base-`2^B` Cauchy product over `ℕ`, mixed length: the product of two
base-`2^B` polynomials of degrees `< n₁`, `< n₂` equals the base-`2^B` value of
their `n₁+n₂-1` schoolbook convolution coefficients. Mirrors `cauchy_base_pow`. -/
lemma cauchy_base_pow_mixed (B n₁ n₂ : ℕ) (f g : ℕ → ℕ) :
    (∑ i ∈ Finset.range n₁, f i * 2 ^ (B * i))
        * (∑ j ∈ Finset.range n₂, g j * 2 ^ (B * j))
      = ∑ k ∈ Finset.range (n₁ + n₂ - 1),
          (∑ i ∈ Finset.range n₁, if i ≤ k ∧ k - i < n₂ then f i * g (k - i) else 0)
            * 2 ^ (B * k) := by
  rw [Finset.sum_mul_sum]
  have hrhs : (∑ k ∈ Finset.range (n₁ + n₂ - 1),
        (∑ i ∈ Finset.range n₁, if i ≤ k ∧ k - i < n₂ then f i * g (k - i) else 0)
          * 2 ^ (B * k))
      = ∑ i ∈ Finset.range n₁, ∑ j ∈ Finset.range n₂, f i * g j * 2 ^ (B * (i + j)) := by
    have hstep : (∑ k ∈ Finset.range (n₁ + n₂ - 1),
          (∑ i ∈ Finset.range n₁, if i ≤ k ∧ k - i < n₂ then f i * g (k - i) else 0)
            * 2 ^ (B * k))
        = ∑ k ∈ Finset.range (n₁ + n₂ - 1), ∑ i ∈ Finset.range n₁,
            if i ≤ k ∧ k - i < n₂ then f i * g (k - i) * 2 ^ (B * k) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [ite_mul, zero_mul]
    rw [hstep, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [cauchy_inner_reindex_mixed B n₁ n₂ f g i hi]
  rw [hrhs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show B * (i + j) = B * i + B * j by ring, pow_add]
  ring

section
variable {p : ℕ} [Fact p.Prime]

namespace MulMod

section
variable {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]

/-! ## `interpolatedMulX` bridge lemmas

Generic soundness/completeness support for `interpolatedMulX`, mirroring
`InterpMul.lean`'s API for `interpolatedMul` (`interpolatedMul_soundness`,
`interpolatedMul_eval_bridge`, `interpolatedMul_eval_bridge_uses`,
`interpolatedMul_requirements`, `interpolatedMul_usesLocalWitnesses`,
`interpolatedMul_completeness`), generalized to mixed operand lengths. -/

/-- Soundness reading of the `interpolatedMulX` operations: every point
constraint holds. Mirrors `interpolatedMul_soundness`. -/
lemma interpolatedMulX_soundness (off : ℕ)
    (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂) (env : Environment (F p))
    (h : Operations.forAllNoOffset
        { assert := fun e => Expression.eval env e = 0, lookup := fun l => l.Soundness env,
          interact := fun i => i.Guarantees env, subcircuit := fun {_n} s => s.Assumptions env → s.Spec env }
        (interpolatedMulX a b off).2) :
    ∀ cIdx : Fin (n₁ + n₂ - 1),
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr (zVecX n₁ n₂ off) ((cIdx.val + 1 : ℕ) : F p)) := by
  simp only [interpolatedMulX, circuit_norm, zVecX] at h ⊢
  intro cIdx
  have hc := h cIdx
  simp only [Expression.eval] at hc
  rw [add_neg_eq_zero] at hc
  exact hc

/-- Per-element eval bridge for the `interpolatedMulX` output: each coefficient
of the output evaluates like the mixed schoolbook convolution `mulNoReduceX a b`.
Mirrors `interpolatedMul_eval_bridge`. -/
lemma interpolatedMulX_eval_bridge (env : Environment (F p)) (off : ℕ)
    (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂)
    (hpm : n₁ + n₂ - 1 < p)
    (hpts : ∀ cIdx : Fin (n₁ + n₂ - 1),
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr (zVecX n₁ n₂ off) ((cIdx.val + 1 : ℕ) : F p))) :
    ∀ k : Fin (n₁ + n₂ - 1),
      Expression.eval env (interpolatedMulX a b off).1[k.val]
        = Expression.eval env (mulNoReduceX a b)[k.val] := by
  intro k
  rw [interpolatedMulX_output off a b]
  have hvec := interpolatedMulX_map_eval env off a b hpm hpts
  have := congrArg (fun w => w[k.val]) hvec
  simpa only [zVecX, Vector.getElem_map] using this

/-- **Completeness eval bridge.** From the coefficient-witness reads, the
output vector evaluates equal to the mixed schoolbook convolution,
coordinate-wise. Mirrors `interpolatedMul_eval_bridge_uses`. -/
lemma interpolatedMulX_eval_bridge_uses
    (env : Environment (F p)) (off : ℕ) (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂)
    (h : ∀ k : Fin (n₁ + n₂ - 1), env.get (off + k.val)
        = Expression.eval env ((mulNoReduceX a b)[k.val])) :
    ∀ k : Fin (n₁ + n₂ - 1),
      Expression.eval env (interpolatedMulX a b off).1[k.val]
        = Expression.eval env (mulNoReduceX a b)[k.val] := by
  intro k
  rw [interpolatedMulX_output off a b]
  rw [Vector.getElem_mapRange]
  show env.get (off + k.val) = _
  exact h k

/-- The `interpolatedMulX` operations carry no requirements. Mirrors
`interpolatedMul_requirements`. -/
lemma interpolatedMulX_requirements (off : ℕ)
    (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂) (env : Environment (F p)) :
    Operations.forAllNoOffset
      { interact := fun i => i.Requirements env,
        subcircuit := fun {_n} s => s.channelsWithRequirements = [] ∨ s.Assumptions env }
      (interpolatedMulX a b off).2 := by
  simp only [interpolatedMulX, circuit_norm]

/-- From `UsesLocalWitnessesCompleteness`: the coefficient witnesses take their
intended values. Mirrors `interpolatedMul_usesLocalWitnesses`. -/
lemma interpolatedMulX_usesLocalWitnesses (off off' : ℕ)
    (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂)
    (penv : ProverEnvironment (F p)) (heq : off' = off)
    (h : penv.UsesLocalWitnessesCompleteness off' (interpolatedMulX a b off).2) :
    ∀ k : Fin (n₁ + n₂ - 1), penv.toEnvironment.get (off + k.val)
        = Expression.eval penv.toEnvironment ((mulNoReduceX a b)[k.val]) := by
  subst heq
  simp only [interpolatedMulX, circuit_norm] at h
  intro k
  have := h k
  simpa only [Vector.getElem_ofFn] using this

/-- Completeness reading: if every coefficient witness holds, the
`interpolatedMulX` operations are satisfiable. Mirrors
`interpolatedMul_completeness`. -/
lemma interpolatedMulX_completeness (off : ℕ)
    (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂) (penv : ProverEnvironment (F p))
    (h : ∀ k : Fin (n₁ + n₂ - 1), penv.toEnvironment.get (off + k.val)
        = Expression.eval penv.toEnvironment ((mulNoReduceX a b)[k.val])) :
    Operations.forAllNoOffset
      { assert := fun e => Expression.eval penv.toEnvironment e = 0,
        lookup := fun l => l.Completeness penv.toEnvironment,
        interact := fun i => i.Guarantees penv.toEnvironment,
        subcircuit := fun {_n} s => s.ProverAssumptions penv }
      (interpolatedMulX a b off).2 := by
  simp only [interpolatedMulX, circuit_norm]
  intro cIdx
  have hn1 : 0 < n₁ := Nat.pos_of_neZero n₁
  have hn2 : 0 < n₂ := Nat.pos_of_neZero n₂
  set c : F p := (((cIdx.val + 1 : ℕ)) : F p) with hcdef
  rw [add_neg_eq_zero]
  rw [show Expression.eval penv.toEnvironment (polyEvalExpr a c)
        = ∑ i : Fin n₁, Expression.eval penv.toEnvironment a[i.val] * c ^ i.val from polyEvalExpr_eval _ _ _,
    show Expression.eval penv.toEnvironment (polyEvalExpr b c)
        = ∑ i : Fin n₂, Expression.eval penv.toEnvironment b[i.val] * c ^ i.val from polyEvalExpr_eval _ _ _,
    show Expression.eval penv.toEnvironment
          (polyEvalExpr (Vector.mapRange (n₁ + n₂ - 1) fun i => var (F := F p) { index := off + i }) c)
        = ∑ k : Fin (n₁ + n₂ - 1),
            Expression.eval penv.toEnvironment
              (Vector.mapRange (n₁ + n₂ - 1) fun i => var (F := F p) { index := off + i })[k.val] * c ^ k.val
      from polyEvalExpr_eval _ _ _]
  rw [cauchy_diag_mixed hn1 hn2 (fun i : Fin n₁ => Expression.eval penv.toEnvironment a[i.val])
    (fun i : Fin n₂ => Expression.eval penv.toEnvironment b[i.val]) c]
  apply Finset.sum_congr rfl; intro k _
  congr 1
  rw [show (∑ i : Fin n₁, if hh : i.val ≤ k.val ∧ k.val - i.val < n₂ then
        (fun i : Fin n₁ => Expression.eval penv.toEnvironment a[i.val]) i
          * (fun i : Fin n₂ => Expression.eval penv.toEnvironment b[i.val]) ⟨k.val - i.val, hh.2⟩ else 0)
      = Expression.eval penv.toEnvironment (mulNoReduceX a b)[k.val] from by
    rw [eval_mulNoReduceX_coeff penv.toEnvironment a b k]]
  rw [← h k]
  simp only [Vector.getElem_mapRange, Expression.eval]

/-- Evaluation-congruence of `mulNoReduceX` in its first argument: only the
evaluated entries of `a` matter. Used to substitute an interpolation output
(known equal to a schoolbook convolution pointwise) inside a further
`mulNoReduceX`, e.g. bridging `mulNoReduceX z1 b` to `mulNoReduceX (a²) b`. -/
lemma eval_mulNoReduceX_congr_left (env : Environment (F p))
    (a1 a2 : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂)
    (h : ∀ i : Fin n₁, Expression.eval env a1[i.val] = Expression.eval env a2[i.val]) :
    ∀ k : Fin (n₁ + n₂ - 1),
      Expression.eval env (mulNoReduceX a1 b)[k.val] = Expression.eval env (mulNoReduceX a2 b)[k.val] := by
  intro k
  rw [eval_mulNoReduceX_coeff env a1 b k, eval_mulNoReduceX_coeff env a2 b k]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hh : i.val ≤ k.val ∧ k.val - i.val < n₂
  · rw [dif_pos hh, dif_pos hh, h i]
  · rw [dif_neg hh, dif_neg hh]

/-! ## Coefficient-value / bound lemmas for `mulNoReduceX`

Mixed-length generalizations of `Theorems.lean`'s `val_bigIntMulNoReduce_coeff` /
`val_bigIntMulNoReduce_coeff_lt` and `polyValue_bigIntMulNoReduce`, and of
`MulModTheorems.lean`'s `polyValue_mul_eq`. Since `mulNoReduceX a b`'s coefficient
`k` sums a guarded term over the *ambient* `Fin n₁` domain, the coefficient
bound one gets "for free" (as in the equal-length case) is `n₁ · A · Bb`; the
tighter `n₂ · A · Bb` bound (using the *shorter* operand's length) needs the
extra fact that at most `n₂` of the `n₁` guarded terms are nonzero — proved via
the injection `i ↦ k − i` from the guarded index set into `Fin n₂`. -/

/-- `.val` of the evaluated `k`-th mixed convolution coefficient, as a
natural-number guarded sum: no field wraparound occurs under the digit bound
`n₂ * (A * Bb) < p`. Mirrors `val_bigIntMulNoReduce_coeff`. -/
lemma val_mulNoReduceX_coeff {A Bb : ℕ} (env : Environment (F p))
    (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂) (k : Fin (n₁ + n₂ - 1))
    (ha : ∀ i : Fin n₁, (Expression.eval env a[i.val]).val < A)
    (hb : ∀ j : Fin n₂, (Expression.eval env b[j.val]).val < Bb)
    (hbound : n₂ * (A * Bb) < p) :
    (Expression.eval env ((mulNoReduceX a b)[k.val])).val
      = ∑ i : Fin n₁, if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
          (Expression.eval env a[i.val]).val
            * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0 := by
  set S : Finset (Fin n₁) := Finset.univ.filter (fun i => i.val ≤ k.val ∧ k.val - i.val < n₂) with hSdef
  have hcard : S.card ≤ n₂ := by
    have hinj : Set.InjOn (fun i : Fin n₁ => k.val - i.val) (S : Set (Fin n₁)) := by
      intro i hi j hj hij
      simp only [hSdef, Finset.coe_filter, Set.mem_setOf_eq] at hi hj
      simp only at hij
      exact Fin.ext (by omega)
    have hmapsub : S.image (fun i : Fin n₁ => k.val - i.val) ⊆ Finset.range n₂ := by
      intro x hx
      simp only [hSdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨i, ⟨_, hi2⟩, rfl⟩ := hx
      exact Finset.mem_range.mpr hi2
    calc S.card = (S.image (fun i : Fin n₁ => k.val - i.val)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range n₂).card := Finset.card_le_card hmapsub
      _ = n₂ := Finset.card_range n₂
  set natSum : ℕ := ∑ i : Fin n₁, if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
      (Expression.eval env a[i.val]).val * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0
    with hnatSum
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin n₁)), i ∉ S →
      (if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
        (Expression.eval env a[i.val]).val * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0) = 0 := by
    intro i _ hi
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [dif_neg hi]
  have heq : (∑ i ∈ S, if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
        (Expression.eval env a[i.val]).val * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      = natSum :=
    Finset.sum_subset (Finset.subset_univ S) hzero
  have hterm_le : ∀ i ∈ S, (if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
        (Expression.eval env a[i.val]).val * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      ≤ A * Bb - 1 := by
    intro i hi
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [dif_pos hi]
    have h1 := ha i
    have h2 := hb ⟨k.val - i.val, hi.2⟩
    have hmul : (Expression.eval env a[i.val]).val * (Expression.eval env (b[k.val - i.val]'hi.2)).val < A * Bb :=
      Nat.mul_lt_mul'' h1 h2
    omega
  have hnatSum_le : natSum ≤ S.card * (A * Bb - 1) := by
    rw [← heq]
    calc (∑ i ∈ S, if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
          (Expression.eval env a[i.val]).val * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
        ≤ ∑ _i ∈ S, (A * Bb - 1) := Finset.sum_le_sum hterm_le
      _ = S.card * (A * Bb - 1) := by rw [Finset.sum_const, smul_eq_mul]
  have hn2pos : 0 < n₂ := Nat.pos_of_neZero n₂
  have hApos : 0 < A := lt_of_le_of_lt (Nat.zero_le _) (ha ⟨0, Nat.pos_of_neZero n₁⟩)
  have hBpos : 0 < Bb := lt_of_le_of_lt (Nat.zero_le _) (hb ⟨0, Nat.pos_of_neZero n₂⟩)
  have hABpos : 0 < A * Bb := Nat.mul_pos hApos hBpos
  have hnatSum_lt : natSum < n₂ * (A * Bb) := by
    calc natSum ≤ S.card * (A * Bb - 1) := hnatSum_le
      _ ≤ n₂ * (A * Bb - 1) := Nat.mul_le_mul_right _ hcard
      _ < n₂ * (A * Bb) := (Nat.mul_lt_mul_left hn2pos).mpr (by omega)
  have hnatSum_ltp : natSum < p := lt_trans hnatSum_lt hbound
  rw [eval_mulNoReduceX_coeff env a b k]
  have hval_eq : (∑ i : Fin n₁, if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
        (Expression.eval env a[i.val]) * (Expression.eval env (b[k.val - i.val]'h.2)) else 0 : F p)
      = (natSum : F p) := by
    rw [hnatSum, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < n₂
    · simp only [dif_pos h]
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    · simp only [dif_neg h, Nat.cast_zero]
  rw [hval_eq, ZMod.val_natCast_of_lt hnatSum_ltp]

/-- **Coefficient bound** for the mixed schoolbook convolution `mulNoReduceX a b`:
each evaluated convolution coefficient is `< n₂ · A · Bb`, using the length of
the *second* operand (the tighter of the two, when `n₂ ≤ n₁`). Mirrors
`val_bigIntMulNoReduce_coeff_lt`. -/
lemma val_mulNoReduceX_coeff_lt {A Bb : ℕ} (env : Environment (F p))
    (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂) (k : Fin (n₁ + n₂ - 1))
    (ha : ∀ i : Fin n₁, (Expression.eval env a[i.val]).val < A)
    (hb : ∀ j : Fin n₂, (Expression.eval env b[j.val]).val < Bb)
    (hbound : n₂ * (A * Bb) < p) :
    (Expression.eval env ((mulNoReduceX a b)[k.val])).val < n₂ * (A * Bb) := by
  rw [val_mulNoReduceX_coeff env a b k ha hb hbound]
  set S : Finset (Fin n₁) := Finset.univ.filter (fun i => i.val ≤ k.val ∧ k.val - i.val < n₂) with hSdef
  have hcard : S.card ≤ n₂ := by
    have hinj : Set.InjOn (fun i : Fin n₁ => k.val - i.val) (S : Set (Fin n₁)) := by
      intro i hi j hj hij
      simp only [hSdef, Finset.coe_filter, Set.mem_setOf_eq] at hi hj
      simp only at hij
      exact Fin.ext (by omega)
    have hmapsub : S.image (fun i : Fin n₁ => k.val - i.val) ⊆ Finset.range n₂ := by
      intro x hx
      simp only [hSdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨i, ⟨_, hi2⟩, rfl⟩ := hx
      exact Finset.mem_range.mpr hi2
    calc S.card = (S.image (fun i : Fin n₁ => k.val - i.val)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range n₂).card := Finset.card_le_card hmapsub
      _ = n₂ := Finset.card_range n₂
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin n₁)), i ∉ S →
      (if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
        (Expression.eval env a[i.val]).val * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0) = 0 := by
    intro i _ hi
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [dif_neg hi]
  have heq : (∑ i ∈ S, if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
        (Expression.eval env a[i.val]).val * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      = ∑ i : Fin n₁, if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
        (Expression.eval env a[i.val]).val * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0 :=
    Finset.sum_subset (Finset.subset_univ S) hzero
  have hterm_le : ∀ i ∈ S, (if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
        (Expression.eval env a[i.val]).val * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      ≤ A * Bb - 1 := by
    intro i hi
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [dif_pos hi]
    have h1 := ha i
    have h2 := hb ⟨k.val - i.val, hi.2⟩
    have hmul : (Expression.eval env a[i.val]).val * (Expression.eval env (b[k.val - i.val]'hi.2)).val < A * Bb :=
      Nat.mul_lt_mul'' h1 h2
    omega
  have hn2pos : 0 < n₂ := Nat.pos_of_neZero n₂
  have hApos : 0 < A := lt_of_le_of_lt (Nat.zero_le _) (ha ⟨0, Nat.pos_of_neZero n₁⟩)
  have hBpos : 0 < Bb := lt_of_le_of_lt (Nat.zero_le _) (hb ⟨0, Nat.pos_of_neZero n₂⟩)
  rw [← heq]
  calc (∑ i ∈ S, if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
        (Expression.eval env a[i.val]).val * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      ≤ ∑ _i ∈ S, (A * Bb - 1) := Finset.sum_le_sum hterm_le
    _ = S.card * (A * Bb - 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n₂ * (A * Bb - 1) := Nat.mul_le_mul_right _ hcard
    _ < n₂ * (A * Bb) := (Nat.mul_lt_mul_left hn2pos).mpr (by
        have := Nat.mul_pos hApos hBpos
        omega)

/-- Base-`2^B` Cauchy-product recomposition for the mixed schoolbook convolution
`mulNoReduceX a b`: under a digit bound that prevents field overflow, the
base-`2^B` value of the `n₁+n₂-1` convolution coefficients equals the product
of the two operands' base-`2^B` values. Mirrors `polyValue_bigIntMulNoReduce`. -/
lemma polyValue_mulNoReduceX {B A Bb : ℕ} (env : Environment (F p))
    (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂)
    (ha : ∀ i : Fin n₁, (Expression.eval env a[i.val]).val < A)
    (hb : ∀ j : Fin n₂, (Expression.eval env b[j.val]).val < Bb)
    (hbound : n₂ * (A * Bb) < p) :
    polyValue B (Vector.map (Expression.eval env) (mulNoReduceX a b))
      = (∑ i : Fin n₁, (Expression.eval env a[i.val]).val * 2 ^ (B * i.val))
        * (∑ j : Fin n₂, (Expression.eval env b[j.val]).val * 2 ^ (B * j.val)) := by
  set av : ℕ → ℕ := fun i => if h : i < n₁ then (Expression.eval env a[i]).val else 0 with hav
  set bv : ℕ → ℕ := fun j => if h : j < n₂ then (Expression.eval env b[j]).val else 0 with hbv
  have hAsum : (∑ i : Fin n₁, (Expression.eval env a[i.val]).val * 2 ^ (B * i.val))
      = ∑ i ∈ Finset.range n₁, av i * 2 ^ (B * i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => av i * 2 ^ (B * i))]
    apply Finset.sum_congr rfl
    intro i _; simp only [hav, dif_pos i.isLt]
  have hBsum : (∑ j : Fin n₂, (Expression.eval env b[j.val]).val * 2 ^ (B * j.val))
      = ∑ j ∈ Finset.range n₂, bv j * 2 ^ (B * j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => bv j * 2 ^ (B * j))]
    apply Finset.sum_congr rfl
    intro j _; simp only [hbv, dif_pos j.isLt]
  rw [hAsum, hBsum, cauchy_base_pow_mixed B n₁ n₂ av bv]
  rw [polyValue]
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => (∑ i ∈ Finset.range n₁, if i ≤ k ∧ k - i < n₂ then av i * bv (k - i) else 0)
      * 2 ^ (B * k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [Vector.getElem_map, val_mulNoReduceX_coeff env a b k ha hb hbound]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => if i ≤ k.val ∧ k.val - i < n₂ then av i * bv (k.val - i) else 0)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val ≤ k.val ∧ k.val - i.val < n₂
  · rw [dif_pos h, if_pos h]
    simp only [hav, hbv, dif_pos i.isLt, dif_pos h.2]
  · rw [dif_neg h, if_neg h]

/-- **Bridge (mixed multiply side).** Base-`2^B` value of the mixed schoolbook
convolution of `a`, `b` equals the product of the two operands' values. Mirrors
`polyValue_mul_eq`. -/
lemma polyValue_mulX_eq {B A Bb : ℕ} (env : Environment (F p))
    (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂)
    (ha : ∀ i : Fin n₁, (Expression.eval env a[i.val]).val < A)
    (hb : ∀ j : Fin n₂, (Expression.eval env b[j.val]).val < Bb)
    (hbound : n₂ * (A * Bb) < p) :
    polyValue B (Vector.map (Expression.eval env) (mulNoReduceX a b))
      = BigInt.value B (Vector.map (Expression.eval env) a)
        * BigInt.value B (Vector.map (Expression.eval env) b) := by
  rw [polyValue_mulNoReduceX env a b ha hb hbound, value_map_eval, value_map_eval]

end

end MulMod

end

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

/-- `2m` is nonzero whenever `m` is. Needed to instantiate `NormalizeTight`,
`ProvableType.witness`, etc. at the `2m`-limb quotient `q`. -/
instance : NeZero (2 * m) := ⟨by have := Nat.pos_of_neZero m; omega⟩

/-- `2m-1` is nonzero whenever `m` is. Needed to feed `z1 = interpolatedMul a a`
(a `Vector _ (2*m-1)`) into `interpolatedMulX`, which is generic in the
(nonzero) lengths of both its arguments. -/
instance : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩

namespace SqMulModTo

open MulModTo (InputsTo)

/-- The `main` circuit of `SqMulModTo`: witness `q = (a²·b)/n` over `2m` limbs,
tight-normalize it (top limb `< 2^tq`), build the three convolution coefficient
vectors `a²`, `a²·b`, `q·n` by (mixed-length) interpolation multiplication, pad
both sides to the common length `2m+m-1`, and assert `a²·b = q·n + em` in base
`2^B` via `GroupedEqX` (with `em`'s limbs added on the affine right-hand side). -/
def main (P : BigIntParams p m) (P2 : BigIntParams p (2 * m)) (XB : ℕ)
    (tq : ℕ) (htq : 1 ≤ tq ∧ 2 ^ tq < p) (htqB : tq ≤ P2.B) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams) (hgvx : GroupedEqXV.GVXHyps p (2 * m + m - 1) XB gf posOf G V VR) (hXB1 : 1 ≤ XB)
    (hB2 : P2.B = P.B) (hXB : XB = P.B) [Fact (p > 2)]
    (input : Var (InputsTo m) (F p)) : Circuit (F p) Unit := do
  let a := input.a
  let b := input.b
  let n := input.modulus
  let em := input.em

  let q ← ProvableType.witness (α := BigInt (2 * m)) fun env =>
    let prod := MulMod.evalValue P.B env a * MulMod.evalValue P.B env a * MulMod.evalValue P.B env b
    let qval : ℕ := prod / MulMod.evalValue P.B env n
    Vector.ofFn fun k : Fin (2 * m) => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  NormalizeTight.circuit P2 tq htq htqB q

  let z1 ← MulMod.interpolatedMul a a
  let z2 ← MulMod.interpolatedMulX z1 b
  let z3 ← MulMod.interpolatedMulX q n

  let lhsPad : Vector (Expression (F p)) (2 * m + m - 1) :=
    Vector.mapFinRange (2 * m + m - 1) fun k =>
      if h : k.val < (2 * m - 1) + m - 1 then z2[k.val]'h else 0
  let rhsS : Vector (Expression (F p)) (2 * m + m - 1) :=
    Vector.mapFinRange (2 * m + m - 1) fun k =>
      if h : k.val < (2 * m) + m - 1 then
        (if hm : k.val < m then z3[k.val]'h + em[k.val]'hm else z3[k.val]'h)
      else 0

  GroupedEqXV.circuit (L := 2 * m + m - 1) XB gf posOf G V VR hgvx hXB1
    { lhs := lhsPad, rhs := rhsS }

instance elaborated (P : BigIntParams p m) (P2 : BigIntParams p (2 * m)) (XB : ℕ)
    (tq : ℕ) (htq : 1 ≤ tq ∧ 2 ^ tq < p) (htqB : tq ≤ P2.B) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams) (hgvx : GroupedEqXV.GVXHyps p (2 * m + m - 1) XB gf posOf G V VR) (hXB1 : 1 ≤ XB)
    (hB2 : P2.B = P.B) (hXB : XB = P.B) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (InputsTo m) unit (main P P2 XB tq htq htqB gf posOf G V VR hgvx hXB1 hB2 hXB) where
  localLength _ :=
    2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1))
      + ((2 * m - 1) + ((2 * m - 1) + m - 1) + ((2 * m) + m - 1))
      + GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0
  localLength_eq := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, MulMod.interpolatedMulX, circuit_norm,
      NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      GroupedEqXV.circuit, GroupedEqXV.elaborated, RangeCheck.circuit]
    omega
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, MulMod.interpolatedMul, MulMod.interpolatedMulX, circuit_norm,
      NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      GroupedEqXV.circuit, GroupedEqXV.elaborated, RangeCheck.circuit]
  channelsLawful := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, MulMod.interpolatedMulX, circuit_norm,
      NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      GroupedEqXV.circuit, GroupedEqXV.elaborated, RangeCheck.circuit]

/-- Preconditions: all four operands normalized; `a` tight (`< 2^((m-1)B+tb)`);
`b < n`; `em < n` (so `em` is the canonical residue). No tight bound is needed on
`b` (it only ever appears un-squared) and no modulus lower bound is needed (the
quotient fit is certified directly via `htbq`, not via a lower bound on `n`). -/
def Assumptions (B tb : ℕ) (input : InputsTo m (F p)) : Prop :=
  input.a.Normalized B ∧ input.b.Normalized B ∧ input.modulus.Normalized B ∧
    input.em.Normalized B ∧
    input.a.value B < 2 ^ ((m - 1) * B + tb) ∧
    input.b.value B < input.modulus.value B ∧
    input.em.value B < input.modulus.value B ∧
    input.modulus.value B < 2 ^ ((m - 1) * B + tb)

/-- Postcondition: `em` is exactly the canonical residue of `a²·b` mod `n`. -/
def Spec (B : ℕ) (input : InputsTo m (F p)) : Prop :=
  input.em.value B = input.a.value B * input.a.value B * input.b.value B % input.modulus.value B

/-! ## Support lemmas: the padded `lhsPad`/`rhsS` coefficient vectors -/

/-- The padded LHS coefficient vector of `SqMulModTo` (schoolbook form): the
`(2m-1)+m-1` coefficients of the second interpolation output `Z2`, zero-padded
to the common length `2m+m-1`. Matches `main`'s `lhsPad` exactly. -/
def lhsPadVec (Z2 : Vector (Expression (F p)) ((2 * m - 1) + m - 1)) :
    Vector (Expression (F p)) (2 * m + m - 1) :=
  Vector.mapFinRange (2 * m + m - 1) fun k =>
    if h : k.val < (2 * m - 1) + m - 1 then Z2[k.val]'h else 0

/-- The padded RHS coefficient vector of `SqMulModTo`: `Z3`'s `2m+m-1`
coefficients (the third interpolation output, `q·n`'s schoolbook coefficients)
with `em`'s limbs added in the low `m` positions. Matches `main`'s `rhsS`
exactly. -/
def rhsSVec (Z3 : Vector (Expression (F p)) ((2 * m) + m - 1)) (em : Var (BigInt m) (F p)) :
    Vector (Expression (F p)) (2 * m + m - 1) :=
  Vector.mapFinRange (2 * m + m - 1) fun k =>
    if h : k.val < (2 * m) + m - 1 then
      (if hm : k.val < m then Z3[k.val]'h + em[k.val]'hm else Z3[k.val]'h)
    else 0

/-- Two coefficient-expression vectors that agree pointwise as evaluated field
values under `env` have the same `polyValue`. -/
lemma polyValue_congr {k B : ℕ} (env : Environment (F p)) (u v : Vector (Expression (F p)) k)
    (h : ∀ i : Fin k, Expression.eval env u[i.val] = Expression.eval env v[i.val]) :
    polyValue B (Vector.map (Expression.eval env) u) = polyValue B (Vector.map (Expression.eval env) v) := by
  unfold polyValue
  apply Finset.sum_congr rfl
  intro i _
  rw [Vector.getElem_map, Vector.getElem_map, h i]

/-- `BigInt.value` and `polyValue` compute the same base-`2^B` positional sum
(they differ only in intended use: `BigInt.value` for the fixed `m`-limb
representation, `polyValue` for a convolution's coefficient vector). -/
lemma value_eq_polyValue {k B : ℕ} (x : BigInt k (F p)) :
    BigInt.value B x = polyValue B x := by
  rw [BigInt.value_eq_sum]; rfl

/-- Dropping the (zero) top-index pad of `lhsPadVec`: `polyValue lhsPad = polyValue Z2`. -/
lemma polyValue_lhsPad_drop {B : ℕ} (env : Environment (F p))
    (Z2 : Vector (Expression (F p)) ((2 * m - 1) + m - 1)) :
    polyValue B (Vector.map (Expression.eval env) (lhsPadVec Z2))
      = polyValue B (Vector.map (Expression.eval env) Z2) := by
  have hm : 0 < m := Nat.pos_of_neZero m
  set f : ℕ → ℕ := fun j => if h : j < (2 * m - 1) + m - 1 then (Expression.eval env (Z2[j]'h)).val else 0
    with hf
  have h1 : polyValue B (Vector.map (Expression.eval env) Z2)
      = ∑ j ∈ Finset.range ((2 * m - 1) + m - 1), f j * 2 ^ (B * j) := by
    rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun j => f j * 2 ^ (B * j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [Vector.getElem_map]
    congr 1
    simp only [hf, dif_pos i.isLt]
  have h2 : polyValue B (Vector.map (Expression.eval env) (lhsPadVec Z2))
      = ∑ j ∈ Finset.range (2 * m + m - 1), f j * 2 ^ (B * j) := by
    rw [polyValue, ← Fin.sum_univ_eq_sum_range (fun j => f j * 2 ^ (B * j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [Vector.getElem_map]
    simp only [lhsPadVec, Vector.getElem_mapFinRange]
    by_cases h : i.val < (2 * m - 1) + m - 1
    · simp only [dif_pos h, hf]
    · simp only [dif_neg h, hf, Expression.eval, ZMod.val_zero]
  rw [h1, h2, show 2 * m + m - 1 = ((2 * m - 1) + m - 1) + 1 from by omega, Finset.sum_range_succ]
  have hftop : f ((2 * m - 1) + m - 1) = 0 := by
    simp only [hf, dif_neg (lt_irrefl ((2 * m - 1) + m - 1))]
  rw [hftop, Nat.zero_mul, Nat.add_zero]

/-- Splitting `rhsS = Z3 + em` (low limbs): `polyValue rhsS = polyValue Z3 + em.value`,
provided each low coefficient does not wrap mod `p`. Mirrors `MulModTo.polyValue_sVecEm_split`. -/
lemma polyValue_rhsS_split {B : ℕ} (env : Environment (F p))
    (Z3 : Vector (Expression (F p)) ((2 * m) + m - 1)) (em : Var (BigInt m) (F p))
    (hnowrap : ∀ k : Fin (2 * m + m - 1), (hk : k.val < m) →
      (Expression.eval env (Z3[k.val]'k.isLt)).val
        + (Expression.eval env (em[k.val]'hk)).val < p) :
    polyValue B (Vector.map (Expression.eval env) (rhsSVec Z3 em))
      = polyValue B (Vector.map (Expression.eval env) Z3)
        + BigInt.value B (Vector.map (Expression.eval env) em) := by
  rw [polyValue, polyValue, MulMod.value_map_eval]
  have hS : ∀ k : Fin (2 * m + m - 1),
      ((Vector.map (Expression.eval env) (rhsSVec Z3 em))[k.val]).val
        = (Expression.eval env (Z3[k.val]'k.isLt)).val
          + (if h : k.val < m then (Expression.eval env (em[k.val]'h)).val else 0) := by
    intro k
    rw [Vector.getElem_map]
    simp only [rhsSVec, Vector.getElem_mapFinRange]
    rw [dif_pos k.isLt]
    by_cases hk : k.val < m
    · simp only [dif_pos hk]
      rw [show Expression.eval env (Z3[k.val]'k.isLt + em[k.val]'hk)
            = Expression.eval env (Z3[k.val]'k.isLt) + Expression.eval env (em[k.val]'hk) from rfl,
        ZMod.val_add_of_lt (hnowrap k hk)]
    · simp only [dif_neg hk, Nat.add_zero]
  simp only [hS]
  rw [show (∑ k : Fin (2 * m + m - 1),
        ((Expression.eval env (Z3[k.val]'k.isLt)).val
          + (if h : k.val < m then (Expression.eval env (em[k.val]'h)).val else 0))
          * 2 ^ (B * k.val))
      = (∑ k : Fin (2 * m + m - 1),
          (Expression.eval env (Z3[k.val]'k.isLt)).val * 2 ^ (B * k.val))
        + (∑ k : Fin (2 * m + m - 1),
          (if h : k.val < m then (Expression.eval env (em[k.val]'h)).val else 0)
            * 2 ^ (B * k.val)) from by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; ring]
  congr 1
  · apply Finset.sum_congr rfl; intro k _; rw [Vector.getElem_map]
  · have hm : 0 < m := Nat.pos_of_neZero m
    have hLHS : (∑ k : Fin (2 * m + m - 1),
          (if h : k.val < m then (Expression.eval env (em[k.val]'h)).val else 0) * 2 ^ (B * k.val))
        = ∑ k ∈ Finset.range (2 * m + m - 1),
          (if h : k < m then (Expression.eval env (em[k]'h)).val else 0) * 2 ^ (B * k) := by
      rw [← Fin.sum_univ_eq_sum_range (fun k =>
        (if h : k < m then (Expression.eval env (em[k]'h)).val else 0) * 2 ^ (B * k))]
    rw [hLHS]
    have hsub : Finset.range m ⊆ Finset.range (2 * m + m - 1) := by
      intro t ht
      simp only [Finset.mem_range] at ht ⊢
      omega
    rw [← Finset.sum_subset hsub (fun k _ hnk => by
      rw [dif_neg (by simpa using hnk), Nat.zero_mul])]
    rw [← Fin.sum_univ_eq_sum_range (fun k =>
      (if h : k < m then (Expression.eval env (em[k]'h)).val else 0) * 2 ^ (B * k))]
    apply Finset.sum_congr rfl
    intro k _
    rw [dif_pos k.isLt]

/-! ## Small arithmetic helpers -/

/-- `3m-1 < p` follows from the `BigIntParams` field bound `P.hp`, exactly like
`MulMod.two_m_sub_one_lt`'s `2m-1 < p`; used for the point-distinctness bound of
all three interpolation calls (`2m-1 < p`, `(2m-1)+m-1 < p`, `(2m)+m-1 < p` are
all `≤ 3m-1 < p`). -/
lemma three_m_sub_one_lt {B : ℕ} (hp : 2 ^ (2 * B) * (m + 1) * 4 < p) :
    3 * m - 1 < p := by
  have hpow : 1 ≤ 2 ^ (2 * B) := Nat.one_le_two_pow
  have hge : 2 ^ (2 * B) * (m + 1) * 4 ≥ 1 * (m + 1) * 4 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hpow)
  omega

/-- The `q·n`-side coefficient bound `m·2^(2B)` plus the `em` digit bound `2^B`
is `≤ m²·2^(3B)`, for `1 ≤ B`, `1 ≤ m`. Feeds `coeff_rhsS_bound` via `hNX`. -/
lemma rhs_bound_le_hNX {B : ℕ} (hB1 : 1 ≤ B) (hm1 : 1 ≤ m) :
    m * 2 ^ (2 * B) + 2 ^ B ≤ m ^ 2 * 2 ^ (3 * B) := by
  have hX2 : (2 : ℕ) ≤ 2 ^ B := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB1
  have e2B : (2 : ℕ) ^ (2 * B) = 2 ^ B * 2 ^ B := by rw [two_mul, pow_add]
  have e3B : (2 : ℕ) ^ (3 * B) = 2 ^ B * 2 ^ B * 2 ^ B := by
    rw [show 3 * B = B + B + B from by ring, pow_add, pow_add]
  rw [e2B, e3B]
  set X := (2 : ℕ) ^ B with hXdef
  have hXle : X ≤ X * X := by
    calc X = X * 1 := (Nat.mul_one X).symm
      _ ≤ X * X := Nat.mul_le_mul_left X (by omega)
  have hmle : m ≤ m * m := by
    calc m = m * 1 := (Nat.mul_one m).symm
      _ ≤ m * m := Nat.mul_le_mul_left m hm1
  have step1 : X ≤ m * (X * X) := by
    calc X ≤ X * X := hXle
      _ = 1 * (X * X) := (Nat.one_mul _).symm
      _ ≤ m * (X * X) := Nat.mul_le_mul_right _ hm1
  have step2 : m * (X * X) + X ≤ 2 * (m * (X * X)) := by omega
  have step3 : (2 : ℕ) * (m * (X * X)) ≤ m * (X * X * X) := by
    have hXXX : (2 : ℕ) * (X * X) ≤ X * X * X := by
      calc (2 : ℕ) * (X * X) ≤ X * (X * X) := by
            apply Nat.mul_le_mul_right
            omega
        _ = X * X * X := by ring
    calc (2 : ℕ) * (m * (X * X)) = m * (2 * (X * X)) := by ring
      _ ≤ m * (X * X * X) := Nat.mul_le_mul_left m hXXX
  have step4 : m * (X * X * X) ≤ m * m * (X * X * X) := by
    calc m * (X * X * X) = 1 * m * (X * X * X) := by ring
      _ ≤ m * m * (X * X * X) := by
          apply Nat.mul_le_mul_right
          calc (1 : ℕ) * m ≤ m * m := by rw [Nat.one_mul]; exact hmle
            _ = m * m := rfl
  calc m * (X * X) + X ≤ 2 * (m * (X * X)) := step2
    _ ≤ m * (X * X * X) := step3
    _ ≤ m * m * (X * X * X) := step4
    _ = m ^ 2 * (X * X * X) := by ring

/-- Coefficient bound for the padded LHS vector `lhsPadVec Z2`: every coefficient
`.val < N`, given the second-interpolation output bound and the pad (`0 < N`). -/
lemma coeff_lhsPad_bound {N : ℕ} (env : Environment (F p))
    (Z2 : Vector (Expression (F p)) ((2 * m - 1) + m - 1))
    (hZ2 : ∀ k : Fin ((2 * m - 1) + m - 1), (Expression.eval env Z2[k.val]).val < N)
    (hNpos : 0 < N) (k : Fin (2 * m + m - 1)) :
    (Expression.eval env ((lhsPadVec Z2)[k.val])).val < N := by
  simp only [lhsPadVec, Vector.getElem_mapFinRange]
  by_cases h : k.val < (2 * m - 1) + m - 1
  · rw [dif_pos h]; exact hZ2 ⟨k.val, h⟩
  · rw [dif_neg h]
    simp only [Expression.eval, ZMod.val_zero]
    exact hNpos

/-- Coefficient bound for the padded RHS vector `rhsSVec Z3 em`: every
coefficient `.val < N`, given the third-interpolation output bound `m·2^(2B)`,
the `em` digit bound `2^B`, and `m·2^(2B)+2^B ≤ N`. -/
lemma coeff_rhsS_bound {B N : ℕ} (env : Environment (F p))
    (Z3 : Vector (Expression (F p)) ((2 * m) + m - 1)) (em : Var (BigInt m) (F p))
    (hZ3 : ∀ k : Fin ((2 * m) + m - 1), (Expression.eval env Z3[k.val]).val < m * 2 ^ (2 * B))
    (hem_d : ∀ j : ℕ, (hj : j < m) → (Expression.eval env (em[j]'hj)).val < 2 ^ B)
    (hN : m * 2 ^ (2 * B) + 2 ^ B ≤ N) (k : Fin (2 * m + m - 1)) :
    (Expression.eval env ((rhsSVec Z3 em)[k.val])).val < N := by
  simp only [rhsSVec, Vector.getElem_mapFinRange]
  rw [dif_pos k.isLt]
  by_cases hkm : k.val < m
  · rw [dif_pos hkm]
    have h1 := hZ3 k
    have h2 := hem_d k.val hkm
    have hadd : (Expression.eval env (Z3[k.val]'k.isLt) + Expression.eval env (em[k.val]'hkm)).val
        ≤ (Expression.eval env (Z3[k.val]'k.isLt)).val + (Expression.eval env (em[k.val]'hkm)).val :=
      ZMod.val_add_le _ _
    rw [show Expression.eval env (Z3[k.val]'k.isLt + em[k.val]'hkm)
          = Expression.eval env (Z3[k.val]'k.isLt) + Expression.eval env (em[k.val]'hkm) from rfl]
    omega
  · rw [dif_neg hkm]
    have h1 := hZ3 k
    have hc0 : 0 ≤ (2 : ℕ) ^ B := Nat.zero_le _
    omega

/-! ## The arithmetic core -/

/-- **Soundness core** (witnessed-product form). From the `GroupedEqX`
implication over the padded vectors `lhsPadVec Z2`/`rhsSVec Z3 em`, together
with the eval-bridges connecting `Z1,Z2,Z3` to their schoolbook meanings
(`a²`, `a²·b`, `q·n`), derive `a²·b = q·n + em` over `ℕ`, hence
`em = (a²·b) mod n` (using `em < n`). -/
lemma soundness_core_wm {B XB tb tq : ℕ} (NfL NfR : ℕ → ℕ) (hXBeq : XB = B) (hB1 : 1 ≤ B) (hm1 : 1 ≤ m)
    (htbB : tb ≤ B) (htqB : tq ≤ B)
    (hNp : m ^ 2 * 2 ^ (3 * B) < p)
    (hf2 : (3 * m) * (3 * m) * ((2 ^ B - 1) * (2 ^ B - 1) * (2 ^ B - 1)) < p)
    (hf3 : (3 * m) * ((2 ^ B - 1) * (2 ^ B - 1)) < p)
    (hlhs_ad : ∀ k, WindowCaps.triCapW B tb m k < NfL k)
    (hrhs_ad : ∀ k, WindowCaps.qnCapW B tb tq m k + 2 ^ B ≤ NfR k)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n em : Var (BigInt m) (F p))
    (Z1 : Vector (Expression (F p)) (2 * m - 1))
    (Z2 : Vector (Expression (F p)) ((2 * m - 1) + m - 1))
    (Z3 : Vector (Expression (F p)) ((2 * m) + m - 1))
    (av bv nv emv : BigInt m (F p))
    (h_a : Vector.map (Expression.eval env) a = av)
    (h_b : Vector.map (Expression.eval env) b = bv)
    (h_n : Vector.map (Expression.eval env) n = nv)
    (h_em : Vector.map (Expression.eval env) em = emv)
    (ha_norm : av.Normalized B) (hb_norm : bv.Normalized B)
    (hn_norm : nv.Normalized B) (hem_norm : emv.Normalized B)
    (hem_lt : emv.value B < nv.value B)
    (hq_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange (2 * m) fun i ↦ var { index := i₀ + i })))
    (ha_top : (av[m - 1]'(by have := Nat.pos_of_neZero m; omega)).val < 2 ^ tb)
    (hb_top : (bv[m - 1]'(by have := Nat.pos_of_neZero m; omega)).val < 2 ^ tb)
    (hn_top : (nv[m - 1]'(by have := Nat.pos_of_neZero m; omega)).val < 2 ^ tb)
    (hq_top : (((Vector.map (Expression.eval env)
        (Vector.mapRange (2 * m) fun i ↦ var { index := i₀ + i }))[2 * m - 1]'(by
          have := Nat.pos_of_neZero m; omega)).val) < 2 ^ tq)
    (heqZ1_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Z1[k.val] = Expression.eval env (bigIntMulNoReduce a a)[k.val])
    (heqZ2_get : ∀ k : Fin ((2 * m - 1) + m - 1),
      Expression.eval env Z2[k.val] = Expression.eval env (MulMod.mulNoReduceX Z1 b)[k.val])
    (heqZ3_get : ∀ k : Fin ((2 * m) + m - 1),
      Expression.eval env Z3[k.val]
        = Expression.eval env
            (MulMod.mulNoReduceX (Vector.mapRange (2 * m) fun i ↦ var { index := i₀ + i }) n)[k.val])
    (h_eq_impl :
      ((∀ k : Fin (2 * m + m - 1),
          (Expression.eval env
            (if h : k.val < (2 * m - 1) + m - 1 then Z2[k.val]'h else 0)).val < NfL k.val) ∧
        ∀ k : Fin (2 * m + m - 1),
          (Expression.eval env
            (if h : k.val < (2 * m) + m - 1 then
              (if hm : k.val < m then Z3[k.val]'h + em[k.val]'hm else Z3[k.val]'h)
            else 0)).val < NfR k.val) →
        polyValue XB (Vector.map (Expression.eval env) (lhsPadVec Z2)) =
          polyValue XB (Vector.map (Expression.eval env) (rhsSVec Z3 em))) :
    emv.value B = av.value B * av.value B * bv.value B % nv.value B := by
  rw [hXBeq] at h_eq_impl
  set qVar := (Vector.mapRange (2 * m) fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  have hm : 0 < m := Nat.pos_of_neZero m
  have ha_lt : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env a[i.val] = av[i.val] from by
      rw [← h_a]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env b[i.val] = bv[i.val] from by
      rw [← h_b]; simp only [Vector.getElem_map]]; exact hb_norm i
  have hn_lt : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env n[i.val] = nv[i.val] from by
      rw [← h_n]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hem_d : ∀ j : ℕ, (hj : j < m) → (Expression.eval env (em[j]'hj)).val < 2 ^ B := by
    intro j hj
    rw [show Expression.eval env (em[j]'hj) = emv[j]'hj from by
      rw [← h_em]; simp only [Vector.getElem_map]]
    exact hem_norm ⟨j, hj⟩
  have hqd_lt : ∀ i : Fin (2 * m), (Expression.eval env qVar[i.val]).val < 2 ^ B := by
    intro i; have := hq_norm i; rwa [Fin.getElem_fin, Vector.getElem_map] at this
  -- field no-wrap facts
  have hfield_aa : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have hle1 : m ≤ m ^ 2 := by
      calc m = m * 1 := (Nat.mul_one m).symm
        _ ≤ m * m := Nat.mul_le_mul_left m hm
        _ = m ^ 2 := (sq m).symm
    have hle2 : (2 : ℕ) ^ (2 * B) ≤ 2 ^ (3 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : m * 2 ^ (2 * B) ≤ m ^ 2 * 2 ^ (3 * B) :=
      calc m * 2 ^ (2 * B) ≤ m ^ 2 * 2 ^ (2 * B) := Nat.mul_le_mul_right _ hle1
        _ ≤ m ^ 2 * 2 ^ (3 * B) := Nat.mul_le_mul_left _ hle2
    omega
  have hfield_qn : m * (2 ^ B * 2 ^ B) < p := hfield_aa
  have hcube_eq : m * (m * 2 ^ (2 * B) * 2 ^ B) = m ^ 2 * 2 ^ (3 * B) := by
    rw [show (3 : ℕ) * B = 2 * B + B from by ring, pow_add]; ring
  have hfield_Z1b : m * (m * 2 ^ (2 * B) * 2 ^ B) < p := by rw [hcube_eq]; exact hNp
  -- Z1 bound (a² convolution coefficients)
  have haa_bound : ∀ i : Fin (2 * m - 1),
      (Expression.eval env ((bigIntMulNoReduce a a))[i.val]).val < m * 2 ^ (2 * B) :=
    fun i => val_bigIntMulNoReduce_coeff_lt env a a i ha_lt ha_lt hfield_aa
  have hZ1_bound : ∀ i : Fin (2 * m - 1), (Expression.eval env Z1[i.val]).val < m * 2 ^ (2 * B) := by
    intro i; rw [heqZ1_get i]; exact haa_bound i
  -- Z2 bound (a²·b convolution coefficients)
  have hZ2_bound : ∀ k : Fin ((2 * m - 1) + m - 1),
      (Expression.eval env Z2[k.val]).val < m ^ 2 * 2 ^ (3 * B) := by
    intro k
    rw [heqZ2_get k, ← hcube_eq]
    exact MulMod.val_mulNoReduceX_coeff_lt env Z1 b k hZ1_bound hb_lt hfield_Z1b
  -- Z3 bound (q·n convolution coefficients)
  have hZ3_bound : ∀ k : Fin ((2 * m) + m - 1),
      (Expression.eval env Z3[k.val]).val < m * 2 ^ (2 * B) := by
    intro k
    rw [heqZ3_get k, show m * 2 ^ (2 * B) = m * (2 ^ B * 2 ^ B) from by rw [two_mul, pow_add]]
    exact MulMod.val_mulNoReduceX_coeff_lt env qVar n k hqd_lt hn_lt hfield_qn
  have ha_top' : (Expression.eval env (a[m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tb := by
    rw [show Expression.eval env (a[m - 1]'(by have := Nat.pos_of_neZero m; omega))
        = av[m - 1]'(by have := Nat.pos_of_neZero m; omega) from by
      rw [← h_a]; simp only [Vector.getElem_map]]
    exact ha_top
  have hb_top' : (Expression.eval env (b[m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tb := by
    rw [show Expression.eval env (b[m - 1]'(by have := Nat.pos_of_neZero m; omega))
        = bv[m - 1]'(by have := Nat.pos_of_neZero m; omega) from by
      rw [← h_b]; simp only [Vector.getElem_map]]
    exact hb_top
  have hn_top' : (Expression.eval env (n[m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tb := by
    rw [show Expression.eval env (n[m - 1]'(by have := Nat.pos_of_neZero m; omega))
        = nv[m - 1]'(by have := Nat.pos_of_neZero m; omega) from by
      rw [← h_n]; simp only [Vector.getElem_map]]
    exact hn_top
  have hq_top' : (Expression.eval env (qVar[2 * m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tq := by
    have h := hq_top
    rwa [Vector.getElem_map] at h
  -- discharge GroupedEqX's `Assumptions` antecedent and invoke its `Spec`
  have hNf_pos : ∀ j, 0 < NfL j := by
    intro j; exact lt_of_le_of_lt (Nat.zero_le _) (hlhs_ad j)
  have hlhs_bound' : ∀ k : Fin (2 * m + m - 1),
      (Expression.eval env (if h : k.val < (2 * m - 1) + m - 1 then Z2[k.val]'h else 0)).val < NfL k.val := by
    intro k
    by_cases h : k.val < (2 * m - 1) + m - 1
    · rw [dif_pos h]
      have hz2 := WindowCaps.z2_coeff_leW env a b Z1 ⟨k.val, h⟩ hm1 htbB heqZ1_get ha_lt hb_lt
        ha_top' hb_top' hfield_aa hf2
      have hbridge : Expression.eval env (Z2[k.val]'h)
          = Expression.eval env ((MulMod.mulNoReduceX Z1 b)[k.val]) := heqZ2_get ⟨k.val, h⟩
      rw [hbridge]
      exact lt_of_le_of_lt hz2 (hlhs_ad k.val)
    · rw [dif_neg h]
      simp only [Expression.eval, ZMod.val_zero]
      exact hNf_pos k.val
  have hrhs_bound' : ∀ k : Fin (2 * m + m - 1),
      (Expression.eval env (if h : k.val < (2 * m) + m - 1 then
        (if hm : k.val < m then Z3[k.val]'h + em[k.val]'hm else Z3[k.val]'h) else 0)).val < NfR k.val := by
    intro k
    rw [dif_pos k.isLt]
    have hz3 := WindowCaps.z3_coeff_leW env qVar n ⟨k.val, k.isLt⟩ hm1 htbB htqB hqd_lt hn_lt
      hq_top' hn_top' hf3
    have hbridge3 : Expression.eval env (Z3[k.val]'k.isLt)
        = Expression.eval env ((MulMod.mulNoReduceX qVar n)[k.val]) := heqZ3_get ⟨k.val, k.isLt⟩
    have hz3val : (Expression.eval env (Z3[k.val]'k.isLt)).val ≤ WindowCaps.qnCapW B tb tq m k.val := by
      rw [hbridge3]; exact hz3
    have had := hrhs_ad k.val
    by_cases hkm : k.val < m
    · rw [dif_pos hkm]
      have hval_add : (Expression.eval env (Z3[k.val]'k.isLt + em[k.val]'hkm)).val
          ≤ (Expression.eval env (Z3[k.val]'k.isLt)).val + (Expression.eval env (em[k.val]'hkm)).val := by
        rw [show Expression.eval env (Z3[k.val]'k.isLt + em[k.val]'hkm)
            = Expression.eval env (Z3[k.val]'k.isLt) + Expression.eval env (em[k.val]'hkm) from rfl]
        exact ZMod.val_add_le _ _
      have hemval : (Expression.eval env (em[k.val]'hkm)).val < 2 ^ B := hem_d k.val hkm
      omega
    · rw [dif_neg hkm]
      have h2 : 0 < 2 ^ B := Nat.two_pow_pos B
      omega
  have h_polyeq := h_eq_impl ⟨hlhs_bound', hrhs_bound'⟩
  -- LHS chain: polyValue lhsPad = av.value · av.value · bv.value
  have hLHS : polyValue B (Vector.map (Expression.eval env) (lhsPadVec Z2))
      = av.value B * av.value B * bv.value B := by
    rw [polyValue_lhsPad_drop env Z2, polyValue_congr env Z2 (MulMod.mulNoReduceX Z1 b) heqZ2_get,
      polyValue_congr env (MulMod.mulNoReduceX Z1 b) (MulMod.mulNoReduceX (bigIntMulNoReduce a a) b)
        (MulMod.eval_mulNoReduceX_congr_left env Z1 (bigIntMulNoReduce a a) b heqZ1_get),
      MulMod.polyValue_mulX_eq env (bigIntMulNoReduce a a) b haa_bound hb_lt hfield_Z1b,
      value_eq_polyValue, MulMod.polyValue_mul_eq env a a ha_lt ha_lt hfield_aa, h_a, h_b]
  -- RHS chain: polyValue rhsS = qVar.value · nv.value + emv.value
  have hnowrap : ∀ k : Fin (2 * m + m - 1), (hk : k.val < m) →
      (Expression.eval env (Z3[k.val]'k.isLt)).val + (Expression.eval env (em[k.val]'hk)).val < p := by
    intro k hk
    have h1 := hZ3_bound k
    have h2 := hem_d k.val hk
    have h3 := rhs_bound_le_hNX hB1 hm
    omega
  have hRHS : polyValue B (Vector.map (Expression.eval env) (rhsSVec Z3 em))
      = BigInt.value B (Vector.map (Expression.eval env) qVar) * nv.value B + emv.value B := by
    rw [polyValue_rhsS_split env Z3 em hnowrap,
      polyValue_congr env Z3 (MulMod.mulNoReduceX qVar n) heqZ3_get,
      MulMod.polyValue_mulX_eq env qVar n hqd_lt hn_lt hfield_qn, h_n, h_em]
  rw [hLHS, hRHS] at h_polyeq
  rw [h_polyeq, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hem_lt]

/-- **Completeness core** (witnessed-product form). Given the honest quotient
witness `q = ⌊a²·b/n⌋` and the spec `em = (a²·b) mod n`, produce the
`NormalizeTight q` obligation (top limb `< 2^tq`) and the `GroupedEqX`
conjunction (`Assumptions` bound conjuncts + the `polyValue` equality). -/
lemma completeness_core_wm {B tb tq PB XB : ℕ} (NfL NfR : ℕ → ℕ) (hPBeq : PB = B) (hXBeq : XB = B)
    (hB : 2 ^ B < p) (htb1 : 1 ≤ tb) (htqB : tq ≤ B)
    (htbq : 2 * tb ≤ B + tq)
    (hNp : m ^ 2 * 2 ^ (3 * B) < p)
    (hf2 : (3 * m) * (3 * m) * ((2 ^ B - 1) * (2 ^ B - 1) * (2 ^ B - 1)) < p)
    (hf3 : (3 * m) * ((2 ^ B - 1) * (2 ^ B - 1)) < p)
    (hlhs_ad : ∀ k, WindowCaps.triCapW B tb m k < NfL k)
    (hrhs_ad : ∀ k, WindowCaps.qnCapW B tb tq m k + 2 ^ B ≤ NfR k)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n em : Var (BigInt m) (F p))
    (Z1 : Vector (Expression (F p)) (2 * m - 1))
    (Z2 : Vector (Expression (F p)) ((2 * m - 1) + m - 1))
    (Z3 : Vector (Expression (F p)) ((2 * m) + m - 1))
    (av bv nv emv : BigInt m (F p))
    (h_a : Vector.map (Expression.eval env) a = av)
    (h_b : Vector.map (Expression.eval env) b = bv)
    (h_n : Vector.map (Expression.eval env) n = nv)
    (h_em : Vector.map (Expression.eval env) em = emv)
    (ha_norm : av.Normalized B) (hb_norm : bv.Normalized B)
    (hn_norm : nv.Normalized B) (hem_norm : emv.Normalized B)
    (hab_ltT : av.value B < 2 ^ ((m - 1) * B + tb))
    (hbb_ltN : bv.value B < nv.value B)
    (hnb_ltT : nv.value B < 2 ^ ((m - 1) * B + tb))
    (h_spec : emv.value B = av.value B * av.value B * bv.value B % nv.value B)
    (hqwit : ∀ i : Fin (2 * m), env.get (i₀ + i.val)
      = ((av.value B * av.value B * bv.value B / nv.value B / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (heqZ1_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Z1[k.val] = Expression.eval env (bigIntMulNoReduce a a)[k.val])
    (heqZ2_get : ∀ k : Fin ((2 * m - 1) + m - 1),
      Expression.eval env Z2[k.val] = Expression.eval env (MulMod.mulNoReduceX Z1 b)[k.val])
    (heqZ3_get : ∀ k : Fin ((2 * m) + m - 1),
      Expression.eval env Z3[k.val]
        = Expression.eval env
            (MulMod.mulNoReduceX (Vector.mapRange (2 * m) fun i ↦ var { index := i₀ + i }) n)[k.val]) :
    BigInt.NormalizedTight PB tq (Vector.map (Expression.eval env)
        (Vector.mapRange (2 * m) fun i ↦ var { index := i₀ + i })) ∧
      ((∀ k : Fin (2 * m + m - 1),
          (Expression.eval env
            (if h : k.val < (2 * m - 1) + m - 1 then Z2[k.val]'h else 0)).val < NfL k.val) ∧
          ∀ k : Fin (2 * m + m - 1),
            (Expression.eval env
              (if h : k.val < (2 * m) + m - 1 then
                (if hm : k.val < m then Z3[k.val]'h + em[k.val]'hm else Z3[k.val]'h)
              else 0)).val < NfR k.val) ∧
        polyValue XB (Vector.map (Expression.eval env) (lhsPadVec Z2)) =
          polyValue XB (Vector.map (Expression.eval env) (rhsSVec Z3 em)) := by
  rw [hPBeq, hXBeq]
  have ha_top : (av[m - 1]'(by have := Nat.pos_of_neZero m; omega)).val < 2 ^ tb :=
    WindowCaps.top_lt_of_value_lt hab_ltT
  have hb_top : (bv[m - 1]'(by have := Nat.pos_of_neZero m; omega)).val < 2 ^ tb :=
    WindowCaps.top_lt_of_value_lt (lt_trans hbb_ltN hnb_ltT)
  have hn_top : (nv[m - 1]'(by have := Nat.pos_of_neZero m; omega)).val < 2 ^ tb :=
    WindowCaps.top_lt_of_value_lt hnb_ltT
  have htbB : tb ≤ B := by omega
  set qVar := (Vector.mapRange (2 * m) fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  set A := av.value B with hAdef
  set Bb := bv.value B with hBbdef
  set Nn := nv.value B with hNndef
  set qval := A * A * Bb / Nn with hqval_def
  have hm : 0 < m := Nat.pos_of_neZero m
  have hm1 : m - 1 < m := by omega
  -- honest quotient bound: q = ⌊a²b/n⌋ ≤ a²b/n < a² < 2^((2m-1)B+tq)
  have hrw2m : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
  have hexp2 : (2 * m - 1) * B = 2 * ((m - 1) * B) + B := by rw [hrw2m]; ring
  have hqval_ltT : qval < 2 ^ ((2 * m - 1) * B + tq) := by
    rw [hqval_def]
    apply Nat.div_lt_of_lt_mul
    calc A * A * Bb < 2 ^ ((2 * m - 1) * B + tq) * Nn := by
          refine Nat.mul_lt_mul_of_lt_of_le ?_ hbb_ltN.le (by omega)
          calc A * A < 2 ^ ((m - 1) * B + tb) * 2 ^ ((m - 1) * B + tb) :=
                Nat.mul_lt_mul'' hab_ltT hab_ltT
            _ = 2 ^ (2 * ((m - 1) * B + tb)) := by rw [← pow_add]; ring_nf
            _ ≤ 2 ^ ((2 * m - 1) * B + tq) := by
                apply Nat.pow_le_pow_right (by norm_num)
                rw [hexp2]; omega
      _ = Nn * 2 ^ ((2 * m - 1) * B + tq) := Nat.mul_comm _ _
  have h2m1 : 2 * m - 1 + 1 = 2 * m := by omega
  have hTle : (2 * m - 1) * B + tq ≤ B * (2 * m) := by
    calc (2 * m - 1) * B + tq ≤ (2 * m - 1) * B + B := by omega
      _ = (2 * m - 1 + 1) * B := by ring
      _ = (2 * m) * B := by rw [h2m1]
      _ = B * (2 * m) := Nat.mul_comm _ _
  have hqval_lt : qval < 2 ^ (B * (2 * m)) :=
    lt_of_lt_of_le hqval_ltT (Nat.pow_le_pow_right (by norm_num) hTle)
  have hqv_val : BigInt.value B (Vector.map (Expression.eval env) qVar) = qval :=
    BigInt.value_mapRange i₀ qval env hB hqval_lt (fun i => hqwit i)
  have hqv_norm : BigInt.Normalized B (Vector.map (Expression.eval env) qVar) :=
    MulMod.normalized_mapRange i₀ qval env hB (fun i => hqwit i)
  have hqtop : BigInt.NormalizedTight B tq (Vector.map (Expression.eval env) qVar) := by
    refine ⟨hqv_norm, ?_⟩
    have hget : (Vector.map (Expression.eval env) qVar)[2 * m - 1]'(by omega)
        = env.get (i₀ + (2 * m - 1)) := by
      simp [hqVar, circuit_norm]
    rw [hget, hqwit ⟨2 * m - 1, by omega⟩,
      ZMod.val_natCast_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) hB.le)]
    calc qval / 2 ^ (B * (2 * m - 1)) % 2 ^ B ≤ qval / 2 ^ (B * (2 * m - 1)) := Nat.mod_le _ _
      _ < 2 ^ tq := by
          apply Nat.div_lt_of_lt_mul
          rw [show (2 : ℕ) ^ (B * (2 * m - 1)) * 2 ^ tq = 2 ^ ((2 * m - 1) * B + tq) from by
            rw [← pow_add]; congr 1; ring]
          exact hqval_ltT
  -- digit bounds (identical in shape to `soundness_core_wm`)
  have ha_lt : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env a[i.val] = av[i.val] from by
      rw [← h_a]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env b[i.val] = bv[i.val] from by
      rw [← h_b]; simp only [Vector.getElem_map]]; exact hb_norm i
  have hn_lt : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env n[i.val] = nv[i.val] from by
      rw [← h_n]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hem_d : ∀ j : ℕ, (hj : j < m) → (Expression.eval env (em[j]'hj)).val < 2 ^ B := by
    intro j hj
    rw [show Expression.eval env (em[j]'hj) = emv[j]'hj from by
      rw [← h_em]; simp only [Vector.getElem_map]]
    exact hem_norm ⟨j, hj⟩
  have hqd_lt : ∀ i : Fin (2 * m), (Expression.eval env qVar[i.val]).val < 2 ^ B := by
    intro i; have := hqv_norm i; rwa [Fin.getElem_fin, Vector.getElem_map] at this
  -- field no-wrap facts
  have hfield_aa : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have hle1 : m ≤ m ^ 2 := by
      calc m = m * 1 := (Nat.mul_one m).symm
        _ ≤ m * m := Nat.mul_le_mul_left m hm
        _ = m ^ 2 := (sq m).symm
    have hle2 : (2 : ℕ) ^ (2 * B) ≤ 2 ^ (3 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : m * 2 ^ (2 * B) ≤ m ^ 2 * 2 ^ (3 * B) :=
      calc m * 2 ^ (2 * B) ≤ m ^ 2 * 2 ^ (2 * B) := Nat.mul_le_mul_right _ hle1
        _ ≤ m ^ 2 * 2 ^ (3 * B) := Nat.mul_le_mul_left _ hle2
    omega
  have hfield_qn : m * (2 ^ B * 2 ^ B) < p := hfield_aa
  have hcube_eq : m * (m * 2 ^ (2 * B) * 2 ^ B) = m ^ 2 * 2 ^ (3 * B) := by
    rw [show (3 : ℕ) * B = 2 * B + B from by ring, pow_add]; ring
  have hfield_Z1b : m * (m * 2 ^ (2 * B) * 2 ^ B) < p := by rw [hcube_eq]; exact hNp
  have haa_bound : ∀ i : Fin (2 * m - 1),
      (Expression.eval env ((bigIntMulNoReduce a a))[i.val]).val < m * 2 ^ (2 * B) :=
    fun i => val_bigIntMulNoReduce_coeff_lt env a a i ha_lt ha_lt hfield_aa
  have hZ1_bound : ∀ i : Fin (2 * m - 1), (Expression.eval env Z1[i.val]).val < m * 2 ^ (2 * B) := by
    intro i; rw [heqZ1_get i]; exact haa_bound i
  have hZ2_bound : ∀ k : Fin ((2 * m - 1) + m - 1),
      (Expression.eval env Z2[k.val]).val < m ^ 2 * 2 ^ (3 * B) := by
    intro k
    rw [heqZ2_get k, ← hcube_eq]
    exact MulMod.val_mulNoReduceX_coeff_lt env Z1 b k hZ1_bound hb_lt hfield_Z1b
  have hZ3_bound : ∀ k : Fin ((2 * m) + m - 1),
      (Expression.eval env Z3[k.val]).val < m * 2 ^ (2 * B) := by
    intro k
    rw [heqZ3_get k, show m * 2 ^ (2 * B) = m * (2 ^ B * 2 ^ B) from by rw [two_mul, pow_add]]
    exact MulMod.val_mulNoReduceX_coeff_lt env qVar n k hqd_lt hn_lt hfield_qn
  -- LHS/RHS value chains (identical to `soundness_core_wm`)
  have hLHS : polyValue B (Vector.map (Expression.eval env) (lhsPadVec Z2)) = A * A * Bb := by
    rw [polyValue_lhsPad_drop env Z2, polyValue_congr env Z2 (MulMod.mulNoReduceX Z1 b) heqZ2_get,
      polyValue_congr env (MulMod.mulNoReduceX Z1 b) (MulMod.mulNoReduceX (bigIntMulNoReduce a a) b)
        (MulMod.eval_mulNoReduceX_congr_left env Z1 (bigIntMulNoReduce a a) b heqZ1_get),
      MulMod.polyValue_mulX_eq env (bigIntMulNoReduce a a) b haa_bound hb_lt hfield_Z1b,
      value_eq_polyValue, MulMod.polyValue_mul_eq env a a ha_lt ha_lt hfield_aa, h_a, h_b]
  have hnowrap : ∀ k : Fin (2 * m + m - 1), (hk : k.val < m) →
      (Expression.eval env (Z3[k.val]'k.isLt)).val + (Expression.eval env (em[k.val]'hk)).val < p := by
    intro k hk
    have h1 := hZ3_bound k
    have h2 := hem_d k.val hk
    have h3 := rhs_bound_le_hNX (by omega : (1:ℕ) ≤ B) hm
    omega
  have hRHS : polyValue B (Vector.map (Expression.eval env) (rhsSVec Z3 em))
      = BigInt.value B (Vector.map (Expression.eval env) qVar) * Nn + emv.value B := by
    rw [polyValue_rhsS_split env Z3 em hnowrap,
      polyValue_congr env Z3 (MulMod.mulNoReduceX qVar n) heqZ3_get,
      MulMod.polyValue_mulX_eq env qVar n hqd_lt hn_lt hfield_qn, h_n, h_em]
  have hpolyeq : polyValue B (Vector.map (Expression.eval env) (lhsPadVec Z2))
      = polyValue B (Vector.map (Expression.eval env) (rhsSVec Z3 em)) := by
    rw [hLHS, hRHS, hqv_val, hqval_def, h_spec, Nat.div_add_mod']
  have ha_top' : (Expression.eval env (a[m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tb := by
    rw [show Expression.eval env (a[m - 1]'(by have := Nat.pos_of_neZero m; omega))
        = av[m - 1]'(by have := Nat.pos_of_neZero m; omega) from by
      rw [← h_a]; simp only [Vector.getElem_map]]
    exact ha_top
  have hb_top' : (Expression.eval env (b[m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tb := by
    rw [show Expression.eval env (b[m - 1]'(by have := Nat.pos_of_neZero m; omega))
        = bv[m - 1]'(by have := Nat.pos_of_neZero m; omega) from by
      rw [← h_b]; simp only [Vector.getElem_map]]
    exact hb_top
  have hn_top' : (Expression.eval env (n[m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tb := by
    rw [show Expression.eval env (n[m - 1]'(by have := Nat.pos_of_neZero m; omega))
        = nv[m - 1]'(by have := Nat.pos_of_neZero m; omega) from by
      rw [← h_n]; simp only [Vector.getElem_map]]
    exact hn_top
  have hq_top' : (Expression.eval env (qVar[2 * m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tq := by
    have h := hqtop.2
    rwa [Vector.getElem_map] at h
  have hNf_pos : ∀ j, 0 < NfL j := by
    intro j; exact lt_of_le_of_lt (Nat.zero_le _) (hlhs_ad j)
  have hlhs_bound' : ∀ k : Fin (2 * m + m - 1),
      (Expression.eval env (if h : k.val < (2 * m - 1) + m - 1 then Z2[k.val]'h else 0)).val < NfL k.val := by
    intro k
    by_cases h : k.val < (2 * m - 1) + m - 1
    · rw [dif_pos h]
      have hz2 := WindowCaps.z2_coeff_leW env a b Z1 ⟨k.val, h⟩ hm htbB heqZ1_get ha_lt hb_lt
        ha_top' hb_top' hfield_aa hf2
      have hbridge : Expression.eval env (Z2[k.val]'h)
          = Expression.eval env ((MulMod.mulNoReduceX Z1 b)[k.val]) := heqZ2_get ⟨k.val, h⟩
      rw [hbridge]
      exact lt_of_le_of_lt hz2 (hlhs_ad k.val)
    · rw [dif_neg h]
      simp only [Expression.eval, ZMod.val_zero]
      exact hNf_pos k.val
  have hrhs_bound' : ∀ k : Fin (2 * m + m - 1),
      (Expression.eval env (if h : k.val < (2 * m) + m - 1 then
        (if hm : k.val < m then Z3[k.val]'h + em[k.val]'hm else Z3[k.val]'h) else 0)).val < NfR k.val := by
    intro k
    rw [dif_pos k.isLt]
    have hz3 := WindowCaps.z3_coeff_leW env qVar n ⟨k.val, k.isLt⟩ hm htbB htqB hqd_lt hn_lt
      hq_top' hn_top' hf3
    have hbridge3 : Expression.eval env (Z3[k.val]'k.isLt)
        = Expression.eval env ((MulMod.mulNoReduceX qVar n)[k.val]) := heqZ3_get ⟨k.val, k.isLt⟩
    have hz3val : (Expression.eval env (Z3[k.val]'k.isLt)).val ≤ WindowCaps.qnCapW B tb tq m k.val := by
      rw [hbridge3]; exact hz3
    have had := hrhs_ad k.val
    by_cases hkm : k.val < m
    · rw [dif_pos hkm]
      have hval_add : (Expression.eval env (Z3[k.val]'k.isLt + em[k.val]'hkm)).val
          ≤ (Expression.eval env (Z3[k.val]'k.isLt)).val + (Expression.eval env (em[k.val]'hkm)).val := by
        rw [show Expression.eval env (Z3[k.val]'k.isLt + em[k.val]'hkm)
            = Expression.eval env (Z3[k.val]'k.isLt) + Expression.eval env (em[k.val]'hkm) from rfl]
        exact ZMod.val_add_le _ _
      have hemval : (Expression.eval env (em[k.val]'hkm)).val < 2 ^ B := hem_d k.val hkm
      omega
    · rw [dif_neg hkm]
      have h2 : 0 < 2 ^ B := Nat.two_pow_pos B
      omega
  exact ⟨hqtop, ⟨hlhs_bound', hrhs_bound'⟩, hpolyeq⟩

/-! ## The formal assertion -/

/-- The `SqMulModTo` formal assertion: `a²·b ≡ em (mod n)` with `em` canonical
(`em = (a²·b) mod n`), fusing the squared modular multiplication with the
grouped equality check. -/
def circuit (P : BigIntParams p m) (P2 : BigIntParams p (2 * m)) (XB : ℕ)
    (tb tq : ℕ) (htq : 1 ≤ tq ∧ 2 ^ tq < p) (htqB : tq ≤ P2.B)
    (htb1 : 1 ≤ tb) (htbq : 2 * tb ≤ P.B + tq) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams) (hgvx : GroupedEqXV.GVXHyps p (2 * m + m - 1) XB gf posOf G V VR) (hXB1 : 1 ≤ XB)
    (hNp : m ^ 2 * 2 ^ (3 * P.B) < p)
    (hf2 : (3 * m) * (3 * m) * ((2 ^ P.B - 1) * (2 ^ P.B - 1) * (2 ^ P.B - 1)) < p)
    (hf3 : (3 * m) * ((2 ^ P.B - 1) * (2 ^ P.B - 1)) < p)
    (hlhs_ad : ∀ k, WindowCaps.triCapW P.B tb m k < V.Nf k)
    (hrhs_ad : ∀ k, WindowCaps.qnCapW P.B tb tq m k + 2 ^ P.B ≤ VR.Nf k)
    (hB2 : P2.B = P.B) (hXB : XB = P.B) [Fact (p > 2)] :
    FormalAssertion (F p) (InputsTo m) where
  main := main P P2 XB tq htq htqB gf posOf G V VR hgvx hXB1 hB2 hXB
  Assumptions := Assumptions P.B tb
  Spec := Spec P.B
  soundness := by
    obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
    circuit_proof_start [NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      NormalizeTight.Assumptions, NormalizeTight.Spec,
      GroupedEqXV.circuit_assumptions_eq, GroupedEqXV.circuit_spec_eq,
      GroupedEqXV.Assumptions, GroupedEqX.Spec]
    obtain ⟨ha_norm, hb_norm, hn_norm, hem_norm, hab_ltT, hbb_ltN, hem_lt, hnb_ltT⟩ := h_assumptions
    obtain ⟨hq_tight, hZ1_ops, hZ2_ops, hZ3_ops, h_eq_impl⟩ := h_holds
    have hm : 0 < m := Nat.pos_of_neZero m
    have htqB' : tq ≤ B := by have h := htqB; rw [hB2] at h; exact h
    have htbB : tb ≤ B := by omega
    have ha_top : (input.a[m - 1]'(by omega)).val < 2 ^ tb :=
      WindowCaps.top_lt_of_value_lt hab_ltT
    have hb_top : (input.b[m - 1]'(by omega)).val < 2 ^ tb :=
      WindowCaps.top_lt_of_value_lt (lt_trans hbb_ltN hnb_ltT)
    have hn_top : (input.modulus[m - 1]'(by omega)).val < 2 ^ tb :=
      WindowCaps.top_lt_of_value_lt hnb_ltT
    have h3m : 3 * m - 1 < p := three_m_sub_one_lt hp
    have hpm1 : 2 * m - 1 < p := by omega
    have hpm2 : (2 * m - 1) + m - 1 < p := by omega
    have hpm3 : (2 * m) + m - 1 < p := by omega
    have h_pZ1 := MulMod.interpolatedMul_soundness (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1))) input_var.a input_var.a env hZ1_ops
    have h_pZ2 := MulMod.interpolatedMulX_soundness (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2)
      (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).1 input_var.b env hZ2_ops
    have h_pZ3 := MulMod.interpolatedMulX_soundness (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2 + Operations.localLength (MulMod.interpolatedMulX (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).1 input_var.b (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2)).2)
      (Vector.mapRange (2 * m) fun i => var { index := i₀ + i }) input_var.modulus env hZ3_ops
    refine ⟨?_, MulMod.interpolatedMul_requirements _ _ _ _, MulMod.interpolatedMulX_requirements _ _ _ _,
      MulMod.interpolatedMulX_requirements _ _ _ _, Or.inl (GroupedEqXV.circuit_channels_req_eq _ _ _ _ _ _ _ _)⟩
    have h_a : Vector.map (Expression.eval env) input_var.a = input.a := by simp only [← h_input]
    have h_b : Vector.map (Expression.eval env) input_var.b = input.b := by simp only [← h_input]
    have h_n : Vector.map (Expression.eval env) input_var.modulus = input.modulus := by
      simp only [← h_input]
    have h_em : Vector.map (Expression.eval env) input_var.em = input.em := by simp only [← h_input]
    have hq_norm' : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange (2 * m) fun i => var { index := i₀ + i })) := by
      have h := hq_tight.1; rw [hB2] at h; exact h
    have heqZ1_get := MulMod.interpolatedMul_eval_bridge env (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1))) input_var.a input_var.a hpm1 h_pZ1
    have heqZ2_get := MulMod.interpolatedMulX_eval_bridge env (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2)
      (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).1 input_var.b hpm2 h_pZ2
    have heqZ3_get := MulMod.interpolatedMulX_eval_bridge env (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2 + Operations.localLength (MulMod.interpolatedMulX (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).1 input_var.b (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2)).2)
      (Vector.mapRange (2 * m) fun i => var { index := i₀ + i }) input_var.modulus hpm3 h_pZ3
    exact soundness_core_wm (B := B) V.Nf VR.Nf (XB := XB) hXB hB1 hm htbB htqB' hNp hf2 hf3 hlhs_ad hrhs_ad i₀ env
      input_var.a input_var.b input_var.modulus input_var.em
      (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).1
      (MulMod.interpolatedMulX (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).1 input_var.b (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2)).1
      (MulMod.interpolatedMulX (Vector.mapRange (2 * m) fun i => var { index := i₀ + i })
        input_var.modulus (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2 + Operations.localLength (MulMod.interpolatedMulX (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).1 input_var.b (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2)).2)).1
      input.a input.b input.modulus input.em h_a h_b h_n h_em
      ha_norm hb_norm hn_norm hem_norm hem_lt hq_norm' ha_top hb_top hn_top hq_tight.2
      heqZ1_get heqZ2_get heqZ3_get h_eq_impl
  completeness := by
    obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
    circuit_proof_start [NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      NormalizeTight.Assumptions, NormalizeTight.Spec,
      GroupedEqXV.circuit_assumptions_eq, GroupedEqXV.circuit_spec_eq,
      GroupedEqXV.Assumptions, GroupedEqX.Spec]
    obtain ⟨ha_norm, hb_norm, hn_norm, hem_norm, hab_ltT, hbb_ltN, hem_lt, hnb_ltT⟩ := h_assumptions
    obtain ⟨hq_env, hZ1_uses, hZ2_uses, hZ3_uses⟩ := h_env
    have hm : 0 < m := Nat.pos_of_neZero m
    have htqB' : tq ≤ B := by have h := htqB; rw [hB2] at h; exact h
    have h_pvZ1 := MulMod.interpolatedMul_usesLocalWitnesses (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1))) (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))
      input_var.a input_var.a env rfl hZ1_uses
    have h_pvZ2 := MulMod.interpolatedMulX_usesLocalWitnesses (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2)
      (Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2 + (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1))))
      (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).1 input_var.b env (by ring) hZ2_uses
    have h_pvZ3 := MulMod.interpolatedMulX_usesLocalWitnesses (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2 + Operations.localLength (MulMod.interpolatedMulX (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).1 input_var.b (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2)).2)
      (Operations.localLength (MulMod.interpolatedMulX
          (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).1 input_var.b (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2)).2 +
        (Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2 + (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))))
      (Vector.mapRange (2 * m) fun i => var { index := i₀ + i }) input_var.modulus env (by ring) hZ3_uses
    have heva : MulMod.evalValue B env input_var.a = BigInt.value B input.a := by
      rw [MulMod.evalValue, BigInt.value, ← h_input]
    have hevb : MulMod.evalValue B env input_var.b = BigInt.value B input.b := by
      rw [MulMod.evalValue, BigInt.value, ← h_input]
    have hevn : MulMod.evalValue B env input_var.modulus = BigInt.value B input.modulus := by
      rw [MulMod.evalValue, BigInt.value, ← h_input]
    have hqwit : ∀ i : Fin (2 * m), env.toEnvironment.get (i₀ + i.val)
        = ((BigInt.value B input.a * BigInt.value B input.a * BigInt.value B input.b
            / BigInt.value B input.modulus / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
      intro i; rw [hq_env i, Vector.getElem_ofFn, heva, hevb, hevn]
    have h_a : Vector.map (Expression.eval env.toEnvironment) input_var.a = input.a := by
      simp only [← h_input]
    have h_b : Vector.map (Expression.eval env.toEnvironment) input_var.b = input.b := by
      simp only [← h_input]
    have h_n : Vector.map (Expression.eval env.toEnvironment) input_var.modulus = input.modulus := by
      simp only [← h_input]
    have h_em : Vector.map (Expression.eval env.toEnvironment) input_var.em = input.em := by
      simp only [← h_input]
    have heqZ1_get := MulMod.interpolatedMul_eval_bridge_uses env.toEnvironment (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))
      input_var.a input_var.a h_pvZ1
    have heqZ2_get := MulMod.interpolatedMulX_eval_bridge_uses env.toEnvironment (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2)
      (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).1 input_var.b h_pvZ2
    have heqZ3_get := MulMod.interpolatedMulX_eval_bridge_uses env.toEnvironment (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2 + Operations.localLength (MulMod.interpolatedMulX (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).1 input_var.b (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2)).2)
      (Vector.mapRange (2 * m) fun i => var { index := i₀ + i }) input_var.modulus h_pvZ3
    have core := completeness_core_wm (B := B) (tb := tb) (tq := tq) V.Nf VR.Nf
      (PB := P2.B) (XB := XB) hB2 hXB
      hB htb1 htqB' htbq hNp hf2 hf3 hlhs_ad hrhs_ad i₀
      env.toEnvironment input_var.a input_var.b input_var.modulus input_var.em
      (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).1
      (MulMod.interpolatedMulX (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).1 input_var.b (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2)).1
      (MulMod.interpolatedMulX (Vector.mapRange (2 * m) fun i => var { index := i₀ + i })
        input_var.modulus (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2 + Operations.localLength (MulMod.interpolatedMulX (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).1 input_var.b (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2)).2)).1
      input.a input.b input.modulus input.em h_a h_b h_n h_em
      ha_norm hb_norm hn_norm hem_norm hab_ltT hbb_ltN hnb_ltT h_spec hqwit heqZ1_get heqZ2_get heqZ3_get
    refine ⟨core.1,
      MulMod.interpolatedMul_completeness (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1))) input_var.a input_var.a env h_pvZ1,
      MulMod.interpolatedMulX_completeness (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2) (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).1
        input_var.b env h_pvZ2,
      MulMod.interpolatedMulX_completeness (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2 + Operations.localLength (MulMod.interpolatedMulX (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).1 input_var.b (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) + Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)))).2)).2) (Vector.mapRange (2 * m) fun i => var { index := i₀ + i })
        input_var.modulus env h_pvZ3,
      core.2⟩

end SqMulModTo

end

/-! ## Cost / R1CS certificates -/

namespace GadgetCost

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Challenge.CostR1CS
open Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostInfra

variable {m : ℕ}

/-- Per-gadget `Count` of the `SqMulModTo` assertion: witness `q` (`2m`),
`NormalizeTight q` at top-limb `tq`, the three interpolation blocks
(`interpolatedMul a a`, `interpolatedMulX z1 b`, `interpolatedMulX q n`), and the
`GroupedEqX` grouped equality at group size `g`. -/
def sqMulModToCount (B tq G : ℕ) (Wf : ℕ → ℕ) : Count :=
  ⟨2 * m, 0⟩ + ((⟨(2 * m - 1) * (B - 1), (2 * m - 1) * B⟩ + ⟨tq - 1, tq⟩) +
    (⟨2 * m - 1, 2 * m - 1⟩ +
      (⟨(2 * m - 1) + m - 1, (2 * m - 1) + m - 1⟩ +
        (⟨(2 * m) + m - 1, (2 * m) + m - 1⟩ +
          ⟨GroupedEqXV.widthAllocFrom Wf (G - 2) 0,
            GroupedEqXV.widthConsFrom Wf (G - 2) 0 + 1⟩))))

theorem costIs_sqMulModTo (P : BigIntParams circomPrime m) (P2 : BigIntParams circomPrime (2 * m))
    (XB : ℕ) (tq : ℕ)
    (htq : 1 ≤ tq ∧ (2 : ℕ) ^ tq < circomPrime) (htqB : tq ≤ P2.B) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams) (hgvx : GroupedEqXV.GVXHyps circomPrime (2 * m + m - 1) XB gf posOf G V VR)
    (hXB1 : 1 ≤ XB)
    (hB2 : P2.B = P.B) (hXB : XB = P.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (MulModTo.InputsTo m) (F circomPrime)) :
    CostIs (SqMulModTo.main P P2 XB tq htq htqB gf posOf G V VR hgvx hXB1 hB2 hXB input)
      (sqMulModToCount (m := m) P.B tq G V.Wf) := by
  have hm : 0 < m := Nat.pos_of_neZero m
  rw [show sqMulModToCount (m := m) P.B tq G V.Wf = sqMulModToCount (m := m) P2.B tq G V.Wf from by
    rw [hB2]]
  unfold SqMulModTo.main sqMulModToCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (costIs_assertion_normalizeTight P2 tq htq htqB _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun z1 => ?_
  refine CostIs.bind (costIs_interpolatedMulX _ _) fun z2 => ?_
  refine CostIs.bind (costIs_interpolatedMulX _ _) fun z3 => ?_
  exact costIs_assertion_groupedEqXV XB gf posOf G V VR hgvx hXB1 _

theorem costIs_assertion_sqMulModTo (P : BigIntParams circomPrime m) (P2 : BigIntParams circomPrime (2 * m))
    (XB : ℕ) (tb tq : ℕ)
    (htq : 1 ≤ tq ∧ (2 : ℕ) ^ tq < circomPrime) (htqB : tq ≤ P2.B)
    (htb1 : 1 ≤ tb) (htbq : 2 * tb ≤ P.B + tq) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams) (hgvx : GroupedEqXV.GVXHyps circomPrime (2 * m + m - 1) XB gf posOf G V VR)
    (hXB1 : 1 ≤ XB) (hNp : m ^ 2 * 2 ^ (3 * P.B) < circomPrime)
    (hf2 : (3 * m) * (3 * m) * ((2 ^ P.B - 1) * (2 ^ P.B - 1) * (2 ^ P.B - 1)) < circomPrime)
    (hf3 : (3 * m) * ((2 ^ P.B - 1) * (2 ^ P.B - 1)) < circomPrime)
    (hlhs_ad : ∀ k, WindowCaps.triCapW P.B tb m k < V.Nf k)
    (hrhs_ad : ∀ k, WindowCaps.qnCapW P.B tb tq m k + 2 ^ P.B ≤ VR.Nf k)
    (hB2 : P2.B = P.B) (hXB : XB = P.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulModTo.InputsTo m) (F circomPrime)) :
    CostIs (assertion (SqMulModTo.circuit P P2 XB tb tq htq htqB htb1 htbq gf posOf G V VR hgvx hXB1 hNp hf2 hf3 hlhs_ad hrhs_ad hB2 hXB) b)
      (sqMulModToCount (m := m) P.B tq G V.Wf) :=
  CostIs.assertion (fun n => costIs_sqMulModTo P P2 XB tq htq htqB gf posOf G V VR hgvx hXB1 hB2 hXB b n)

theorem isR1CS_sqMulModTo (P : BigIntParams circomPrime m) (P2 : BigIntParams circomPrime (2 * m))
    (XB : ℕ) (tq : ℕ)
    (htq : 1 ≤ tq ∧ (2 : ℕ) ^ tq < circomPrime) (htqB : tq ≤ P2.B) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams) (hgvx : GroupedEqXV.GVXHyps circomPrime (2 * m + m - 1) XB gf posOf G V VR)
    (hXB1 : 1 ≤ XB)
    (hB2 : P2.B = P.B) (hXB : XB = P.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (MulModTo.InputsTo m) (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hn : AffineW input.modulus)
    (hem : AffineW input.em) :
    IsR1CSCirc (SqMulModTo.main P P2 XB tq htq htqB gf posOf G V VR hgvx hXB1 hB2 hXB input) := by
  have hm : 0 < m := Nat.pos_of_neZero m
  unfold SqMulModTo.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalizeTight P2 tq htq htqB _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha ha) fun nz1 => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_interpolatedMulX _ _ (affineW_interpolatedMul_output _ _ _) hb) fun nz2 => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_interpolatedMulX _ _ (affineW_provableWitness_bigInt _ nq) hn) fun nz3 => ?_
  refine isR1CS_assertion_groupedEqXV XB gf posOf G V VR hgvx hXB1 _ ?_ ?_
  · intro i hi
    rw [Vector.getElem_mapFinRange]
    split
    · exact affineW_interpolatedMulX_output _ _ _ i (by assumption)
    · exact (Affine.zero : Affine (0 : Expression (F circomPrime)))
  · intro i hi
    rw [Vector.getElem_mapFinRange, dif_pos (show i < (2 * m) + m - 1 from hi)]
    split
    · exact Affine.add (affineW_interpolatedMulX_output _ _ _ i hi)
        (hem i (by assumption))
    · exact affineW_interpolatedMulX_output _ _ _ i hi

theorem isR1CS_assertion_sqMulModTo (P : BigIntParams circomPrime m) (P2 : BigIntParams circomPrime (2 * m))
    (XB : ℕ) (tb tq : ℕ)
    (htq : 1 ≤ tq ∧ (2 : ℕ) ^ tq < circomPrime) (htqB : tq ≤ P2.B)
    (htb1 : 1 ≤ tb) (htbq : 2 * tb ≤ P.B + tq) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams) (hgvx : GroupedEqXV.GVXHyps circomPrime (2 * m + m - 1) XB gf posOf G V VR)
    (hXB1 : 1 ≤ XB) (hNp : m ^ 2 * 2 ^ (3 * P.B) < circomPrime)
    (hf2 : (3 * m) * (3 * m) * ((2 ^ P.B - 1) * (2 ^ P.B - 1) * (2 ^ P.B - 1)) < circomPrime)
    (hf3 : (3 * m) * ((2 ^ P.B - 1) * (2 ^ P.B - 1)) < circomPrime)
    (hlhs_ad : ∀ k, WindowCaps.triCapW P.B tb m k < V.Nf k)
    (hrhs_ad : ∀ k, WindowCaps.qnCapW P.B tb tq m k + 2 ^ P.B ≤ VR.Nf k)
    (hB2 : P2.B = P.B) (hXB : XB = P.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulModTo.InputsTo m) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus) (hem : AffineW b.em) :
    IsR1CSCirc (assertion (SqMulModTo.circuit P P2 XB tb tq htq htqB htb1 htbq gf posOf G V VR hgvx hXB1 hNp hf2 hf3 hlhs_ad hrhs_ad hB2 hXB) b) :=
  IsR1CSCirc.assertion (fun n => isR1CS_sqMulModTo P P2 XB tq htq htqB gf posOf G V VR hgvx hXB1 hB2 hXB b ha hb hn hem n)

end GadgetCost

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
