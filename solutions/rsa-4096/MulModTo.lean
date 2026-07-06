import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulMod
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.NormalizeTight

/-!
# RSA fused modular-multiplication equality (gadget "MulModTo")

`MulModTo` is a `FormalAssertion` fusing the final `MulModLazy` and `EqMod` of the
RSA pipeline into a single gadget: given operands `a`, `b`, the `modulus` `n`, and
an *affine* target `em` (the PKCS#1-v1_5 encoded message, whose limbs are linear
forms over the digest bits), it asserts

    a · b = q · n + em          (as natural numbers)

with a witnessed quotient `q` (tight-normalized: top limb `< 2^tq`). Under the
assumption `em < n` this pins `em = (a·b) mod n` — the canonical residue — without
ever witnessing the remainder: `em`'s limbs sit on the affine right-hand side of the
`EqViaCarries` chain exactly where the remainder's witnessed limbs sit in
`MulModLazy`. This saves the `m` remainder cells, its `NormalizeTight`, and the
whole separate `EqMod` gadget.

The quotient is range-checked with `NormalizeTight` at top-limb width `tq = tb + 1`:
with `a, b < 2^((m-1)B + tb)` and `n ≥ 2^((m-1)B + tb - 1)` the honest quotient is
`< 2^((m-1)B + tb + 1)`.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace MulModTo

open MulMod (Inputs interpolatedMul interpolatedMul_output interpolatedMul_localLength
  interpolatedMul_soundness interpolatedMul_eval_bridge interpolatedMul_eval_bridge_uses
  interpolatedMul_requirements interpolatedMul_usesLocalWitnesses interpolatedMul_completeness
  two_m_sub_one_lt polyValue_mul_eq polyValue_Sqn_eq coeff_P_bound)

/-- Inputs of `MulModTo`: the two operands `a`, `b`, the `modulus`, and the affine
target `em` that `a·b` must reduce to modulo `n`. -/
structure InputsTo (m : ℕ) (F : Type) where
  a : BigInt m F
  b : BigInt m F
  modulus : BigInt m F
  em : BigInt m F
deriving ProvableStruct

/-- The `main` circuit of `MulModTo`: witness `q = (a·b)/n`, tight-normalize it
(top limb `< 2^tq`), build the two convolution coefficient vectors by
interpolation multiplication, and assert `a·b = q·n + em` in base `2^B` via
`EqViaCarries` (with `em`'s limbs added on the affine right-hand side). -/
def main (P : BigIntParams p m) (tq : ℕ) (htq : 1 ≤ tq ∧ 2 ^ tq < p) (htqB : tq ≤ P.B)
    [Fact (p > 2)] (input : Var (InputsTo m) (F p)) :
    Circuit (F p) Unit := do
  let a := input.a
  let b := input.b
  let n := input.modulus
  let em := input.em

  let q ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := MulMod.evalValue P.B env a * MulMod.evalValue P.B env b
    let qval : ℕ := prod / MulMod.evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  NormalizeTight.circuit P tq htq htqB q

  let Pc ← interpolatedMul a b
  let Sqn ← interpolatedMul q n
  let S : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then Sqn[k.val] + em[k.val]'h else Sqn[k.val]

  EqViaCarries.circuit P { lhs := Pc, rhs := S }

instance elaborated (P : BigIntParams p m) (tq : ℕ) (htq : 1 ≤ tq ∧ 2 ^ tq < p) (htqB : tq ≤ P.B)
    [Fact (p > 2)] :
    ElaboratedCircuit (F p) (InputsTo m) unit (main P tq htq htqB) where
  localLength _ :=
    m + ((m - 1) * (P.B - 1) + (tq - 1)) + (2 * m - 1) + (2 * m - 1)
      + ((2 * m - 1 - 1) * (P.W - 1) + (2 * m - 1 - 1))
  localLength_eq := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm,
      NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main, RangeCheck.circuit]
    omega
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, interpolatedMul, circuit_norm,
      NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main, RangeCheck.circuit]
  channelsLawful := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm,
      NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main, RangeCheck.circuit]

/-- Preconditions: all four operands normalized; `a`, `b` tight
(`< 2^((m-1)B + tb)`); `em < n` (so `em` is the canonical residue); and the
modulus lower bound `2^((m-1)B + tb - 1) ≤ n` (so the honest quotient fits with
top limb `< 2^(tb+1) ≤ 2^tq`). -/
def Assumptions (B tb : ℕ) (input : InputsTo m (F p)) : Prop :=
  input.a.Normalized B ∧ input.b.Normalized B ∧ input.modulus.Normalized B ∧
    input.em.Normalized B ∧
    input.a.value B < 2 ^ ((m - 1) * B + tb) ∧ input.b.value B < 2 ^ ((m - 1) * B + tb) ∧
    input.b.value B < input.modulus.value B ∧
    input.em.value B < input.modulus.value B

/-- Postcondition: `em` is exactly the canonical residue of `a·b` mod `n`. -/
def Spec (B : ℕ) (input : InputsTo m (F p)) : Prop :=
  input.em.value B = input.a.value B * input.b.value B % input.modulus.value B

/-! ## Support lemmas: the `S = q·n + em` coefficient vector -/

/-- The `S` coefficient vector of `MulModTo` (schoolbook form): `(q·n)[k] + em[k]`
in the low `m` limbs, `(q·n)[k]` above. -/
def sVecEm (q n em : Var (BigInt m) (F p)) : Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then (bigIntMulNoReduce q n)[k.val] + em[k.val]'h
    else (bigIntMulNoReduce q n)[k.val]

/-- Splitting `S = Sqn + em` (low limbs): `polyValue S = polyValue Sqn + em.value`,
provided each low coefficient does not wrap mod `p`. -/
lemma polyValue_sVecEm_split {B : ℕ} (env : Environment (F p))
    (q n em : Var (BigInt m) (F p))
    (hnowrap : ∀ k : Fin (2 * m - 1), (hk : k.val < m) →
      (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
        + (Expression.eval env (em[k.val]'hk)).val < p) :
    polyValue B (Vector.map (Expression.eval env) (sVecEm q n em))
      = polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce q n))
        + BigInt.value B (Vector.map (Expression.eval env) em) := by
  rw [polyValue, polyValue, MulMod.value_map_eval]
  -- per-index value of S
  have hS : ∀ k : Fin (2 * m - 1),
      ((Vector.map (Expression.eval env) (sVecEm q n em))[k.val]).val
        = (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
          + (if h : k.val < m then (Expression.eval env (em[k.val]'h)).val else 0) := by
    intro k
    rw [Vector.getElem_map]
    simp only [sVecEm, Vector.getElem_mapFinRange]
    by_cases hk : k.val < m
    · simp only [dif_pos hk]
      rw [show Expression.eval env ((bigIntMulNoReduce q n)[k.val] + em[k.val]'hk)
            = Expression.eval env ((bigIntMulNoReduce q n)[k.val])
              + Expression.eval env (em[k.val]'hk) from rfl,
        ZMod.val_add_of_lt (hnowrap k hk)]
    · simp only [dif_neg hk, Nat.add_zero]
  simp only [hS]
  rw [show (∑ k : Fin (2 * m - 1),
        ((Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
          + (if h : k.val < m then (Expression.eval env (em[k.val]'h)).val else 0))
          * 2 ^ (B * k.val))
      = (∑ k : Fin (2 * m - 1),
          (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val * 2 ^ (B * k.val))
        + (∑ k : Fin (2 * m - 1),
          (if h : k.val < m then (Expression.eval env (em[k.val]'h)).val else 0)
            * 2 ^ (B * k.val)) from by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; ring]
  congr 1
  · apply Finset.sum_congr rfl; intro k _; rw [Vector.getElem_map]
  · -- em part: guarded `Fin (2m-1)` sum collapses to the `Fin m` value sum
    have hm : 0 < m := Nat.pos_of_neZero m
    -- total ℕ-indexed digit function
    have hLHS : (∑ k : Fin (2 * m - 1),
          (if h : k.val < m then (Expression.eval env (em[k.val]'h)).val else 0) * 2 ^ (B * k.val))
        = ∑ k ∈ Finset.range (2 * m - 1),
          (if h : k < m then (Expression.eval env (em[k]'h)).val else 0) * 2 ^ (B * k) := by
      rw [← Fin.sum_univ_eq_sum_range (fun k =>
        (if h : k < m then (Expression.eval env (em[k]'h)).val else 0) * 2 ^ (B * k))]
    rw [hLHS]
    have hsub : Finset.range m ⊆ Finset.range (2 * m - 1) := by
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

/-- Coefficient bound for `S = sVecEm q n em`: each coefficient is
`< (m+1)·2^(2B)`, the size assumption required by `EqViaCarries`. -/
lemma coeff_SEm_bound {B : ℕ} (env : Environment (F p))
    (q n em : Var (BigInt m) (F p)) (k : Fin (2 * m - 1))
    (hq : ∀ i : Fin m, (Expression.eval env q[i.val]).val < 2 ^ B)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B)
    (hem : ∀ j : ℕ, (hj : j < m) → (Expression.eval env (em[j]'hj)).val < 2 ^ B)
    (hfield : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((sVecEm q n em)[k.val])).val < (m + 1) * 2 ^ (2 * B) := by
  have hSqn := val_bigIntMulNoReduce_coeff_lt env q n k hq hn hfield
  have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmm : (m + 1) * 2 ^ (2 * B) = m * 2 ^ (2 * B) + 2 ^ (2 * B) := by ring
  rw [hmm]
  generalize hX : 2 ^ (2 * B) = X at *
  generalize hY : m * X = Y at *
  simp only [sVecEm, Vector.getElem_mapFinRange]
  by_cases hk : k.val < m
  · rw [dif_pos hk]
    have hem' := hem k.val hk
    have hadd : (Expression.eval env ((bigIntMulNoReduce q n)[k.val])
        + Expression.eval env (em[k.val]'hk)).val
        ≤ (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
          + (Expression.eval env (em[k.val]'hk)).val := ZMod.val_add_le _ _
    rw [show Expression.eval env ((bigIntMulNoReduce q n)[k.val] + em[k.val]'hk)
          = Expression.eval env ((bigIntMulNoReduce q n)[k.val])
            + Expression.eval env (em[k.val]'hk) from rfl]
    omega
  · rw [dif_neg hk]
    omega

omit [NeZero m] in
/-- `EqViaCarries` implication bridge with an affine `em` tail: if `Pv`/`Pn` and
`Qv`/`Qn` evaluate identically, the implication phrased with the witnessed vectors
transfers to the schoolbook one. Mirror of `MulMod.eqImpl_bridge` with `em[k]`
replacing the remainder cells. -/
lemma eqImpl_bridge_em {B : ℕ} (env : Environment (F p))
    (em : Var (BigInt m) (F p))
    (Pv Pn Qv Qn : Vector (Expression (F p)) (2 * m - 1))
    (hP_get : ∀ k : Fin (2 * m - 1), Expression.eval env Pv[k.val] = Expression.eval env Pn[k.val])
    (hQ_get : ∀ k : Fin (2 * m - 1), Expression.eval env Qv[k.val] = Expression.eval env Qn[k.val])
    (himpl :
      ((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env (if h : k.val < m then Qv[k.val] + em[k.val]'h
            else Qv[k.val])).val < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) Pv) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k =>
              if h : k.val < m then Qv[k.val] + em[k.val]'h else Qv[k.val]))) :
    ((∀ k : Fin (2 * m - 1), (Expression.eval env Pn[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
      ∀ k : Fin (2 * m - 1),
        (Expression.eval env (if h : k.val < m then Qn[k.val] + em[k.val]'h
          else Qn[k.val])).val < (m + 1) * 2 ^ (2 * B)) →
      polyValue B (Vector.map (Expression.eval env) Pn) =
        polyValue B (Vector.map (Expression.eval env)
          (Vector.mapFinRange (2 * m - 1) fun k =>
            if h : k.val < m then Qn[k.val] + em[k.val]'h else Qn[k.val])) := by
  have hS_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env (if h : k.val < m then Qv[k.val] + em[k.val]'h else Qv[k.val])
        = Expression.eval env (if h : k.val < m then Qn[k.val] + em[k.val]'h else Qn[k.val]) := by
    intro k
    by_cases hk : k.val < m
    · simp only [dif_pos hk]
      show Expression.eval env Qv[k.val] + Expression.eval env (em[k.val]'hk)
        = Expression.eval env Qn[k.val] + Expression.eval env (em[k.val]'hk)
      rw [hQ_get k]
    · simp only [dif_neg hk]; exact hQ_get k
  have hSvec : Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * m - 1) fun k =>
          if h : k.val < m then Qv[k.val] + em[k.val]'h else Qv[k.val])
      = Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * m - 1) fun k =>
          if h : k.val < m then Qn[k.val] + em[k.val]'h else Qn[k.val]) := by
    apply Vector.ext; intro k hk
    rw [Vector.getElem_map, Vector.getElem_map, Vector.getElem_mapFinRange, Vector.getElem_mapFinRange]
    exact hS_get ⟨k, hk⟩
  have hPvec : Vector.map (Expression.eval env) Pv = Vector.map (Expression.eval env) Pn := by
    apply Vector.ext; intro k hk; rw [Vector.getElem_map, Vector.getElem_map]; exact hP_get ⟨k, hk⟩
  intro hbounds
  rw [← hPvec, ← hSvec]
  apply himpl
  refine ⟨fun k => ?_, fun k => ?_⟩
  · rw [hP_get k]; exact hbounds.1 k
  · rw [hS_get k]; exact hbounds.2 k

omit [NeZero m] in
/-- `EqViaCarries` conjunction bridge with an affine `em` tail (completeness
direction). Mirror of `MulMod.eqConj_bridge`. -/
lemma eqConj_bridge_em {B : ℕ} (env : Environment (F p))
    (em : Var (BigInt m) (F p))
    (Pv Pn Qv Qn : Vector (Expression (F p)) (2 * m - 1))
    (hP_get : ∀ k : Fin (2 * m - 1), Expression.eval env Pv[k.val] = Expression.eval env Pn[k.val])
    (hQ_get : ∀ k : Fin (2 * m - 1), Expression.eval env Qv[k.val] = Expression.eval env Qn[k.val])
    (hconj :
      ((∀ k : Fin (2 * m - 1), (Expression.eval env Pn[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
        (∀ k : Fin (2 * m - 1),
          (Expression.eval env (if h : k.val < m then Qn[k.val] + em[k.val]'h
            else Qn[k.val])).val < (m + 1) * 2 ^ (2 * B))) ∧
        polyValue B (Vector.map (Expression.eval env) Pn) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k =>
              if h : k.val < m then Qn[k.val] + em[k.val]'h else Qn[k.val]))) :
    ((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
      (∀ k : Fin (2 * m - 1),
        (Expression.eval env (if h : k.val < m then Qv[k.val] + em[k.val]'h
          else Qv[k.val])).val < (m + 1) * 2 ^ (2 * B))) ∧
        polyValue B (Vector.map (Expression.eval env) Pv) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k =>
              if h : k.val < m then Qv[k.val] + em[k.val]'h else Qv[k.val])) := by
  have hS_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env (if h : k.val < m then Qv[k.val] + em[k.val]'h else Qv[k.val])
        = Expression.eval env (if h : k.val < m then Qn[k.val] + em[k.val]'h else Qn[k.val]) := by
    intro k
    by_cases hk : k.val < m
    · simp only [dif_pos hk]
      show Expression.eval env Qv[k.val] + Expression.eval env (em[k.val]'hk)
        = Expression.eval env Qn[k.val] + Expression.eval env (em[k.val]'hk)
      rw [hQ_get k]
    · simp only [dif_neg hk]; exact hQ_get k
  have hPvec : Vector.map (Expression.eval env) Pv = Vector.map (Expression.eval env) Pn := by
    apply Vector.ext; intro k hk; rw [Vector.getElem_map, Vector.getElem_map]; exact hP_get ⟨k, hk⟩
  have hSvec : Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * m - 1) fun k =>
          if h : k.val < m then Qv[k.val] + em[k.val]'h else Qv[k.val])
      = Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * m - 1) fun k =>
          if h : k.val < m then Qn[k.val] + em[k.val]'h else Qn[k.val]) := by
    apply Vector.ext; intro k hk
    rw [Vector.getElem_map, Vector.getElem_map, Vector.getElem_mapFinRange, Vector.getElem_mapFinRange]
    exact hS_get ⟨k, hk⟩
  refine ⟨⟨fun k => ?_, fun k => ?_⟩, ?_⟩
  · rw [hP_get k]; exact hconj.1.1 k
  · rw [hS_get k]; exact hconj.1.2 k
  · rw [hPvec, hSvec]; exact hconj.2

/-! ## Arithmetic cores -/

/-- **Soundness core** (schoolbook form). From the `EqViaCarries` implication over
the schoolbook convolutions we get `a·b = q·n + em` over ℕ, hence
`em = (a·b) mod n` (using `em < n`). -/
lemma soundness_core {B : ℕ} (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n em : Var (BigInt m) (F p))
    (av bv nv emv : BigInt m (F p))
    (h_a : Vector.map (Expression.eval env) a = av)
    (h_b : Vector.map (Expression.eval env) b = bv)
    (h_n : Vector.map (Expression.eval env) n = nv)
    (h_em : Vector.map (Expression.eval env) em = emv)
    (ha_norm : av.Normalized B) (hb_norm : bv.Normalized B)
    (hn_norm : nv.Normalized B) (hem_norm : emv.Normalized B)
    (hem_lt : emv.value B < nv.value B)
    (hq_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })))
    (h_eq_impl :
      ((∀ k : Fin (2 * m - 1),
          (Expression.eval env (bigIntMulNoReduce a b)[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env
            (if h : k.val < m then
              (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]
                + em[k.val]'h
            else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])).val
            < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b)) =
          polyValue B
            (Vector.map (Expression.eval env)
              (Vector.mapFinRange (2 * m - 1) fun k ↦
                if h : k.val < m then
                  (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]
                    + em[k.val]'h
                else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]))) :
    emv.value B = av.value B * bv.value B % nv.value B := by
  set qVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  -- digit bounds
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
  have hqd_lt : ∀ i : Fin m, (Expression.eval env qVar[i.val]).val < 2 ^ B := by
    intro i; have := hq_norm i; rwa [Fin.getElem_fin, Vector.getElem_map] at this
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
    omega
  have hS_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce qVar n)[k.val] + em[k.val]'h
        else (bigIntMulNoReduce qVar n)[k.val])
      = sVecEm qVar n em := rfl
  -- discharge the EqViaCarries bounds
  have h_polyeq := h_eq_impl ⟨fun k => coeff_P_bound env a b k ha_lt hb_lt hfield,
    fun k => by
      have hb := coeff_SEm_bound env qVar n em k hqd_lt hn_lt hem_d hfield
      rw [sVecEm, Vector.getElem_mapFinRange] at hb
      exact hb⟩
  rw [hS_eq] at h_polyeq
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = av.value B * bv.value B := by
    rw [polyValue_mul_eq env a b ha_lt hb_lt hfield, h_a, h_b]
  have hSplit := polyValue_sVecEm_split (B := B) env qVar n em
    (fun k hk => by
      have h1 := val_bigIntMulNoReduce_coeff_lt env qVar n k hqd_lt hn_lt hfield
      have h2 := hem_d k.val hk
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by
        nlinarith [Nat.two_pow_pos (2 * B)]
      omega)
  have hSqn : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce qVar n))
      = BigInt.value B (Vector.map (Expression.eval env) qVar) * nv.value B := by
    rw [polyValue_Sqn_eq env qVar n hqd_lt hn_lt hfield, h_n]
  rw [hP, hSplit, hSqn, h_em] at h_polyeq
  -- h_polyeq : av·bv = qv·nv + emv; conclude
  rw [h_polyeq, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hem_lt]

/-- **Witnessed-product soundness core**: same conclusion, consuming the
`EqViaCarries` implication over the abstract coefficient vectors `Pv`,`Qv` and the
per-element eval bridges. -/
lemma soundness_core_wm {B : ℕ} (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n em : Var (BigInt m) (F p))
    (Pv Qv : Vector (Expression (F p)) (2 * m - 1))
    (av bv nv emv : BigInt m (F p))
    (h_a : Vector.map (Expression.eval env) a = av)
    (h_b : Vector.map (Expression.eval env) b = bv)
    (h_n : Vector.map (Expression.eval env) n = nv)
    (h_em : Vector.map (Expression.eval env) em = emv)
    (ha_norm : av.Normalized B) (hb_norm : bv.Normalized B)
    (hn_norm : nv.Normalized B) (hem_norm : emv.Normalized B)
    (hem_lt : emv.value B < nv.value B)
    (hq_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (heqQN_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Qv[k.val]
        = Expression.eval env (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])
    (h_eq_impl :
      ((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env
            (if h : k.val < m then Qv[k.val] + em[k.val]'h else Qv[k.val])).val
            < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) Pv) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k ↦
              if h : k.val < m then Qv[k.val] + em[k.val]'h else Qv[k.val]))) :
    emv.value B = av.value B * bv.value B % nv.value B := by
  have h_eq_impl' := eqImpl_bridge_em env em Pv (bigIntMulNoReduce a b)
    Qv (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)
    heqAB_get heqQN_get h_eq_impl
  exact soundness_core (B := B) hp i₀ env a b n em av bv nv emv h_a h_b h_n h_em
    ha_norm hb_norm hn_norm hem_norm hem_lt hq_norm h_eq_impl'

/-- **Completeness core** (schoolbook form). Given the honest quotient witness
`q = ⌊a·b/n⌋` and the spec `em = (a·b) mod n`, produce the `NormalizeTight q`
obligation (top limb `< 2^tq`) and the `EqViaCarries` conjunction. -/
lemma completeness_core {B tb tq : ℕ} (hB : 2 ^ B < p) (htb1 : 1 ≤ tb) (htqB : tq ≤ B)
    (htbq : tb ≤ tq)
    (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n em : Var (BigInt m) (F p))
    (av bv nv emv : BigInt m (F p))
    (h_a : Vector.map (Expression.eval env) a = av)
    (h_b : Vector.map (Expression.eval env) b = bv)
    (h_n : Vector.map (Expression.eval env) n = nv)
    (h_em : Vector.map (Expression.eval env) em = emv)
    (ha_norm : av.Normalized B) (hb_norm : bv.Normalized B)
    (hn_norm : nv.Normalized B) (hem_norm : emv.Normalized B)
    (hab_ltT : av.value B < 2 ^ ((m - 1) * B + tb))
    (hbb_ltT : bv.value B < 2 ^ ((m - 1) * B + tb))
    (hbb_ltN : bv.value B < nv.value B)
    (h_spec : emv.value B = av.value B * bv.value B % nv.value B)
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((av.value B * bv.value B / nv.value B / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p)) :
    BigInt.NormalizedTight B tq (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })) ∧
      ((∀ k : Fin (2 * m - 1),
            (Expression.eval env (bigIntMulNoReduce a b)[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
          ∀ k : Fin (2 * m - 1),
            (Expression.eval env
              (if h : k.val < m then
                (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]
                  + em[k.val]'h
              else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])).val
              < (m + 1) * 2 ^ (2 * B)) ∧
        polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b)) =
          polyValue B
            (Vector.map (Expression.eval env)
              (Vector.mapFinRange (2 * m - 1) fun k ↦
                if h : k.val < m then
                  (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]
                    + em[k.val]'h
                else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])) := by
  set A := av.value B with hA
  set Bb := bv.value B with hBb
  set N := nv.value B with hN
  set qval := A * Bb / N with hqval_def
  have hm1 : m - 1 < m := by have := Nat.pos_of_neZero m; omega
  -- the honest quotient bounds
  have hqval_ltT : qval < 2 ^ ((m - 1) * B + tq) := by
    rw [hqval_def]
    apply Nat.div_lt_of_lt_mul
    calc A * Bb < 2 ^ ((m - 1) * B + tq) * N := by
          refine Nat.mul_lt_mul_of_lt_of_le ?_ hbb_ltN.le (by omega)
          exact lt_of_lt_of_le hab_ltT (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ = N * 2 ^ ((m - 1) * B + tq) := Nat.mul_comm _ _
  have hTle : (m - 1) * B + tq ≤ B * m := by
    have hm := Nat.pos_of_neZero m
    calc (m - 1) * B + tq ≤ (m - 1) * B + B := by omega
      _ = m * B := by
          cases m with
          | zero => omega
          | succ k => rw [Nat.succ_sub_one]; ring
      _ = B * m := Nat.mul_comm m B
  have hqval_lt : qval < 2 ^ (B * m) :=
    lt_of_lt_of_le hqval_ltT (Nat.pow_le_pow_right (by norm_num) hTle)
  -- witness values / normalization
  have hqv_val : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) = qval :=
    BigInt.value_mapRange i₀ qval env hB hqval_lt (by intro i; rw [hqwit i])
  have hqv_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) :=
    MulMod.normalized_mapRange i₀ qval env hB (by intro i; rw [hqwit i])
  -- tight top limb of q
  have hqtop : BigInt.NormalizedTight B tq (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) := by
    refine ⟨hqv_norm, ?_⟩
    have hget : (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }))[m - 1]'(by
          have := Nat.pos_of_neZero m; omega) = env.get (i₀ + (m - 1)) := by
      simp [circuit_norm]
    rw [hget, hqwit ⟨m - 1, hm1⟩,
      ZMod.val_natCast_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) hB.le)]
    calc qval / 2 ^ (B * (m - 1)) % 2 ^ B ≤ qval / 2 ^ (B * (m - 1)) := Nat.mod_le _ _
      _ < 2 ^ tq := by
          apply Nat.div_lt_of_lt_mul
          rw [show (2 : ℕ) ^ (B * (m - 1)) * 2 ^ tq = 2 ^ ((m - 1) * B + tq) from by
            rw [← pow_add]; congr 1; ring]
          exact hqval_ltT
  -- digit bounds
  have ha_lt : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env a[i.val] = av[i.val] from by
      rw [← h_a]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env b[i.val] = bv[i.val] from by
      rw [← h_b]; simp only [Vector.getElem_map]]; exact hb_norm i
  have hn_lt' : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env n[i.val] = nv[i.val] from by
      rw [← h_n]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hem_d : ∀ j : ℕ, (hj : j < m) → (Expression.eval env (em[j]'hj)).val < 2 ^ B := by
    intro j hj
    rw [show Expression.eval env (em[j]'hj) = emv[j]'hj from by
      rw [← h_em]; simp only [Vector.getElem_map]]
    exact hem_norm ⟨j, hj⟩
  have hqd_lt : ∀ i : Fin m,
      (Expression.eval env (Vector.mapRange m fun j ↦ var (F := F p) { index := i₀ + j })[i.val]).val
        < 2 ^ B := by
    intro i; have := hqv_norm i; rwa [Fin.getElem_fin, Vector.getElem_map] at this
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
    omega
  have hS_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then
          (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]
            + em[k.val]'h
        else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])
      = sVecEm (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n em := rfl
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = A * Bb := by
    rw [polyValue_mul_eq env a b ha_lt hb_lt hfield, h_a, h_b]
  have hSplit := polyValue_sVecEm_split (B := B) env
    (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n em
    (fun k hk => by
      have h1 := val_bigIntMulNoReduce_coeff_lt env (Vector.mapRange m fun i ↦ var { index := i₀ + i })
        n k hqd_lt hn_lt' hfield
      have h2 := hem_d k.val hk
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by
        nlinarith [Nat.two_pow_pos (2 * B)]
      omega)
  have hSqn : polyValue B (Vector.map (Expression.eval env)
      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n))
      = qval * N := by
    rw [polyValue_Sqn_eq env (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n hqd_lt hn_lt' hfield,
      hqv_val, h_n]
  have hpolyS : polyValue B (Vector.map (Expression.eval env)
      (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then
          (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]
            + em[k.val]'h
        else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]))
      = A * Bb := by
    rw [hS_eq, hSplit, hSqn, h_em, h_spec, hqval_def, Nat.div_add_mod']
  refine ⟨hqtop, ⟨?_, ?_⟩, ?_⟩
  · intro k; exact coeff_P_bound env a b k ha_lt hb_lt hfield
  · intro k
    have hb := coeff_SEm_bound env (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n em k
      hqd_lt hn_lt' hem_d hfield
    rw [sVecEm, Vector.getElem_mapFinRange] at hb
    exact hb
  · rw [hP, hpolyS]

/-- **Witnessed-product completeness core**: same obligations, phrased over the
abstract witnessed-product vectors `Pv`,`Qv` via `eqConj_bridge_em`. -/
lemma completeness_core_wm {B tb tq : ℕ} (hB : 2 ^ B < p) (htb1 : 1 ≤ tb) (htqB : tq ≤ B)
    (htbq : tb ≤ tq)
    (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n em : Var (BigInt m) (F p))
    (Pv Qv : Vector (Expression (F p)) (2 * m - 1))
    (av bv nv emv : BigInt m (F p))
    (h_a : Vector.map (Expression.eval env) a = av)
    (h_b : Vector.map (Expression.eval env) b = bv)
    (h_n : Vector.map (Expression.eval env) n = nv)
    (h_em : Vector.map (Expression.eval env) em = emv)
    (ha_norm : av.Normalized B) (hb_norm : bv.Normalized B)
    (hn_norm : nv.Normalized B) (hem_norm : emv.Normalized B)
    (hab_ltT : av.value B < 2 ^ ((m - 1) * B + tb))
    (hbb_ltT : bv.value B < 2 ^ ((m - 1) * B + tb))
    (hbb_ltN : bv.value B < nv.value B)
    (h_spec : emv.value B = av.value B * bv.value B % nv.value B)
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((av.value B * bv.value B / nv.value B / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (heqQN_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Qv[k.val]
        = Expression.eval env (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]) :
    BigInt.NormalizedTight B tq (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })) ∧
      ((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
          (∀ k : Fin (2 * m - 1),
            (Expression.eval env
              (if h : k.val < m then Qv[k.val] + em[k.val]'h else Qv[k.val])).val
              < (m + 1) * 2 ^ (2 * B))) ∧
        polyValue B (Vector.map (Expression.eval env) Pv) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k ↦
              if h : k.val < m then Qv[k.val] + em[k.val]'h else Qv[k.val])) := by
  obtain ⟨hqt, hconj1, hconj2⟩ :=
    completeness_core (B := B) (tb := tb) (tq := tq) hB htb1 htqB htbq hp i₀ env a b n em
      av bv nv emv h_a h_b h_n h_em ha_norm hb_norm hn_norm hem_norm
      hab_ltT hbb_ltT hbb_ltN h_spec hqwit
  exact ⟨hqt,
    eqConj_bridge_em env em Pv (bigIntMulNoReduce a b) Qv
      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)
      heqAB_get heqQN_get ⟨hconj1, hconj2⟩⟩

/-! ## The formal assertion -/

/-- The `MulModTo` formal assertion: `a·b ≡ em (mod n)` with `em` canonical
(`em = (a·b) mod n`), fusing the final lazy modmul with the equality check. -/
def circuit (P : BigIntParams p m) (tb tq : ℕ) (htq : 1 ≤ tq ∧ 2 ^ tq < p) (htqB : tq ≤ P.B)
    (htb1 : 1 ≤ tb) (htbq : tb ≤ tq) [Fact (p > 2)] :
    FormalAssertion (F p) (InputsTo m) where
  main := main P tq htq htqB
  Assumptions := Assumptions P.B tb
  Spec := Spec P.B
  soundness := by
    obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
    circuit_proof_start [NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      NormalizeTight.Assumptions, NormalizeTight.Spec,
      EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      EqViaCarries.Assumptions, EqViaCarries.Spec]
    obtain ⟨ha_norm, hb_norm, hn_norm, hem_norm, hab_ltT, hbb_ltT, hbb_ltN, hem_lt⟩ := h_assumptions
    obtain ⟨hq_tight, hAB_ops, hQN_ops, h_eq_impl⟩ := h_holds
    have hpm : 2 * m - 1 < p := two_m_sub_one_lt hp
    have h_pAB := interpolatedMul_soundness (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)))
      input_var.a input_var.b env hAB_ops
    have h_pQN := interpolatedMul_soundness
      (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)) + Operations.localLength
        (interpolatedMul input_var.a input_var.b (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)))).2)
      (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus env hQN_ops
    refine ⟨?_, interpolatedMul_requirements _ _ _ _, interpolatedMul_requirements _ _ _ _⟩
    have h_a : Vector.map (Expression.eval env) input_var.a = input.a := by
      simp only [← h_input]
    have h_b : Vector.map (Expression.eval env) input_var.b = input.b := by
      simp only [← h_input]
    have h_n : Vector.map (Expression.eval env) input_var.modulus = input.modulus := by
      simp only [← h_input]
    have h_em : Vector.map (Expression.eval env) input_var.em = input.em := by
      simp only [← h_input]
    have heqAB_get := interpolatedMul_eval_bridge env (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)))
      input_var.a input_var.b hpm h_pAB
    have heqQN_get := interpolatedMul_eval_bridge env
      (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)) + Operations.localLength
        (interpolatedMul input_var.a input_var.b (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)))).2)
      (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus hpm h_pQN
    exact soundness_core_wm (B := B) hp i₀ env
      input_var.a input_var.b input_var.modulus input_var.em
      (interpolatedMul input_var.a input_var.b (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)))).1
      (interpolatedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus
        (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)) + Operations.localLength
          (interpolatedMul input_var.a input_var.b (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)))).2)).1
      input.a input.b input.modulus input.em h_a h_b h_n h_em
      ha_norm hb_norm hn_norm hem_norm hem_lt hq_tight.1 heqAB_get heqQN_get h_eq_impl
  completeness := by
    obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
    circuit_proof_start [NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      NormalizeTight.Assumptions, NormalizeTight.Spec,
      EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      EqViaCarries.Assumptions, EqViaCarries.Spec]
    obtain ⟨ha_norm, hb_norm, hn_norm, hem_norm, hab_ltT, hbb_ltT, hbb_ltN, hem_lt⟩ := h_assumptions
    obtain ⟨hq_env, hAB_uses, hQN_uses⟩ := h_env
    have h_pvAB := interpolatedMul_usesLocalWitnesses (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)))
      (i₀ + m + ((m - 1) * (B - 1) + (tq - 1))) input_var.a input_var.b env rfl hAB_uses
    have h_pvQN := interpolatedMul_usesLocalWitnesses
      (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)) + Operations.localLength
        (interpolatedMul input_var.a input_var.b (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)))).2)
      (Operations.localLength (interpolatedMul input_var.a input_var.b
          (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)))).2
        + (i₀ + m + ((m - 1) * (B - 1) + (tq - 1))))
      (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus env
      (Nat.add_comm _ _) hQN_uses
    have heva : MulMod.evalValue B env input_var.a = BigInt.value B input.a := by
      rw [MulMod.evalValue, BigInt.value, ← h_input]
    have hevb : MulMod.evalValue B env input_var.b = BigInt.value B input.b := by
      rw [MulMod.evalValue, BigInt.value, ← h_input]
    have hevn : MulMod.evalValue B env input_var.modulus = BigInt.value B input.modulus := by
      rw [MulMod.evalValue, BigInt.value, ← h_input]
    have hqwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + i.val)
        = ((BigInt.value B input.a * BigInt.value B input.b / BigInt.value B input.modulus
            / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
      intro i; rw [hq_env i, Vector.getElem_ofFn, heva, hevb, hevn]
    have h_a : Vector.map (Expression.eval env.toEnvironment) input_var.a = input.a := by
      simp only [← h_input]
    have h_b : Vector.map (Expression.eval env.toEnvironment) input_var.b = input.b := by
      simp only [← h_input]
    have h_n : Vector.map (Expression.eval env.toEnvironment) input_var.modulus = input.modulus := by
      simp only [← h_input]
    have h_em : Vector.map (Expression.eval env.toEnvironment) input_var.em = input.em := by
      simp only [← h_input]
    have heqAB_get := interpolatedMul_eval_bridge_uses env.toEnvironment
      (i₀ + m + ((m - 1) * (B - 1) + (tq - 1))) input_var.a input_var.b h_pvAB
    have heqQN_get := interpolatedMul_eval_bridge_uses env.toEnvironment
      (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)) + Operations.localLength
        (interpolatedMul input_var.a input_var.b (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)))).2)
      (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus h_pvQN
    have core := completeness_core_wm (B := B) (tb := tb) (tq := tq) hB htb1 htqB htbq hp i₀
      env.toEnvironment input_var.a input_var.b input_var.modulus input_var.em
      (interpolatedMul input_var.a input_var.b (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)))).1
      (interpolatedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus
        (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)) + Operations.localLength
          (interpolatedMul input_var.a input_var.b (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)))).2)).1
      input.a input.b input.modulus input.em h_a h_b h_n h_em
      ha_norm hb_norm hn_norm hem_norm hab_ltT hbb_ltT hbb_ltN h_spec hqwit heqAB_get heqQN_get
    exact ⟨core.1,
      interpolatedMul_completeness (i₀ + m + ((m - 1) * (B - 1) + (tq - 1)))
        input_var.a input_var.b env h_pvAB,
      interpolatedMul_completeness _ (Vector.mapRange m fun i => var { index := i₀ + i })
        input_var.modulus env h_pvQN,
      core.2⟩

end MulModTo

end

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
