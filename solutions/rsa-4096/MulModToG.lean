import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulMod
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.NormalizeTight
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulModTo
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.GroupedEq

/-!
# RSA fused modular-multiplication equality with grouped equality ("MulModToG")

`MulModToG` is `MulModTo` with the per-index `EqViaCarries` equality replaced by
the grouped `GroupedEq` assertion (group size `g`). The arithmetic core lemmas of
`MulModTo` are reused verbatim (`GroupedEq` certifies the same `polyValue`
equality under the same coefficient bounds).

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

namespace MulModToG

open MulMod (Inputs interpolatedMul interpolatedMul_output interpolatedMul_localLength
  interpolatedMul_soundness interpolatedMul_eval_bridge interpolatedMul_eval_bridge_uses
  interpolatedMul_requirements interpolatedMul_usesLocalWitnesses interpolatedMul_completeness
  two_m_sub_one_lt polyValue_mul_eq polyValue_Sqn_eq coeff_P_bound)
open MulModTo (InputsTo soundness_core_wm completeness_core_wm)

/-- The `main` circuit of `MulModTo`: witness `q = (a·b)/n`, tight-normalize it
(top limb `< 2^tq`), build the two convolution coefficient vectors by
interpolation multiplication, and assert `a·b = q·n + em` in base `2^B` via
`EqViaCarries` (with `em`'s limbs added on the affine right-hand side). -/
def main (P : BigIntParams p m) (tq : ℕ) (htq : 1 ≤ tq ∧ 2 ^ tq < p) (htqB : tq ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps p m P.B P.W g)
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

  GroupedEq.circuit P g hgp { lhs := Pc, rhs := S }

instance elaborated (P : BigIntParams p m) (tq : ℕ) (htq : 1 ≤ tq ∧ 2 ^ tq < p) (htqB : tq ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps p m P.B P.W g) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (InputsTo m) unit (main P tq htq htqB g hgp) where
  localLength _ :=
    m + ((m - 1) * (P.B - 1) + (tq - 1)) + (2 * m - 1) + (2 * m - 1)
      + ((GroupedEq.numGroups m g - 1) * (P.W - 1))
  localLength_eq := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm,
      NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      GroupedEq.circuit, GroupedEq.elaborated, GroupedEq.main, RangeCheck.circuit]
    omega
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, interpolatedMul, circuit_norm,
      NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      GroupedEq.circuit, GroupedEq.elaborated, GroupedEq.main, RangeCheck.circuit]
  channelsLawful := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm,
      NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      GroupedEq.circuit, GroupedEq.elaborated, GroupedEq.main, RangeCheck.circuit]

/-! ## The formal assertion -/

/-- The `MulModTo` formal assertion: `a·b ≡ em (mod n)` with `em` canonical
(`em = (a·b) mod n`), fusing the final lazy modmul with the equality check. -/
def circuit (P : BigIntParams p m) (tb tq : ℕ) (htq : 1 ≤ tq ∧ 2 ^ tq < p) (htqB : tq ≤ P.B)
    (htb1 : 1 ≤ tb) (htbq : tb ≤ tq)
    (g : ℕ) (hgp : GroupedEq.GHyps p m P.B P.W g) [Fact (p > 2)] :
    FormalAssertion (F p) (InputsTo m) where
  main := main P tq htq htqB g hgp
  Assumptions := MulModTo.Assumptions P.B tb
  Spec := MulModTo.Spec P.B
  soundness := by
    obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
    circuit_proof_start [NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      NormalizeTight.Assumptions, NormalizeTight.Spec,
      GroupedEq.circuit, GroupedEq.elaborated, GroupedEq.main,
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
      GroupedEq.circuit, GroupedEq.elaborated, GroupedEq.main,
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

end MulModToG

end

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
