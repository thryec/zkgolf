import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulMod
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.NormalizeTight

/-!
# RSA canonical modular multiplication with lazy inputs — `MulModCanon`

`MulModCanon` reuses `MulMod.main` (so it keeps the canonical `LessThan (r < n)`
check and produces the **exact** remainder `r = a·b % n`), but weakens the input
precondition to the *lazy* bounds (`a, b < 2^((m-1)B+tb)` instead of `a, b < n`).

It is used once, as the final canonicalizing step of `ModExp`/`Main`: applied to a
`MulModLazy` output (congruent, `< 2^4096`) and the constant `1`, it recovers the
canonical `sig^e mod n < n`, which the top-level `Equal` needs.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace MulModCanon

open MulMod (Inputs interpolatedMul interpolatedMul_soundness interpolatedMul_eval_bridge
  interpolatedMul_eval_bridge_uses interpolatedMul_requirements interpolatedMul_usesLocalWitnesses
  interpolatedMul_completeness two_m_sub_one_lt evalValue)

/-- The `main` circuit of `MulModCanon` — a local copy of `MulMod.main` (so that
`circuit_proof_start` reduces its offsets), reusing the shared `interpolatedMul`. -/
def main (P : BigIntParams p m) [Fact (p > 2)]
    (input : Var (Inputs m) (F p)) :
    Circuit (F p) (Var (BigInt m) (F p)) := do
  let a := input.a
  let b := input.b
  let n := input.modulus
  let q ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env a * evalValue P.B env b
    let qval : ℕ := prod / evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let r ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env a * evalValue P.B env b
    let rval : ℕ := prod % evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((rval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  Normalize.circuit P q
  Normalize.circuit P r
  let Pc ← interpolatedMul a b
  let Sqn ← interpolatedMul q n
  let S : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then Sqn[k.val] + r[k.val]'h else Sqn[k.val]
  EqViaCarries.circuit P { lhs := Pc, rhs := S }
  LessThan.circuit P { lhs := r, rhs := n }
  return r

instance elaborated (P : BigIntParams p m) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) (BigInt m) (main P) where
  localLength _ :=
    m + m + m * (P.B - 1) + m * (P.B - 1) + (2 * m - 1) + (2 * m - 1)
      + ((2 * m - 1 - 1) * (P.W - 1) + (2 * m - 1 - 1)) + (m + m * (P.B - 1) + (m - 1))
  output _ i0 := varFromOffset (BigInt m) (i0 + m)
  localLength_eq := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      LessThan.circuit, LessThan.elaborated, LessThan.main, RangeCheck.circuit, Gadgets.ToBits.rangeCheck]
    omega
  output_eq := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      LessThan.circuit, LessThan.elaborated, LessThan.main, RangeCheck.circuit, Gadgets.ToBits.rangeCheck]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      LessThan.circuit, LessThan.elaborated, LessThan.main, RangeCheck.circuit, Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      LessThan.circuit, LessThan.elaborated, LessThan.main, RangeCheck.circuit, Gadgets.ToBits.rangeCheck]

/-- Preconditions (lazy inputs, canonical output): `a`, `b`, `n` normalized; `a`, `b`,
`n` all `< 2^((m-1)B+tb)`; `n` positive; and `n` large enough (`2^(2·T) ≤ n·2^(B·m)`)
that the honest quotient still fits `m` limbs. -/
def Assumptions (B tb : ℕ) (input : Inputs m (F p)) : Prop :=
  let a := input.a
  let b := input.b
  let n := input.modulus
  a.Normalized B ∧ b.Normalized B ∧ n.Normalized B ∧
    a.value B < 2 ^ ((m - 1) * B + tb) ∧ b.value B < 2 ^ ((m - 1) * B + tb) ∧
    n.value B < 2 ^ ((m - 1) * B + tb) ∧ 0 < n.value B ∧
    2 ^ (2 * ((m - 1) * B + tb)) ≤ n.value B * 2 ^ (B * m)

/-- The `MulModCanon` formal circuit: canonical `c = a · b mod n` (`c < n`, exact),
under relaxed *lazy* input bounds. Structurally identical to `MulMod` (it reuses
`MulMod.main`); only the precondition is weakened and the completeness quotient bound
is discharged from `2^(2·T) ≤ n·2^(B·m)`. -/
def circuit (P : BigIntParams p m) (tb : ℕ) (htbB : tb ≤ P.B) [Fact (p > 2)] :
    FormalCircuit (F p) (Inputs m) (BigInt m) where
    main := main P
    Assumptions := Assumptions P.B tb
    Spec := MulMod.Spec P.B
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
        EqViaCarries.Assumptions, EqViaCarries.Spec,
        LessThan.circuit, LessThan.elaborated, LessThan.main,
        LessThan.Assumptions, LessThan.Spec]
      obtain ⟨ha_norm, hb_norm, hn_norm, hab_ltT, hbb_ltT, hn_ltT, hn_pos, hn_big⟩ := h_assumptions
      obtain ⟨hq_norm, hr_norm, hAB_ops, hQN_ops, h_eq_impl, h_lt_impl⟩ := h_holds
      have hpm : 2 * m - 1 < p := two_m_sub_one_lt hp
      have h_pAB := interpolatedMul_soundness (i₀ + m + m + m * (B - 1) + m * (B - 1)) input_var.a input_var.b env hAB_ops
      have h_pQN := interpolatedMul_soundness
        (i₀ + m + m + m * (B - 1) + m * (B - 1) + Operations.localLength
          (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + m * (B - 1))).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus env hQN_ops
      refine ⟨?_, interpolatedMul_requirements _ _ _ _, interpolatedMul_requirements _ _ _ _⟩
      have h_input' : (Vector.map (Expression.eval env) input_var.a,
          Vector.map (Expression.eval env) input_var.b,
          Vector.map (Expression.eval env) input_var.modulus)
            = ((input.a, input.b, input.modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [← h_input]
      have heqAB_get := interpolatedMul_eval_bridge env (i₀ + m + m + m * (B - 1) + m * (B - 1))
        input_var.a input_var.b hpm h_pAB
      have heqQN_get := interpolatedMul_eval_bridge env
        (i₀ + m + m + m * (B - 1) + m * (B - 1) + Operations.localLength
          (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + m * (B - 1))).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus hpm h_pQN
      exact MulMod.mulMod_soundness_core_wm (B := B) hp i₀ env
        input_var.a input_var.b input_var.modulus
        (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + m * (B - 1))).1
        (interpolatedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus
          (i₀ + m + m + m * (B - 1) + m * (B - 1) + Operations.localLength
            (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + m * (B - 1))).2)).1
        (input.a, input.b, input.modulus) h_input' ha_norm hb_norm hn_norm hq_norm hr_norm
        heqAB_get heqQN_get h_eq_impl h_lt_impl
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
        EqViaCarries.Assumptions, EqViaCarries.Spec,
        LessThan.circuit, LessThan.elaborated, LessThan.main,
        LessThan.Assumptions, LessThan.Spec]
      obtain ⟨ha_norm, hb_norm, hn_norm, hab_ltT, hbb_ltT, hn_ltT, hn_pos, hn_big⟩ := h_assumptions
      obtain ⟨hq_env, hr_env, hAB_uses, hQN_uses⟩ := h_env
      have h_pvAB := interpolatedMul_usesLocalWitnesses (i₀ + m + m + m * (B - 1) + m * (B - 1))
        (i₀ + m + m + m * (B - 1) + m * (B - 1)) input_var.a input_var.b env rfl hAB_uses
      have h_pvQN := interpolatedMul_usesLocalWitnesses
        (i₀ + m + m + m * (B - 1) + m * (B - 1) + Operations.localLength
          (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + m * (B - 1))).2)
        (Operations.localLength (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + m * (B - 1))).2
          + (i₀ + m + m + m * (B - 1) + m * (B - 1)))
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus env
        (Nat.add_comm _ _) hQN_uses
      have heva : evalValue B env input_var.a = BigInt.value B input.a := by
        rw [evalValue, BigInt.value, ← h_input]
      have hevb : evalValue B env input_var.b = BigInt.value B input.b := by
        rw [evalValue, BigInt.value, ← h_input]
      have hevn : evalValue B env input_var.modulus = BigInt.value B input.modulus := by
        rw [evalValue, BigInt.value, ← h_input]
      have hqwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + i.val)
          = ((BigInt.value B input.a * BigInt.value B input.b / BigInt.value B input.modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hq_env i, Vector.getElem_ofFn, heva, hevb, hevn]
      have hrwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + m + i.val)
          = ((BigInt.value B input.a * BigInt.value B input.b % BigInt.value B input.modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hr_env i, Vector.getElem_ofFn, heva, hevb, hevn]
      have h_input' : (Vector.map (Expression.eval env.toEnvironment) input_var.a,
          Vector.map (Expression.eval env.toEnvironment) input_var.b,
          Vector.map (Expression.eval env.toEnvironment) input_var.modulus)
            = ((input.a, input.b, input.modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [← h_input]
      have heqAB_get := interpolatedMul_eval_bridge_uses env.toEnvironment (i₀ + m + m + m * (B - 1) + m * (B - 1))
        input_var.a input_var.b h_pvAB
      have heqQN_get := interpolatedMul_eval_bridge_uses env.toEnvironment
        (i₀ + m + m + m * (B - 1) + m * (B - 1) + Operations.localLength
          (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + m * (B - 1))).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus h_pvQN
      have core := MulMod.mulMod_completeness_core_wm_lazy_canon (B := B) (tb := tb) hB htbB hp i₀ env.toEnvironment
        input_var.a input_var.b input_var.modulus
        (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + m * (B - 1))).1
        (interpolatedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus
          (i₀ + m + m + m * (B - 1) + m * (B - 1) + Operations.localLength
            (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + m * (B - 1))).2)).1
        (input.a, input.b, input.modulus) h_input' ha_norm hb_norm hn_norm
        hab_ltT hbb_ltT hn_ltT hn_pos hn_big hqwit hrwit heqAB_get heqQN_get
      exact ⟨core.1, core.2.1,
        interpolatedMul_completeness (i₀ + m + m + m * (B - 1) + m * (B - 1)) input_var.a input_var.b env h_pvAB,
        interpolatedMul_completeness _ (Vector.mapRange m fun i => var { index := i₀ + i })
          input_var.modulus env h_pvQN,
        core.2.2⟩

end MulModCanon

end

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
