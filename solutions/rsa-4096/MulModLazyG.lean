import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulMod
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.NormalizeTight
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.GroupedEq

/-!
# RSA lazy modular multiplication with grouped equality (gadget G5-lazy-G)

`MulModLazyG` is `MulModLazy` with the per-index `EqViaCarries` equality replaced
by the grouped `GroupedEq` assertion (group size `g`): only
`⌈(2m−1)/g⌉ − 1` carries are witnessed/range-checked instead of `2m−2`.
`MulModLazy` is a cheaper variant of `MulMod`: it drops the per-modmul `LessThan`
(canonical `r < n`) check and range-checks the remainder `r` with `NormalizeTight`
(top limb `< 2^tb`) instead of `Normalize`. This keeps each output `< 2^((m-1)B+tb)`
so the next quotient still fits `m` limbs, while only certifying the **congruence**
`r ≡ a·b (mod n)` rather than the canonical `r = a·b % n`. Congruence propagates
through the square-and-multiply chain; canonicity is pinned once, at the top level.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace MulModLazyG

open MulMod (Inputs interpolatedMul interpolatedMul_output interpolatedMul_localLength
  interpolatedMul_soundness interpolatedMul_eval_bridge interpolatedMul_eval_bridge_uses
  interpolatedMul_requirements interpolatedMul_usesLocalWitnesses interpolatedMul_completeness
  two_m_sub_one_lt)

/-- Natural-number value of a witnessed limb vector under a prover environment
(little-endian base `2^B`); used only inside the witness generators. -/
private def evalValue (B : ℕ) (env : ProverEnvironment (F p))
    (x : Var (BigInt m) (F p)) : ℕ :=
  Specs.RSA.fromLimbs B ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)

/-- The `main` circuit of `MulModLazy`. Like `MulMod.main` but `Normalize r` is
replaced by `NormalizeTight r` and the `LessThan (r < n)` check is dropped. -/
def main (P : BigIntParams p m) (tb : ℕ) (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htbB : tb ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps p m P.B P.W g) [Fact (p > 2)]
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
  NormalizeTight.circuit P tb htb htbB r

  let Pc ← interpolatedMul a b
  let Sqn ← interpolatedMul q n
  let S : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then Sqn[k.val] + r[k.val]'h else Sqn[k.val]

  GroupedEq.circuit P g hgp { lhs := Pc, rhs := S }

  return r

instance elaborated (P : BigIntParams p m) (tb : ℕ) (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htbB : tb ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps p m P.B P.W g) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) (BigInt m) (main P tb htb htbB g hgp) where
  localLength _ :=
    m + m + m * (P.B - 1) + ((m - 1) * (P.B - 1) + (tb - 1)) + (2 * m - 1) + (2 * m - 1)
      + ((GroupedEq.numGroups m g - 1) * (P.W - 1))
  output _ i0 := varFromOffset (BigInt m) (i0 + m)
  localLength_eq := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      GroupedEq.circuit, GroupedEq.elaborated, GroupedEq.main, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]
    omega
  output_eq := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      GroupedEq.circuit, GroupedEq.elaborated, GroupedEq.main, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      GroupedEq.circuit, GroupedEq.elaborated, GroupedEq.main, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    intro input offset
    simp only [main, interpolatedMul, circuit_norm, Normalize.circuit, Normalize.elaborated,
      Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      GroupedEq.circuit, GroupedEq.elaborated, GroupedEq.main, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]

/-- Preconditions for lazy modular multiplication: `a`, `b`, `n` normalized; `a`, `b`,
`n` all `< 2^((m-1)B+tb)`; and `n` large enough (`2^(2·T) ≤ n·2^(B·m)`) that the
honest quotient `q = ⌊a·b/n⌋` still fits `m` limbs. -/
def Assumptions (B tb : ℕ) (input : Inputs m (F p)) : Prop :=
  let a := input.a
  let b := input.b
  let n := input.modulus
  a.Normalized B ∧ b.Normalized B ∧ n.Normalized B ∧
    a.value B < 2 ^ ((m - 1) * B + tb) ∧ b.value B < 2 ^ ((m - 1) * B + tb) ∧
    n.value B < 2 ^ ((m - 1) * B + tb) ∧ 0 < n.value B ∧
    2 ^ (2 * ((m - 1) * B + tb)) ≤ n.value B * 2 ^ (B * m)

/-- Postcondition: the output is tight-normalized and **congruent** to `a·b` mod `n`. -/
def Spec (B tb : ℕ) (input : Inputs m (F p)) (out : BigInt m (F p)) : Prop :=
  let a := input.a
  let b := input.b
  let n := input.modulus
  BigInt.NormalizedTight B tb out ∧ out.value B % n.value B = (a.value B * b.value B) % n.value B

/-- The `MulModLazy` formal circuit: `c ≡ a · b (mod n)` over normalized big integers,
with `c` tight-normalized (`< 2^((m-1)B+tb)`). -/
def circuit (P : BigIntParams p m) (tb : ℕ) (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htbB : tb ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps p m P.B P.W g) [Fact (p > 2)] :
    FormalCircuit (F p) (Inputs m) (BigInt m) where
    main := main P tb htb htbB g hgp
    Assumptions := Assumptions P.B tb
    Spec := Spec P.B tb
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
        NormalizeTight.Assumptions, NormalizeTight.Spec,
        GroupedEq.circuit, GroupedEq.elaborated, GroupedEq.main,
        EqViaCarries.Assumptions, EqViaCarries.Spec]
      obtain ⟨ha_norm, hb_norm, hn_norm, hab_ltT, hbb_ltT, hn_ltT, hn_pos, hn_big⟩ := h_assumptions
      obtain ⟨hq_norm, hr_tight, hAB_ops, hQN_ops, h_eq_impl⟩ := h_holds
      have hpm : 2 * m - 1 < p := two_m_sub_one_lt hp
      have h_pAB := interpolatedMul_soundness (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)))
        input_var.a input_var.b env hAB_ops
      have h_pQN := interpolatedMul_soundness
        (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
          (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)))).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus env hQN_ops
      refine ⟨⟨hr_tight, ?_⟩, interpolatedMul_requirements _ _ _ _, interpolatedMul_requirements _ _ _ _⟩
      have h_input' : (Vector.map (Expression.eval env) input_var.a,
          Vector.map (Expression.eval env) input_var.b,
          Vector.map (Expression.eval env) input_var.modulus)
            = ((input.a, input.b, input.modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [← h_input]
      have heqAB_get := interpolatedMul_eval_bridge env (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)))
        input_var.a input_var.b hpm h_pAB
      have heqQN_get := interpolatedMul_eval_bridge env
        (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
          (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)))).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus hpm h_pQN
      exact (MulMod.mulMod_soundness_core_wm_lazy (B := B) hp i₀ env
        input_var.a input_var.b input_var.modulus
        (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)))).1
        (interpolatedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus
          (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
            (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)))).2)).1
        (input.a, input.b, input.modulus) h_input' ha_norm hb_norm hn_norm hq_norm hr_tight.1
        heqAB_get heqQN_get h_eq_impl).2
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
        NormalizeTight.Assumptions, NormalizeTight.Spec,
        GroupedEq.circuit, GroupedEq.elaborated, GroupedEq.main,
        EqViaCarries.Assumptions, EqViaCarries.Spec]
      obtain ⟨ha_norm, hb_norm, hn_norm, hab_ltT, hbb_ltT, hn_ltT, hn_pos, hn_big⟩ := h_assumptions
      obtain ⟨hq_env, hr_env, hAB_uses, hQN_uses⟩ := h_env
      have h_pvAB := interpolatedMul_usesLocalWitnesses (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)))
        (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1))) input_var.a input_var.b env rfl hAB_uses
      have h_pvQN := interpolatedMul_usesLocalWitnesses
        (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
          (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)))).2)
        (Operations.localLength (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)))).2
          + (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1))))
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
      have heqAB_get := interpolatedMul_eval_bridge_uses env.toEnvironment (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)))
        input_var.a input_var.b h_pvAB
      have heqQN_get := interpolatedMul_eval_bridge_uses env.toEnvironment
        (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
          (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)))).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus h_pvQN
      have core := MulMod.mulMod_completeness_core_wm_lazy (B := B) (tb := tb) hB htbB hp i₀ env.toEnvironment
        input_var.a input_var.b input_var.modulus
        (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)))).1
        (interpolatedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus
          (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
            (interpolatedMul input_var.a input_var.b (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1)))).2)).1
        (input.a, input.b, input.modulus) h_input' ha_norm hb_norm hn_norm
        hab_ltT hbb_ltT hn_ltT hn_pos hn_big hqwit hrwit heqAB_get heqQN_get
      exact ⟨core.1, core.2.1,
        interpolatedMul_completeness (i₀ + m + m + m * (B - 1) + ((m - 1) * (B - 1) + (tb - 1))) input_var.a input_var.b env h_pvAB,
        interpolatedMul_completeness _ (Vector.mapRange m fun i => var { index := i₀ + i })
          input_var.modulus env h_pvQN,
        core.2.2⟩

end MulModLazyG

end

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
