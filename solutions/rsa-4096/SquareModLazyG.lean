import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulMod
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.SquareModLazy
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.GroupedEqV

/-!
# RSA *lazy* modular squaring with graduated grouped equality (gadget G5′-lazy-V)

`SquareModLazyG` is `SquareModLazy` with the per-index `EqViaCarries` equality
replaced by the **graduated** grouped `GroupedEqV` assertion (group size `g`,
position-dependent carry widths `V.Wf`): only `⌈(2m−1)/g⌉ − 1` carries are
witnessed/range-checked, each at its own tent-shaped width. Everything else
(interpolated `a·a` and `q·n` products, tight-normalized quotient and remainder)
is unchanged; the same `MulMod` arithmetic cores are reused because `GroupedEqV`
certifies the same `polyValue` equality. The per-position coefficient bounds
demanded by `GroupedEqV.Assumptions` are discharged from the tent-shaped
convolution window bound (`GroupedEqV.val_bigIntMulNoReduce_coeff_le_pos`).
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

namespace SquareModLazyG

variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

open SquareModLazy (Inputs)

/-- Natural-number value of a witnessed limb vector (used only in witness generators). -/
private def evalValue (B : ℕ) (env : ProverEnvironment (F p))
    (x : Var (BigInt m) (F p)) : ℕ :=
  Specs.RSA.fromLimbs B ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)

/-- The `main` circuit of `SquareModLazy`: witness `q = a²/n`, `r = a²%n`,
tight-normalize `q` (top limb `< 2^(tb+1)`: the honest quotient is
`< 2^((m-1)B + tb + 1)` since `n ≥ 2^((m-1)B + tb - 1)`), tight-normalize `r`,
certify `a·a = q·n + r` via the graduated grouped equality, and return `r`. -/
def main (P : BigIntParams p m) (tb : ℕ) (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htbB : tb + 1 ≤ P.B)
    (g : ℕ) (V : GroupedEqV.VParams) (hgv : GroupedEqV.GVHyps p m P.B g V)
    [Fact (p > 2)] (input : Var (Inputs m) (F p)) :
    Circuit (F p) (Var (BigInt m) (F p)) := do
  let a := input.a
  let n := input.modulus

  let q ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env a * evalValue P.B env a
    let qval : ℕ := prod / evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let r ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env a * evalValue P.B env a
    let rval : ℕ := prod % evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((rval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  NormalizeTight.circuit P (tb + 1)
    ⟨by omega, lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) htbB) P.hB⟩
    htbB q
  NormalizeTight.circuit P tb htb (Nat.le_of_succ_le htbB) r

  let Pc ← MulMod.interpolatedMul a a
  let Sqn ← MulMod.interpolatedMul q n
  let S : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then Sqn[k.val] + r[k.val]'h else Sqn[k.val]

  GroupedEqV.circuit P.B g V hgv P.hB1 { lhs := Pc, rhs := S }
  return r

instance elaborated (P : BigIntParams p m) (tb : ℕ) (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htbB : tb + 1 ≤ P.B)
    (g : ℕ) (V : GroupedEqV.VParams) (hgv : GroupedEqV.GVHyps p m P.B g V) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) (BigInt m) (main P tb htb htbB g V hgv) where
  localLength _ :=
    m + m + ((m - 1) * (P.B - 1) + (tb + 1 - 1)) + ((m - 1) * (P.B - 1) + (tb - 1))
      + (2 * m - 1) + (2 * m - 1)
      + GroupedEqV.widthAllocFrom V.Wf (GroupedEq.numGroups m g - 1) 0
  output _ i0 := varFromOffset (BigInt m) (i0 + m)
  localLength_eq := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, circuit_norm, Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, GroupedEqV.circuit, GroupedEqV.elaborated, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]
    omega
  output_eq := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, circuit_norm, Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, GroupedEqV.circuit, GroupedEqV.elaborated, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, MulMod.interpolatedMul, circuit_norm, Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, GroupedEqV.circuit, GroupedEqV.elaborated, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, circuit_norm, Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, GroupedEqV.circuit, GroupedEqV.elaborated, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]

/-- Preconditions for lazy modular squaring: `a`, `n` normalized; `a`, `n` both
`< 2^((m-1)B+tb)`; and the modulus lower bound `2^((m-1)B+tb-1) ≤ n` (so the
honest quotient `q = ⌊a²/n⌋` is `< 2^((m-1)B+tb+1)`, fitting `m` limbs with a
`tb+1`-bit top limb). -/
def Assumptions (B tb : ℕ) (input : Inputs m (F p)) : Prop :=
  let a := input.a
  let n := input.modulus
  a.Normalized B ∧ n.Normalized B ∧
    a.value B < 2 ^ ((m - 1) * B + tb) ∧
    n.value B < 2 ^ ((m - 1) * B + tb) ∧ 0 < n.value B ∧
    2 ^ ((m - 1) * B + tb - 1) ≤ n.value B

/-- Postcondition: the output is tight-normalized and **congruent** to `a·a` mod `n`. -/
def Spec (B tb : ℕ) (input : Inputs m (F p)) (out : BigInt m (F p)) : Prop :=
  let a := input.a
  let n := input.modulus
  BigInt.NormalizedTight B tb out ∧ out.value B % n.value B = (a.value B * a.value B) % n.value B

/-- Adequacy of the graduated coefficient-bound function for the squaring step:
`Nf` dominates the per-position convolution window bound plus one extra limb —
the tent bound below the top window, and in the upper regime `m − 1 ≤ j` the
top-limb-aware bound (`≤ 2m−3−j` interior products, one product carrying the
quotient top limb `< 2^(tb+1)`, one carrying an input/modulus top limb
`< 2^tb`). -/
def NfOk (B tb : ℕ) (V : GroupedEqV.VParams) : Prop :=
  ∀ j, j < 2 * m - 1 →
    (if m - 1 ≤ j then
      (2 * m - 3 - j) * ((2 ^ B - 1) * (2 ^ B - 1))
        + (2 ^ (tb + 1) - 1) * (2 ^ B - 1) + (2 ^ tb - 1) * (2 ^ B - 1) + 2 ^ B
    else
      min (j + 1) (2 * m - 1 - j) * ((2 ^ B - 1) * (2 ^ B - 1)) + 2 ^ B) ≤ V.Nf j

/-- Discharge `GroupedEqV.Assumptions` for the squaring step: the witnessed
product coefficients equal tent-bounded convolutions (via the interpolation
bridges), the rhs adds one normalized `r`-limb per low position, and in the
upper window regime the top limbs of `a`, `n` (`< 2^tb`) and of the quotient
(`< 2^(tb+1)`) tighten the two boundary window products. -/
private lemma vassum {B tb : ℕ} (env : Environment (F p)) (V : GroupedEqV.VParams)
    (hNf : NfOk (m := m) B tb V) (htbB : tb + 1 ≤ B)
    (a n : Var (BigInt m) (F p)) (i₀ : ℕ)
    (Pv Qv : Vector (Expression (F p)) (2 * m - 1))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B)
    (hq : ∀ i : Fin m, (Expression.eval env (var (F := F p) { index := i₀ + i.val })).val < 2 ^ B)
    (hr : ∀ i : Fin m, (Expression.eval env (var (F := F p) { index := i₀ + m + i.val })).val < 2 ^ B)
    (ha_top : (Expression.eval env
      (a[m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tb)
    (hn_top : (Expression.eval env
      (n[m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tb)
    (hq_top : (Expression.eval env
      (var (F := F p) { index := i₀ + (m - 1) })).val < 2 ^ (tb + 1))
    (heqP : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a a)[k.val])
    (heqQ : ∀ k : Fin (2 * m - 1),
      Expression.eval env Qv[k.val]
        = Expression.eval env
            (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])
    (hbound : m * (2 ^ B * 2 ^ B) < p) :
    (∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < V.Nf k.val) ∧
    (∀ k : Fin (2 * m - 1),
      (Expression.eval env
        (if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val])).val
        < V.Nf k.val) := by
  have hg1 : (1 : ℕ) ≤ 2 ^ B := Nat.one_le_two_pow
  have hm := Nat.pos_of_neZero m
  have hqvec : ∀ i : Fin m, (Expression.eval env
      ((Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i })[i.val])).val < 2 ^ B := by
    intro i
    have hgi : (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i })[i.val]
        = var { index := i₀ + i.val } := by simp [circuit_norm]
    rw [hgi]; exact hq i
  have hq_top' : (Expression.eval env
      ((Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i })[m - 1]'(by omega))).val
        < 2 ^ (tb + 1) := by
    have hgi : (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i })[m - 1]'(by omega)
        = var { index := i₀ + (m - 1) } := by simp [circuit_norm]
    rw [hgi]; exact hq_top
  -- monotonicity of the narrow-product atoms, for the `omega` closes below
  have hCD : (2 ^ tb - 1) * (2 ^ B - 1) ≤ (2 ^ (tb + 1) - 1) * (2 ^ B - 1) :=
    Nat.mul_le_mul_right _ (by
      have := Nat.pow_le_pow_right (show 1 ≤ 2 from by norm_num) (Nat.le_succ tb)
      omega)
  constructor
  · intro k
    rw [heqP k]
    have h2 := hNf k.val k.isLt
    by_cases hj : m - 1 ≤ k.val
    · rw [if_pos hj] at h2
      have h1 := GroupedEqV.val_bigIntMulNoReduce_coeff_le_top (ta := tb) (tb' := tb)
        env a a k ha ha ha_top ha_top (by omega) (by omega) hj hbound
      omega
    · rw [if_neg hj] at h2
      have h1 := GroupedEqV.val_bigIntMulNoReduce_coeff_le_pos env a a k ha ha hbound
      omega
  · intro k
    have h2 := hNf k.val k.isLt
    have h1 : (Expression.eval env
        ((bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])).val
          < V.Nf k.val - (2 ^ B - 1) ∨
        (Expression.eval env
        ((bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])).val
          + (2 ^ B - 1) < V.Nf k.val := by
      right
      by_cases hj : m - 1 ≤ k.val
      · rw [if_pos hj] at h2
        have h1t := GroupedEqV.val_bigIntMulNoReduce_coeff_le_top (ta := tb + 1) (tb' := tb)
          env (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n k hqvec hn
          hq_top' hn_top (by omega) (by omega) hj hbound
        omega
      · rw [if_neg hj] at h2
        have h1t := GroupedEqV.val_bigIntMulNoReduce_coeff_le_pos env
          (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n k hqvec hn hbound
        omega
    have h1' : (Expression.eval env
        ((bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])).val
          + (2 ^ B - 1) < V.Nf k.val := by omega
    by_cases h : k.val < m
    · rw [dif_pos h]
      have hadd : (Expression.eval env (Qv[k.val] + var { index := i₀ + m + k.val })).val
          ≤ (Expression.eval env Qv[k.val]).val
            + (Expression.eval env (var (F := F p) { index := i₀ + m + k.val })).val := by
        rw [show Expression.eval env (Qv[k.val] + var { index := i₀ + m + k.val })
            = Expression.eval env Qv[k.val]
              + Expression.eval env (var (F := F p) { index := i₀ + m + k.val }) from by
          simp [Expression.eval]]
        rw [ZMod.val_add]
        exact Nat.mod_le _ _
      have h3 : (Expression.eval env (var (F := F p) { index := i₀ + m + k.val })).val < 2 ^ B :=
        hr ⟨k.val, h⟩
      rw [heqQ k] at hadd
      omega
    · rw [dif_neg h]
      rw [heqQ k]
      omega

set_option maxHeartbeats 8000000 in
/-- The `SquareModLazy` formal circuit with graduated carries: `c ≡ a · a (mod n)`
over normalized big integers, with `c` tight-normalized (`< 2^((m-1)B+tb)`). -/
def circuit (P : BigIntParams p m) (tb : ℕ) (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htbB : tb + 1 ≤ P.B)
    (g : ℕ) (V : GroupedEqV.VParams) (hgv : GroupedEqV.GVHyps p m P.B g V)
    (hNf : NfOk (m := m) P.B tb V) [Fact (p > 2)] :
    FormalCircuit (F p) (Inputs m) (BigInt m) where
    main := main P tb htb htbB g V hgv
    Assumptions := Assumptions P.B tb
    Spec := Spec P.B tb
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
        NormalizeTight.Assumptions, NormalizeTight.Spec,
        GroupedEqV.circuit_assumptions_eq, GroupedEqV.circuit_spec_eq,
        GroupedEqV.Assumptions, EqViaCarries.Spec]
      obtain ⟨ha_norm, hn_norm, hab_ltT, hn_ltT, hn_pos, hn_ge⟩ := h_assumptions
      obtain ⟨hq_tight, hr_tight, hSq_ops, hQN_ops, h_eq_impl⟩ := h_holds
      have hpm : 2 * m - 1 < p := MulMod.two_m_sub_one_lt hp
      have h_pSq := MulMod.interpolatedMul_soundness (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))
        input_var.a input_var.a env hSq_ops
      have h_pQN := MulMod.interpolatedMul_soundness
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
          (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus env hQN_ops
      refine ⟨⟨hr_tight, ?_⟩, MulMod.interpolatedMul_requirements _ _ _ _,
        MulMod.interpolatedMul_requirements _ _ _ _,
        Or.inl (GroupedEqV.circuit_channels_req_eq _ _ _ _ _)⟩
      have h_input' : (Vector.map (Expression.eval env) input_var.a,
          Vector.map (Expression.eval env) input_var.a,
          Vector.map (Expression.eval env) input_var.modulus)
            = ((input.a, input.a, input.modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [← h_input]
      have heqSq_get := MulMod.interpolatedMul_eval_bridge env (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))
        input_var.a input_var.a hpm h_pSq
      have heqQN_get := MulMod.interpolatedMul_eval_bridge env
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
          (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus hpm h_pQN
      -- per-position coefficient bounds for the graduated equality
      have hmapa : Vector.map (Expression.eval env) input_var.a = input.a :=
        congrArg SquareModLazy.Inputs.a h_input
      have hmapn : Vector.map (Expression.eval env) input_var.modulus = input.modulus :=
        congrArg SquareModLazy.Inputs.modulus h_input
      have ha_lim : ∀ i : Fin m, (Expression.eval env (input_var.a[i.val]'i.isLt)).val < 2 ^ B := by
        intro i
        have hel : Expression.eval env (input_var.a[i.val]'i.isLt) = input.a[i.val]'i.isLt := by
          rw [← hmapa, Vector.getElem_map]
        rw [hel]; exact ha_norm i
      have hn_lim : ∀ i : Fin m, (Expression.eval env (input_var.modulus[i.val]'i.isLt)).val < 2 ^ B := by
        intro i
        have hel : Expression.eval env (input_var.modulus[i.val]'i.isLt) = input.modulus[i.val]'i.isLt := by
          rw [← hmapn, Vector.getElem_map]
        rw [hel]; exact hn_norm i
      have hq_lim : ∀ i : Fin m, (Expression.eval env
          (var (F := F p) { index := i₀ + i.val })).val < 2 ^ B := by
        intro i
        have h := hq_tight.1 i
        simpa only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] using h
      have hr_lim : ∀ i : Fin m, (Expression.eval env
          (var (F := F p) { index := i₀ + m + i.val })).val < 2 ^ B := by
        intro i
        have h := hr_tight.1 i
        simpa only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] using h
      have hbound_m : m * (2 ^ B * 2 ^ B) < p := by
        have h2B : (2 : ℕ) ^ B * 2 ^ B = 2 ^ (2 * B) := by rw [two_mul, pow_add]
        rw [h2B]
        calc m * 2 ^ (2 * B) = 2 ^ (2 * B) * m := by ring
          _ ≤ 2 ^ (2 * B) * (m + 1) := by
              exact Nat.mul_le_mul_left _ (by omega)
          _ < 2 ^ (2 * B) * (m + 1) * 4 := by
              have hpos : 0 < 2 ^ (2 * B) * (m + 1) := by positivity
              omega
          _ < p := hp
      have ha_top : (Expression.eval env
          (input_var.a[m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tb := by
        have hel : Expression.eval env
            (input_var.a[m - 1]'(by have := Nat.pos_of_neZero m; omega))
              = input.a[m - 1]'(by have := Nat.pos_of_neZero m; omega) := by
          rw [← hmapa, Vector.getElem_map]
        rw [hel]
        exact GroupedEqV.top_limb_lt_of_value_lt hab_ltT
      have hn_top : (Expression.eval env
          (input_var.modulus[m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tb := by
        have hel : Expression.eval env
            (input_var.modulus[m - 1]'(by have := Nat.pos_of_neZero m; omega))
              = input.modulus[m - 1]'(by have := Nat.pos_of_neZero m; omega) := by
          rw [← hmapn, Vector.getElem_map]
        rw [hel]
        exact GroupedEqV.top_limb_lt_of_value_lt hn_ltT
      have hq_top : (Expression.eval env
          (var (F := F p) { index := i₀ + (m - 1) })).val < 2 ^ (tb + 1) := by
        have h := hq_tight.2
        simpa only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] using h
      have hVas := vassum (B := B) (tb := tb) env V hNf htbB input_var.a input_var.modulus i₀
        _ _ ha_lim hn_lim hq_lim hr_lim ha_top hn_top hq_top heqSq_get heqQN_get hbound_m
      exact (MulMod.mulMod_soundness_core_wm_lazy (B := B) hp i₀ env
        input_var.a input_var.a input_var.modulus
        (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).1
        (MulMod.interpolatedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus
          (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
            (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)).1
        (input.a, input.a, input.modulus) h_input' ha_norm ha_norm hn_norm hq_tight.1 hr_tight.1
        heqSq_get heqQN_get (fun _ => h_eq_impl ⟨hVas.1, hVas.2⟩)).2
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
        NormalizeTight.Assumptions, NormalizeTight.Spec,
        GroupedEqV.circuit_assumptions_eq, GroupedEqV.circuit_spec_eq,
        GroupedEqV.Assumptions, EqViaCarries.Spec]
      obtain ⟨ha_norm, hn_norm, hab_ltT, hn_ltT, hn_pos, hn_ge⟩ := h_assumptions
      have hn_big : 2 ^ (2 * ((m - 1) * B + tb)) ≤ BigInt.value B input.modulus * 2 ^ (B * m) :=
        MulMod.hn_big_of_ge hB1 htb.1 htbB hn_ge
      obtain ⟨hq_env, hr_env, hSq_uses, hQN_uses⟩ := h_env
      have h_pvSq := MulMod.interpolatedMul_usesLocalWitnesses (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1))) input_var.a input_var.a env rfl hSq_uses
      have h_pvQN := MulMod.interpolatedMul_usesLocalWitnesses
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
          (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)
        (Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2
          + (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1))))
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus env
        (Nat.add_comm _ _) hQN_uses
      have heva : evalValue B env input_var.a = BigInt.value B input.a := by
        rw [evalValue, BigInt.value, ← h_input]
      have hevn : evalValue B env input_var.modulus = BigInt.value B input.modulus := by
        rw [evalValue, BigInt.value, ← h_input]
      have hqwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + i.val)
          = ((BigInt.value B input.a * BigInt.value B input.a / BigInt.value B input.modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hq_env i, Vector.getElem_ofFn, heva, hevn]
      have hrwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + m + i.val)
          = ((BigInt.value B input.a * BigInt.value B input.a % BigInt.value B input.modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hr_env i, Vector.getElem_ofFn, heva, hevn]
      have h_input' : (Vector.map (Expression.eval env.toEnvironment) input_var.a,
          Vector.map (Expression.eval env.toEnvironment) input_var.a,
          Vector.map (Expression.eval env.toEnvironment) input_var.modulus)
            = ((input.a, input.a, input.modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [← h_input]
      have heqSq_get := MulMod.interpolatedMul_eval_bridge_uses env.toEnvironment
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1))) input_var.a input_var.a h_pvSq
      have heqQN_get := MulMod.interpolatedMul_eval_bridge_uses env.toEnvironment
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
          (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus h_pvQN
      have core := MulMod.mulMod_completeness_core_wm_lazy (B := B) (tb := tb) hB
        (Nat.le_of_succ_le htbB) hp i₀ env.toEnvironment
        input_var.a input_var.a input_var.modulus
        (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).1
        (MulMod.interpolatedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus
          (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
            (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)).1
        (input.a, input.a, input.modulus) h_input' ha_norm ha_norm hn_norm
        hab_ltT hab_ltT hn_ltT hn_pos hn_big hqwit hrwit heqSq_get heqQN_get
      have hqtight := MulMod.qwit_tight (B := B) (tb := tb) (tq := tb + 1) hB htb.1 htbB
        (by omega) i₀ env.toEnvironment
        (BigInt.value B input.a) (BigInt.value B input.a) (BigInt.value B input.modulus)
        hab_ltT hab_ltT hn_ge hqwit
      -- per-position coefficient bounds for the graduated equality
      have hmapa : Vector.map (Expression.eval env.toEnvironment) input_var.a = input.a :=
        congrArg SquareModLazy.Inputs.a h_input
      have hmapn : Vector.map (Expression.eval env.toEnvironment) input_var.modulus = input.modulus :=
        congrArg SquareModLazy.Inputs.modulus h_input
      have ha_lim : ∀ i : Fin m, (Expression.eval env.toEnvironment (input_var.a[i.val]'i.isLt)).val < 2 ^ B := by
        intro i
        have hel : Expression.eval env.toEnvironment (input_var.a[i.val]'i.isLt) = input.a[i.val]'i.isLt := by
          rw [← hmapa, Vector.getElem_map]
        rw [hel]; exact ha_norm i
      have hn_lim : ∀ i : Fin m, (Expression.eval env.toEnvironment (input_var.modulus[i.val]'i.isLt)).val < 2 ^ B := by
        intro i
        have hel : Expression.eval env.toEnvironment (input_var.modulus[i.val]'i.isLt) = input.modulus[i.val]'i.isLt := by
          rw [← hmapn, Vector.getElem_map]
        rw [hel]; exact hn_norm i
      have hq_lim : ∀ i : Fin m, (Expression.eval env.toEnvironment
          (var (F := F p) { index := i₀ + i.val })).val < 2 ^ B := by
        intro i
        have h := core.1 i
        simpa only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] using h
      have hr_lim : ∀ i : Fin m, (Expression.eval env.toEnvironment
          (var (F := F p) { index := i₀ + m + i.val })).val < 2 ^ B := by
        intro i
        have h := core.2.1.1 i
        simpa only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] using h
      have hbound_m : m * (2 ^ B * 2 ^ B) < p := by
        have h2B : (2 : ℕ) ^ B * 2 ^ B = 2 ^ (2 * B) := by rw [two_mul, pow_add]
        rw [h2B]
        calc m * 2 ^ (2 * B) = 2 ^ (2 * B) * m := by ring
          _ ≤ 2 ^ (2 * B) * (m + 1) := by
              exact Nat.mul_le_mul_left _ (by omega)
          _ < 2 ^ (2 * B) * (m + 1) * 4 := by
              have hpos : 0 < 2 ^ (2 * B) * (m + 1) := by positivity
              omega
          _ < p := hp
      have ha_top : (Expression.eval env.toEnvironment
          (input_var.a[m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tb := by
        have hel : Expression.eval env.toEnvironment
            (input_var.a[m - 1]'(by have := Nat.pos_of_neZero m; omega))
              = input.a[m - 1]'(by have := Nat.pos_of_neZero m; omega) := by
          rw [← hmapa, Vector.getElem_map]
        rw [hel]
        exact GroupedEqV.top_limb_lt_of_value_lt hab_ltT
      have hn_top : (Expression.eval env.toEnvironment
          (input_var.modulus[m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tb := by
        have hel : Expression.eval env.toEnvironment
            (input_var.modulus[m - 1]'(by have := Nat.pos_of_neZero m; omega))
              = input.modulus[m - 1]'(by have := Nat.pos_of_neZero m; omega) := by
          rw [← hmapn, Vector.getElem_map]
        rw [hel]
        exact GroupedEqV.top_limb_lt_of_value_lt hn_ltT
      have hq_top : (Expression.eval env.toEnvironment
          (var (F := F p) { index := i₀ + (m - 1) })).val < 2 ^ (tb + 1) := by
        have h := hqtight.2
        simpa only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] using h
      have hVas := vassum (B := B) (tb := tb) env.toEnvironment V hNf htbB
        input_var.a input_var.modulus i₀
        _ _ ha_lim hn_lim hq_lim hr_lim ha_top hn_top hq_top heqSq_get heqQN_get hbound_m
      exact ⟨hqtight, core.2.1,
        MulMod.interpolatedMul_completeness (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 1 - 1)) + ((m - 1) * (B - 1) + (tb - 1))) input_var.a input_var.a env h_pvSq,
        MulMod.interpolatedMul_completeness _ (Vector.mapRange m fun i => var { index := i₀ + i })
          input_var.modulus env h_pvQN,
        ⟨hVas.1, hVas.2⟩, core.2.2.2⟩

end SquareModLazyG

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
