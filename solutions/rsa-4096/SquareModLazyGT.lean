import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulMod
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.SquareModLazy
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.SquareModLazyG
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.WindowCaps

/-!
# Tight first squaring with graduated grouped equality (gadget G5′-lazy-V-T)

`SquareModLazyGT` is `SquareModLazyG` with the quotient range-checked one bit
tighter (top limb `tb`, not `tb+1`), using the extra assumption `a < n`
available for the first squaring of the chain.

`SquareModLazyG` is `SquareModLazy` with the per-index `EqViaCarries` equality
replaced by a graduated grouped assertion: here the **two-sided variable-group**
`GroupedEqXV` (per-group size schedule `gf`/`posOf`, `G` groups,
position-dependent carry widths `V.Wf`, asymmetric per-side offsets
`V.OFFf`/`VR.OFFf`): only `G − 2` carries are witnessed/range-checked, each at
its own tent-shaped width, plus one final `polyEval` row. Everything else
(interpolated `a·a` and `q·n` products, tight-normalized quotient and remainder)
is unchanged; the same `MulMod` arithmetic cores are reused because `GroupedEqXV`
certifies the same `polyValue` equality. The per-position coefficient bounds
demanded by `GroupedEqXV.Assumptions` are discharged from the top-limb-aware
window convolution bound (`WindowCaps.val_bigIntMulNoReduce_coeff_le_wconv`).
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

namespace SquareModLazyGT

variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

/-- `2m-1` is nonzero whenever `m` is (needed for the length-generic
`GroupedEqXV` equality over the `2m-1` convolution coefficients). -/
instance : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩

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
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgvx : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
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

  NormalizeTight.circuit P tb htb (Nat.le_of_succ_le htbB) q
  NormalizeTight.circuit P tb htb (Nat.le_of_succ_le htbB) r

  let Pc ← MulMod.interpolatedMul a a
  let Sqn ← MulMod.interpolatedMul q n
  let S : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then Sqn[k.val] + r[k.val]'h else Sqn[k.val]

  GroupedEqXV.circuit (L := 2 * m - 1) P.B gf posOf G V VR hgvx P.hB1 { lhs := Pc, rhs := S }
  return r

instance elaborated (P : BigIntParams p m) (tb : ℕ) (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htbB : tb + 1 ≤ P.B)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgvx : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) (BigInt m) (main P tb htb htbB gf posOf G V VR hgvx) where
  localLength _ :=
    m + m + ((m - 1) * (P.B - 1) + (tb - 1)) + ((m - 1) * (P.B - 1) + (tb - 1))
      + (2 * m - 1) + (2 * m - 1)
      + GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0
  output _ i0 := varFromOffset (BigInt m) (i0 + m)
  localLength_eq := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, circuit_norm, Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, GroupedEqXV.circuit, GroupedEqXV.elaborated, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]
    omega
  output_eq := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, circuit_norm, Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, GroupedEqXV.circuit, GroupedEqXV.elaborated, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, MulMod.interpolatedMul, circuit_norm, Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, GroupedEqXV.circuit, GroupedEqXV.elaborated, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, circuit_norm, Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, GroupedEqXV.circuit, GroupedEqXV.elaborated, RangeCheck.circuit,
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
    2 ^ ((m - 1) * B + tb - 1) ≤ n.value B ∧
    a.value B < n.value B

/-- Verifier-side assumptions for the tight-quotient square. The circuit itself
only needs the usual lazy-square bounds for soundness; `a < n` is needed only to
make the honest quotient fit the tighter witness range. -/
def SoundAssumptions (B tb : ℕ) (input : Inputs m (F p)) : Prop :=
  SquareModLazyG.Assumptions B tb input

/-- Postcondition: the output is tight-normalized and **congruent** to `a·a` mod `n`. -/
def Spec (B tb : ℕ) (input : Inputs m (F p)) (out : BigInt m (F p)) : Prop :=
  let a := input.a
  let n := input.modulus
  BigInt.NormalizedTight B tb out ∧ out.value B % n.value B = (a.value B * a.value B) % n.value B

/-- Honest-prover side fact for the tight square: the witness generator returns
the canonical remainder, so the output is strictly below the modulus. -/
def ProverSpec (B : ℕ) (input : Inputs m (F p)) (out : BigInt m (F p)) : Prop :=
  out.value B < input.modulus.value B

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

/-- Adequacy of the two-sided graduated coefficient-bound functions for the
tight squaring step: `V.Nf` dominates the top-limb-aware square window sum
(lhs, `a·a` with `tb`-bit top limbs), and `VR.Nf` dominates the same window sum
for `q·n` (the tight quotient also carries a `tb`-bit top limb) plus one tight
`r`-limb (`limbCap`: full `B` bits below the top, `tb` bits at the top) on the
low positions. -/
def NfOk2 (B tb : ℕ) (V VR : GroupedEqV.VParams) : Prop :=
  (∀ j, j < 2 * m - 1 → WindowCaps.sqCapW B tb m j < V.Nf j) ∧
  (∀ j, j < 2 * m - 1 →
    WindowCaps.wconv m m (WindowCaps.limbCap B tb m) (WindowCaps.limbCap B tb m) j
      + (if j < m then WindowCaps.limbCap B tb m j else 0) < VR.Nf j)

/-- Discharge `GroupedEqXV.Assumptions` for the tight squaring step: the
witnessed product coefficients equal top-limb-aware window-bounded convolutions
(via the interpolation bridges), and the rhs adds one tight `r`-limb per low
position. -/
private lemma vassum {B tb : ℕ} (env : Environment (F p)) (V VR : GroupedEqV.VParams)
    (hNf : NfOk2 (m := m) B tb V VR)
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
      (var (F := F p) { index := i₀ + (m - 1) })).val < 2 ^ tb)
    (hr_top : (Expression.eval env
      (var (F := F p) { index := i₀ + m + (m - 1) })).val < 2 ^ tb)
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
        < VR.Nf k.val) := by
  have hm := Nat.pos_of_neZero m
  have hqvec : ∀ i : Fin m, (Expression.eval env
      ((Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i })[i.val])).val < 2 ^ B := by
    intro i
    have hgi : (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i })[i.val]
        = var { index := i₀ + i.val } := by simp [circuit_norm]
    rw [hgi]; exact hq i
  have hqvec_top : (Expression.eval env
      ((Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i })[m - 1]'(by omega))).val
        < 2 ^ tb := by
    have hgi : (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i })[m - 1]'(by omega)
        = var { index := i₀ + (m - 1) } := by simp [circuit_norm]
    rw [hgi]; exact hq_top
  have ha_cap := WindowCaps.limb_caps_of_top (B := B) (tw := tb) env a ha ha_top
  have hn_cap := WindowCaps.limb_caps_of_top (B := B) (tw := tb) env n hn hn_top
  have hq_cap := WindowCaps.limb_caps_of_top (B := B) (tw := tb) env
    (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }) hqvec hqvec_top
  constructor
  · intro k
    rw [heqP k]
    have h1 := WindowCaps.val_bigIntMulNoReduce_coeff_le_wconv (B := B) env a a k
      (WindowCaps.limbCap B tb m) (WindowCaps.limbCap B tb m) ha ha ha_cap ha_cap hbound
    have h2 := hNf.1 k.val k.isLt
    exact lt_of_le_of_lt h1 h2
  · intro k
    have h1 := WindowCaps.val_bigIntMulNoReduce_coeff_le_wconv (B := B) env
      (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n k
      (WindowCaps.limbCap B tb m) (WindowCaps.limbCap B tb m) hqvec hn hq_cap hn_cap hbound
    have h2 := hNf.2 k.val k.isLt
    by_cases h : k.val < m
    · rw [dif_pos h]
      rw [if_pos h] at h2
      have hadd : (Expression.eval env (Qv[k.val] + var { index := i₀ + m + k.val })).val
          ≤ (Expression.eval env Qv[k.val]).val
            + (Expression.eval env (var (F := F p) { index := i₀ + m + k.val })).val := by
        rw [show Expression.eval env (Qv[k.val] + var { index := i₀ + m + k.val })
            = Expression.eval env Qv[k.val]
              + Expression.eval env (var (F := F p) { index := i₀ + m + k.val }) from by
          simp [Expression.eval]]
        rw [ZMod.val_add]
        exact Nat.mod_le _ _
      have h3 : (Expression.eval env (var (F := F p) { index := i₀ + m + k.val })).val
          ≤ WindowCaps.limbCap B tb m k.val := by
        unfold WindowCaps.limbCap
        by_cases hk : k.val = m - 1
        · rw [if_pos hk]
          have heq : (var (F := F p) { index := i₀ + m + k.val })
              = var (F := F p) { index := i₀ + m + (m - 1) } := by rw [hk]
          rw [heq]
          omega
        · rw [if_neg hk]
          have h4 : (Expression.eval env
              (var (F := F p) { index := i₀ + m + k.val })).val < 2 ^ B := hr ⟨k.val, h⟩
          omega
      rw [heqQ k] at hadd
      omega
    · rw [dif_neg h]
      rw [if_neg h] at h2
      rw [heqQ k]
      omega

set_option maxHeartbeats 8000000 in
/-- The `SquareModLazy` formal circuit with graduated carries: `c ≡ a · a (mod n)`
over normalized big integers, with `c` tight-normalized (`< 2^((m-1)B+tb)`). -/
def circuit (P : BigIntParams p m) (tb : ℕ) (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htbB : tb + 1 ≤ P.B)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgvx : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : NfOk2 (m := m) P.B tb V VR) [Fact (p > 2)] :
    FormalCircuit (F p) (Inputs m) (BigInt m) where
    main := main P tb htb htbB gf posOf G V VR hgvx
    Assumptions := Assumptions P.B tb
    Spec := Spec P.B tb
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
        NormalizeTight.Assumptions, NormalizeTight.Spec,
        GroupedEqXV.circuit_assumptions_eq, GroupedEqXV.circuit_spec_eq,
        GroupedEqXV.Assumptions, GroupedEqX.Spec]
      obtain ⟨ha_norm, hn_norm, hab_ltT, hn_ltT, hn_pos, hn_ge, ha_lt_n⟩ := h_assumptions
      obtain ⟨hq_tight, hr_tight, hSq_ops, hQN_ops, h_eq_impl⟩ := h_holds
      have hpm : 2 * m - 1 < p := MulMod.two_m_sub_one_lt hp
      have h_pSq := MulMod.interpolatedMul_soundness (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)))
        input_var.a input_var.a env hSq_ops
      have h_pQN := MulMod.interpolatedMul_soundness
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
          (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus env hQN_ops
      refine ⟨⟨hr_tight, ?_⟩, MulMod.interpolatedMul_requirements _ _ _ _,
        MulMod.interpolatedMul_requirements _ _ _ _,
        Or.inl (GroupedEqXV.circuit_channels_req_eq _ _ _ _ _ _ _ _)⟩
      have h_input' : (Vector.map (Expression.eval env) input_var.a,
          Vector.map (Expression.eval env) input_var.a,
          Vector.map (Expression.eval env) input_var.modulus)
            = ((input.a, input.a, input.modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [← h_input]
      have heqSq_get := MulMod.interpolatedMul_eval_bridge env (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)))
        input_var.a input_var.a hpm h_pSq
      have heqQN_get := MulMod.interpolatedMul_eval_bridge env
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
          (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)
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
          (var (F := F p) { index := i₀ + (m - 1) })).val < 2 ^ tb := by
        have h := hq_tight.2
        simpa only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] using h
      have hr_top : (Expression.eval env
          (var (F := F p) { index := i₀ + m + (m - 1) })).val < 2 ^ tb := by
        have h := hr_tight.2
        simpa only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] using h
      have hVas := vassum (B := B) (tb := tb) env V VR hNf input_var.a input_var.modulus i₀
        _ _ ha_lim hn_lim hq_lim hr_lim ha_top hn_top hq_top hr_top heqSq_get heqQN_get hbound_m
      exact (MulMod.mulMod_soundness_core_wm_lazy (B := B) hp i₀ env
        input_var.a input_var.a input_var.modulus
        (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).1
        (MulMod.interpolatedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus
          (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
            (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)).1
        (input.a, input.a, input.modulus) h_input' ha_norm ha_norm hn_norm hq_tight.1 hr_tight.1
        heqSq_get heqQN_get (fun _ => h_eq_impl ⟨hVas.1, hVas.2⟩)).2
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
        NormalizeTight.Assumptions, NormalizeTight.Spec,
        GroupedEqXV.circuit_assumptions_eq, GroupedEqXV.circuit_spec_eq,
        GroupedEqXV.Assumptions, GroupedEqX.Spec]
      obtain ⟨ha_norm, hn_norm, hab_ltT, hn_ltT, hn_pos, hn_ge, ha_lt_n⟩ := h_assumptions
      have hn_big : 2 ^ (2 * ((m - 1) * B + tb)) ≤ BigInt.value B input.modulus * 2 ^ (B * m) :=
        MulMod.hn_big_of_ge hB1 htb.1 htbB hn_ge
      obtain ⟨hq_env, hr_env, hSq_uses, hQN_uses⟩ := h_env
      have h_pvSq := MulMod.interpolatedMul_usesLocalWitnesses (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)))
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1))) input_var.a input_var.a env rfl hSq_uses
      have h_pvQN := MulMod.interpolatedMul_usesLocalWitnesses
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
          (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)
        (Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2
          + (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1))))
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
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1))) input_var.a input_var.a h_pvSq
      have heqQN_get := MulMod.interpolatedMul_eval_bridge_uses env.toEnvironment
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
          (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus h_pvQN
      have core := MulMod.mulMod_completeness_core_wm_lazy (B := B) (tb := tb) hB
        (Nat.le_of_succ_le htbB) hp i₀ env.toEnvironment
        input_var.a input_var.a input_var.modulus
        (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).1
        (MulMod.interpolatedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus
          (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
            (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)).1
        (input.a, input.a, input.modulus) h_input' ha_norm ha_norm hn_norm
        hab_ltT hab_ltT hn_ltT hn_pos hn_big hqwit hrwit heqSq_get heqQN_get
      have hqtight := MulMod.qwit_tight_lt (B := B) (tb := tb) (tq := tb) hB
        (Nat.le_of_succ_le htbB) (le_refl tb) i₀ env.toEnvironment
        (BigInt.value B input.a) (BigInt.value B input.a) (BigInt.value B input.modulus)
        hab_ltT ha_lt_n hqwit
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
          (var (F := F p) { index := i₀ + (m - 1) })).val < 2 ^ tb := by
        have h := hqtight.2
        simpa only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] using h
      have hr_top : (Expression.eval env.toEnvironment
          (var (F := F p) { index := i₀ + m + (m - 1) })).val < 2 ^ tb := by
        have h := core.2.1.2
        simpa only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] using h
      have hVas := vassum (B := B) (tb := tb) env.toEnvironment V VR hNf
        input_var.a input_var.modulus i₀
        _ _ ha_lim hn_lim hq_lim hr_lim ha_top hn_top hq_top hr_top heqSq_get heqQN_get hbound_m
      exact ⟨hqtight, core.2.1,
        MulMod.interpolatedMul_completeness (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1))) input_var.a input_var.a env h_pvSq,
        MulMod.interpolatedMul_completeness _ (Vector.mapRange m fun i => var { index := i₀ + i })
          input_var.modulus env h_pvQN,
        ⟨hVas.1, hVas.2⟩, core.2.2.2⟩

private lemma prover_output_lt (P : BigIntParams p m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htbB : tb + 1 ≤ P.B)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgvx : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    [Fact (p > 2)]
    (i₀ : ℕ) (env : ProverEnvironment (F p)) (input_var : Var (Inputs m) (F p))
    (input : Inputs m (F p))
    (h_input : eval env input_var = input)
    (h_assumptions : Assumptions P.B tb input)
    (h_env : env.UsesLocalWitnessesCompleteness i₀
      ((main P tb htb htbB gf posOf G V VR hgvx input_var).operations i₀)) :
    ProverSpec P.B input
      (eval env ((main P tb htb htbB gf posOf G V VR hgvx input_var).output i₀)) := by
  obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
  simp only [ProverSpec]
  obtain ⟨ha_norm, hn_norm, hab_ltT, hn_ltT, hn_pos, hn_ge, ha_lt_n⟩ := h_assumptions
  simp only [main, MulMod.interpolatedMul, circuit_norm, Normalize.circuit,
    Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
    NormalizeTight.main, GroupedEqXV.circuit, GroupedEqXV.elaborated, RangeCheck.circuit,
    Gadgets.ToBits.rangeCheck] at h_env ⊢
  obtain ⟨hq_env, hr_env, hSq_uses, hQN_uses⟩ := h_env
  change tb + 1 ≤ B at htbB
  have h_input_toEnv : eval env.toEnvironment input_var = input := by
    have h_eval_eq : eval env input_var = eval env.toEnvironment input_var :=
      CircuitType.eval_var_prover_to_verifier env input_var
    rwa [← h_eval_eq]
  have h_eval_a : (eval env.toEnvironment input_var).a =
      Vector.map (Expression.eval env.toEnvironment) input_var.a := by
    rw [ProvableStruct.eval_eq_eval]
    simp only [ProvableStruct.eval, SquareModLazy.instProvableStructInputs,
      ProvableStruct.eval.go]
    rw [CircuitType.eval_var_fields]
  have h_eval_n : (eval env.toEnvironment input_var).modulus =
      Vector.map (Expression.eval env.toEnvironment) input_var.modulus := by
    rw [ProvableStruct.eval_eq_eval]
    simp only [ProvableStruct.eval, SquareModLazy.instProvableStructInputs,
      ProvableStruct.eval.go]
    rw [CircuitType.eval_var_fields]
  have hmapa : Vector.map (Expression.eval env.toEnvironment) input_var.a = input.a := by
    rw [← h_eval_a, h_input_toEnv]
  have hmapn : Vector.map (Expression.eval env.toEnvironment) input_var.modulus = input.modulus := by
    rw [← h_eval_n, h_input_toEnv]
  have heva : evalValue B env input_var.a = BigInt.value B input.a := by
    rw [evalValue, BigInt.value, hmapa]
  have hevn : evalValue B env input_var.modulus = BigInt.value B input.modulus := by
    rw [evalValue, BigInt.value, hmapn]
  set rval := BigInt.value B input.a * BigInt.value B input.a % BigInt.value B input.modulus with hrval
  have hrwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + m + i.val)
      = ((rval / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
    intro i
    rw [hr_env i, Vector.getElem_ofFn, heva, hevn, hrval]
  have hTle : (m - 1) * B + tb ≤ B * m := by
    have htbB' : tb ≤ B := Nat.le_of_succ_le htbB
    have hm : 0 < m := Nat.pos_of_neZero m
    calc (m - 1) * B + tb ≤ (m - 1) * B + B := by omega
      _ = ((m - 1) + 1) * B := by ring
      _ = m * B := by rw [Nat.sub_add_cancel hm]
      _ = B * m := Nat.mul_comm _ _
  have hrval_lt : rval < 2 ^ (B * m) := by
    calc rval < BigInt.value B input.modulus := by
          rw [hrval]
          exact Nat.mod_lt _ hn_pos
      _ < 2 ^ ((m - 1) * B + tb) := hn_ltT
      _ ≤ 2 ^ (B * m) := Nat.pow_le_pow_right (by norm_num) hTle
  have hvalue : BigInt.value B
      (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i })) = rval := by
    exact BigInt.value_mapRange (i₀ + m) rval env.toEnvironment hB hrval_lt hrwit
  rw [hvalue, hrval]
  exact Nat.mod_lt _ hn_pos

set_option maxHeartbeats 8000000 in
/-- General version of `SquareModLazyGT`: soundness only needs the usual lazy
square assumptions, while completeness assumes `a < n` and exposes the honest
fact that the produced remainder is canonical. -/
def generalCircuit (P : BigIntParams p m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htbB : tb + 1 ≤ P.B)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgvx : GroupedEqXV.GVXHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : NfOk2 (m := m) P.B tb V VR) [Fact (p > 2)] :
    GeneralFormalCircuit (F p) (Inputs m) (BigInt m) where
  main := main P tb htb htbB gf posOf G V VR hgvx
  Assumptions := fun input _ => SoundAssumptions P.B tb input
  Spec := fun input out _ => Spec P.B tb input out
  ProverAssumptions := fun input _ _ => Assumptions P.B tb input
  ProverSpec := fun input out _ => ProverSpec P.B input out
  soundness := by
    obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
    circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
      Normalize.Assumptions, Normalize.Spec,
      NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      NormalizeTight.Assumptions, NormalizeTight.Spec,
      GroupedEqXV.circuit_assumptions_eq, GroupedEqXV.circuit_spec_eq,
      GroupedEqXV.Assumptions, GroupedEqX.Spec]
    obtain ⟨ha_norm, hn_norm, hab_ltT, hn_ltT, hn_pos, hn_ge⟩ := h_assumptions
    obtain ⟨hq_tight, hr_tight, hSq_ops, hQN_ops, h_eq_impl⟩ := h_holds
    have hpm : 2 * m - 1 < p := MulMod.two_m_sub_one_lt hp
    have h_pSq := MulMod.interpolatedMul_soundness (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)))
      input_var.a input_var.a env hSq_ops
    have h_pQN := MulMod.interpolatedMul_soundness
      (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
        (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)
      (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus env hQN_ops
    refine ⟨⟨hr_tight, ?_⟩, MulMod.interpolatedMul_requirements _ _ _ _,
      MulMod.interpolatedMul_requirements _ _ _ _,
      Or.inl (GroupedEqXV.circuit_channels_req_eq _ _ _ _ _ _ _ _)⟩
    have h_input' : (Vector.map (Expression.eval env) input_var.a,
        Vector.map (Expression.eval env) input_var.a,
        Vector.map (Expression.eval env) input_var.modulus)
          = ((input.a, input.a, input.modulus) :
            ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
      simp only [← h_input]
    have heqSq_get := MulMod.interpolatedMul_eval_bridge env (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)))
      input_var.a input_var.a hpm h_pSq
    have heqQN_get := MulMod.interpolatedMul_eval_bridge env
      (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
        (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)
      (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus hpm h_pQN
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
        (var (F := F p) { index := i₀ + (m - 1) })).val < 2 ^ tb := by
      have h := hq_tight.2
      simpa only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] using h
    have hr_top : (Expression.eval env
        (var (F := F p) { index := i₀ + m + (m - 1) })).val < 2 ^ tb := by
      have h := hr_tight.2
      simpa only [Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange] using h
    have hVas := vassum (B := B) (tb := tb) env V VR hNf input_var.a input_var.modulus i₀
      _ _ ha_lim hn_lim hq_lim hr_lim ha_top hn_top hq_top hr_top heqSq_get heqQN_get hbound_m
    exact (MulMod.mulMod_soundness_core_wm_lazy (B := B) hp i₀ env
      input_var.a input_var.a input_var.modulus
      (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).1
      (MulMod.interpolatedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
          (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)).1
      (input.a, input.a, input.modulus) h_input' ha_norm ha_norm hn_norm hq_tight.1 hr_tight.1
      heqSq_get heqQN_get (fun _ => h_eq_impl ⟨hVas.1, hVas.2⟩)).2
  completeness := by
    intro i₀ env input_var h_env input h_input h_assumptions
    constructor
    · exact (circuit P tb htb htbB gf posOf G V VR hgvx hNf).completeness i₀ env input_var
        h_env input h_input h_assumptions
    · exact prover_output_lt P tb htb htbB gf posOf G V VR hgvx i₀ env input_var input
        h_input h_assumptions h_env

end SquareModLazyGT

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
