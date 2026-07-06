import Solution.RSASSAPKCS1v15_SHA256_4096_65537.SqMulModTo
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.SquareModBalGT
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.GroupedEqDCost

/-!
# Balanced fused square-multiply-mod equality (`SqMulModBalTo`)

`SqMulModBalTo` is `SqMulModTo` with a *balanced* signed-digit multiplicand
`a = r_15`: the inner square `z1 = interpolatedMul aS aS` is built from the
shifted operand `aS` (so `z1` carries the signed convolution of the balanced
digits of `a`), the coefficient evaluations feed the two-sided window grouped
equality `GroupedEqD`, and the recovered identity is over ℤ:

    VZ(a)² · b.value = q.value · n.value + em.value.

Under `em < n` this pins `em.value ≡ VZ(a)² · b.value (mod n)`. The quotient
`q`, `b`, `n`, `em` stay unsigned/unchanged.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537

open Specs.RSA

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace SqMulModBalTo

open MulModTo (InputsTo)
open SqMulModTo (lhsPadVec rhsSVec)

/-- The definitional-top rhs vector of the fused step: witnessed low `q·n`
cells plus `em`'s limbs on the low `m` positions; the top entry is a dummy `0`
(replaced inside `GroupedEqD.circuitD` by the affine reconstruction). -/
def rhsSVecD (z3Low : Vector (Expression (F p)) ((2 * m) + m - 2))
    (em : Var (BigInt m) (F p)) : Vector (Expression (F p)) (2 * m + m - 1) :=
  Vector.mapFinRange (2 * m + m - 1) fun k =>
    if hlow : k.val < (2 * m) + m - 2 then
      (if hm : k.val < m then z3Low[k.val]'hlow + em[k.val]'hm else z3Low[k.val]'hlow)
    else 0

/-- The spliced `q·n` coefficient vector fed to the point-row assertion: the
witnessed low cells with the top coefficient replaced by the affine
reconstruction `topExprD` of the equality's deleted final row. -/
def z3VecD (XB : ℕ) (lhsPad : Vector (Expression (F p)) (2 * m + m - 1))
    (z3Low : Vector (Expression (F p)) ((2 * m) + m - 2))
    (em : Var (BigInt m) (F p)) : Vector (Expression (F p)) (2 * m + m - 1) :=
  Vector.mapFinRange (2 * m + m - 1) fun k =>
    if hlow : k.val < (2 * m) + m - 2 then z3Low[k.val]'hlow
    else GroupedEqXV.topExprD (L := 2 * m + m - 1) XB lhsPad (rhsSVecD z3Low em)

lemma rhsSVecD_getElem_low (z3Low : Vector (Expression (F p)) ((2 * m) + m - 2))
    (em : Var (BigInt m) (F p)) (k : ℕ) (hk : k < (2 * m) + m - 2) :
    (rhsSVecD z3Low em)[k]'(by omega)
      = (if hm : k < m then z3Low[k]'hk + em[k]'hm else z3Low[k]'hk) := by
  unfold rhsSVecD
  rw [Vector.getElem_mapFinRange]
  simp only [dif_pos hk]

lemma z3VecD_getElem_low (XB : ℕ) (lhsPad : Vector (Expression (F p)) (2 * m + m - 1))
    (z3Low : Vector (Expression (F p)) ((2 * m) + m - 2))
    (em : Var (BigInt m) (F p)) (k : ℕ) (hk : k < (2 * m) + m - 2) :
    (z3VecD XB lhsPad z3Low em)[k]'(by omega) = z3Low[k]'hk := by
  unfold z3VecD
  rw [Vector.getElem_mapFinRange]
  simp only [dif_pos hk]

lemma z3VecD_getElem_top (XB : ℕ) (lhsPad : Vector (Expression (F p)) (2 * m + m - 1))
    (z3Low : Vector (Expression (F p)) ((2 * m) + m - 2))
    (em : Var (BigInt m) (F p)) :
    (z3VecD XB lhsPad z3Low em)[2 * m + m - 1 - 1]'(by have := Nat.pos_of_neZero m; omega)
      = GroupedEqXV.topExprD (L := 2 * m + m - 1) XB lhsPad (rhsSVecD z3Low em) := by
  unfold z3VecD
  rw [Vector.getElem_mapFinRange]
  simp only [dif_neg (by omega : ¬ (2 * m + m - 1 - 1 < (2 * m) + m - 2))]

lemma lhsPadVec_getElem (Z2 : Vector (Expression (F p)) ((2 * m - 1) + m - 1))
    (k : ℕ) (hk : k < 2 * m + m - 1) :
    (lhsPadVec Z2)[k]'hk = (if h : k < (2 * m - 1) + m - 1 then Z2[k]'h else 0) := by
  unfold lhsPadVec
  rw [Vector.getElem_mapFinRange]

/-- The `main` circuit: witness `q = VZ(a)²·b/n` over `2m` limbs, tight-normalize
it, build `z1 = (aS)²` (signed), `z2 = z1·b`, `z3 = q·n`, and assert
`z2 = q·n + em` in base `2^B` via `GroupedEqD`. -/
def main (P : BigIntParams p m) (P2 : BigIntParams p (2 * m)) (XB tw : ℕ)
    (tq : ℕ) (htq : 1 ≤ tq ∧ 2 ^ tq < p) (htqB : tq ≤ P2.B) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m + m - 1) XB gf posOf G V VR) (hXB1 : 1 ≤ XB)
    (hB2 : P2.B = P.B) (hXB : XB = P.B) [Fact (p > 2)]
    (input : Var (InputsTo m) (F p)) : Circuit (F p) Unit := do
  let a := input.a
  let b := input.b
  let n := input.modulus
  let em := input.em

  let q ← ProvableType.witness (α := BigInt (2 * m)) fun env =>
    let vN := MulMod.evalValue P.B env a - BalancedZ.balShift P.B m
    let prod := vN * vN * MulMod.evalValue P.B env b
    let qval : ℕ := prod / MulMod.evalValue P.B env n
    Vector.ofFn fun k : Fin (2 * m) => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  NormalizeTight.circuit P2 tq htq htqB q

  let aS := SquareModBalGT.shiftedA P.B a
  let z1 ← MulMod.interpolatedMul aS aS
  let z2 ← MulMod.interpolatedMulX z1 b
  let z3Low ← ProvableType.witness (α := fields ((2 * m) + m - 2)) fun env =>
    Vector.ofFn fun k : Fin ((2 * m) + m - 2) =>
      Expression.eval env.toEnvironment
        ((MulMod.mulNoReduceX q n)[k.val]'(by have := k.isLt; omega))

  MulMod.interpolatedMulXAssert q n (z3VecD XB (lhsPadVec z2) z3Low em)
  GroupedEqD.circuitD (L := 2 * m + m - 1) XB gf posOf G V VR hgv hXB1
    { lhs := lhsPadVec z2, rhs := rhsSVecD z3Low em }

instance elaborated (P : BigIntParams p m) (P2 : BigIntParams p (2 * m)) (XB tw : ℕ)
    (tq : ℕ) (htq : 1 ≤ tq ∧ 2 ^ tq < p) (htqB : tq ≤ P2.B) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m + m - 1) XB gf posOf G V VR) (hXB1 : 1 ≤ XB)
    (hB2 : P2.B = P.B) (hXB : XB = P.B) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (InputsTo m) unit (main P P2 XB tw tq htq htqB gf posOf G V VR hgv hXB1 hB2 hXB) where
  localLength _ :=
    2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1))
      + ((2 * m - 1) + ((2 * m - 1) + m - 1) + ((2 * m) + m - 2))
      + GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0
  localLength_eq := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, MulMod.interpolatedMulX,
      MulMod.interpolatedMulXAssert, circuit_norm,
      NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      GroupedEqD.circuitD, GroupedEqD.elaboratedD, RangeCheck.circuit]
    omega
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, MulMod.interpolatedMul, MulMod.interpolatedMulX,
      MulMod.interpolatedMulXAssert, circuit_norm,
      NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      GroupedEqD.circuitD, GroupedEqD.elaboratedD, RangeCheck.circuit]
  channelsLawful := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, MulMod.interpolatedMulX,
      MulMod.interpolatedMulXAssert, circuit_norm,
      NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      GroupedEqD.circuitD, GroupedEqD.elaboratedD, RangeCheck.circuit]

/-- Preconditions: all four operands normalized; `a` balanced-window
(`< 2^((m-1)B+tw)`); `b < n`; `em < n`; `n` tight. -/
def Assumptions (B tb tw : ℕ) (input : InputsTo m (F p)) : Prop :=
  input.a.Normalized B ∧ input.b.Normalized B ∧ input.modulus.Normalized B ∧
    input.em.Normalized B ∧
    input.a.value B < 2 ^ ((m - 1) * B + tw) ∧
    input.b.value B < input.modulus.value B ∧
    input.em.value B < input.modulus.value B ∧
    input.modulus.value B < 2 ^ ((m - 1) * B + tb)

/-- Honest-prover assumptions: additionally `a` encodes a canonical residue. -/
def ProverAssumptions (B tb tw : ℕ) (input : InputsTo m (F p)) : Prop :=
  Assumptions B tb tw input ∧
    BalancedZ.balShift B m ≤ input.a.value B ∧
    input.a.value B - BalancedZ.balShift B m < input.modulus.value B ∧
    ((input.em.value B : ℤ) ≡
      BalancedZ.VZ B input.a * BalancedZ.VZ B input.a * (input.b.value B : ℤ)
        [ZMOD (input.modulus.value B : ℤ)])

/-- Postcondition: `em`'s value is congruent to `VZ(a)²·b` mod `n` (over ℤ). -/
def Spec (B : ℕ) (input : InputsTo m (F p)) : Prop :=
  (input.em.value B : ℤ) ≡
    BalancedZ.VZ B input.a * BalancedZ.VZ B input.a * (input.b.value B : ℤ)
      [ZMOD (input.modulus.value B : ℤ)]

/-! ## Digit families and the ℤ difference sum -/

/-- The signed inner-square family `z1 = (aS)²`. -/
def z1F (B : ℕ) (av : BigInt m (F p)) : ℕ → ℤ :=
  fun k => WindowCaps.zconv m m (BalancedZ.zdigits B av) (BalancedZ.zdigits B av) k

/-- The signed lhs (triple-product) family `z2 = z1·b`. -/
def lhsF (B : ℕ) (av bv : BigInt m (F p)) : ℕ → ℤ :=
  fun k => WindowCaps.zconv (2 * m - 1) m (z1F B av) (BalancedZ.udigits bv) k

/-- The rhs family `q·n + em`. -/
def rhsF (qv : BigInt (2 * m) (F p)) (nv emv : BigInt m (F p)) : ℕ → ℤ :=
  fun k => WindowCaps.zconv (2 * m) m (BalancedZ.udigits qv) (BalancedZ.udigits nv) k
    + (if k < m then BalancedZ.udigits emv k else 0)

/-- Padded lhs family (zero beyond `(2m-1)+m-1`). -/
def zlF (B : ℕ) (av bv : BigInt m (F p)) : ℕ → ℤ :=
  fun k => if k < (2 * m - 1) + m - 1 then lhsF B av bv k else 0

lemma abs_z1F_le {B tw : ℕ} (hB1 : 1 ≤ B) (hm : 1 ≤ m) (av : BigInt m (F p))
    (ha_norm : av.Normalized B) (ha_top : (av[m - 1]'(by omega)).val < 2 ^ tw) (k : ℕ) :
    |z1F B av k| ≤ (WindowCaps.wconv m m (WindowCaps.balCap B tw m) (WindowCaps.balCap B tw m) k : ℤ) := by
  have hza := BalancedZ.abs_zdigits_le hB1 hm av ha_norm ha_top
  exact WindowCaps.abs_zconv_le m m _ _ _ _ hza hza k

lemma abs_lhsF_le {B tb tw : ℕ} (hB1 : 1 ≤ B) (hm : 1 ≤ m) (av bv : BigInt m (F p))
    (ha_norm : av.Normalized B) (ha_top : (av[m - 1]'(by omega)).val < 2 ^ tw)
    (hb_norm : bv.Normalized B) (hb_top : (bv[m - 1]'(by omega)).val < 2 ^ tb) (k : ℕ) :
    |lhsF B av bv k| ≤ (WindowCaps.wconv (2 * m - 1) m
        (WindowCaps.wconv m m (WindowCaps.balCap B tw m) (WindowCaps.balCap B tw m))
        (WindowCaps.limbCap B tb m) k : ℤ) := by
  have hzb := BalancedZ.abs_udigits_le_limbCap hm bv hb_norm hb_top
  exact WindowCaps.abs_zconv_le (2 * m - 1) m _ _ _ _
    (abs_z1F_le hB1 hm av ha_norm ha_top) hzb k

lemma rhsF_nonneg (qv : BigInt (2 * m) (F p)) (nv emv : BigInt m (F p)) (k : ℕ) :
    0 ≤ rhsF qv nv emv k := by
  unfold rhsF
  have h1 := WindowCaps.zconv_nonneg (2 * m) m _ _
    (BalancedZ.udigits_nonneg qv) (BalancedZ.udigits_nonneg nv) k
  have h2 : (0 : ℤ) ≤ (if k < m then BalancedZ.udigits emv k else 0) := by
    split
    · exact BalancedZ.udigits_nonneg emv k
    · exact le_refl 0
  omega

lemma abs_rhsF_le {B tb tq : ℕ} (hm : 1 ≤ m)
    (qv : BigInt (2 * m) (F p)) (nv emv : BigInt m (F p))
    (hq_norm : qv.Normalized B) (hq_top : (qv[2 * m - 1]'(by omega)).val < 2 ^ tq)
    (hn_norm : nv.Normalized B) (hn_top : (nv[m - 1]'(by omega)).val < 2 ^ tb)
    (hem_norm : emv.Normalized B) (hem_top : (emv[m - 1]'(by omega)).val < 2 ^ tb) (k : ℕ) :
    rhsF qv nv emv k
      ≤ (WindowCaps.qnCapW B tb tq m k
          + (if k < m then WindowCaps.limbCap B tb m k else 0) : ℕ) := by
  unfold rhsF
  have hzq : ∀ i, |BalancedZ.udigits qv i| ≤ (WindowCaps.limbCap B tq (2 * m) i : ℤ) :=
    BalancedZ.abs_udigits_le_limbCap (by omega) qv hq_norm hq_top
  have hzn := BalancedZ.abs_udigits_le_limbCap hm nv hn_norm hn_top
  have hem := BalancedZ.abs_udigits_le_limbCap hm emv hem_norm hem_top
  have hqn := WindowCaps.abs_zconv_le (2 * m) m _ _ _ _ hzq hzn k
  have hqn0 := WindowCaps.zconv_nonneg (2 * m) m _ _
    (BalancedZ.udigits_nonneg qv) (BalancedZ.udigits_nonneg nv) k
  rw [abs_le] at hqn
  have hqW : WindowCaps.zconv (2 * m) m (BalancedZ.udigits qv) (BalancedZ.udigits nv) k
      ≤ WindowCaps.qnCapW B tb tq m k := by
    have : (WindowCaps.zconv (2 * m) m (BalancedZ.udigits qv) (BalancedZ.udigits nv) k : ℤ)
        ≤ (WindowCaps.wconv (2 * m) m (WindowCaps.limbCap B tq (2 * m)) (WindowCaps.limbCap B tb m) k : ℤ) :=
      hqn.2
    have h2 : (WindowCaps.wconv (2 * m) m (WindowCaps.limbCap B tq (2 * m)) (WindowCaps.limbCap B tb m) k)
        = WindowCaps.qnCapW B tb tq m k := rfl
    rw [h2] at this
    exact_mod_cast this
  by_cases hkm : k < m
  · rw [if_pos hkm, if_pos hkm]
    have hemk : BalancedZ.udigits emv k ≤ (WindowCaps.limbCap B tb m k : ℤ) := by
      have := (abs_le.mp (hem k)).2
      exact this
    have hnn : (0 : ℤ) ≤ BalancedZ.udigits emv k := BalancedZ.udigits_nonneg emv k
    push_cast
    have : (WindowCaps.zconv (2 * m) m (BalancedZ.udigits qv) (BalancedZ.udigits nv) k : ℤ)
        ≤ (WindowCaps.qnCapW B tb tq m k : ℤ) := by exact_mod_cast hqW
    omega
  · rw [if_neg hkm, if_neg hkm, Nat.add_zero]
    push_cast
    have : (WindowCaps.zconv (2 * m) m (BalancedZ.udigits qv) (BalancedZ.udigits nv) k : ℤ)
        ≤ (WindowCaps.qnCapW B tb tq m k : ℤ) := by exact_mod_cast hqW
    omega

/-- Base-`2^B` value of `z1F` is `VZ(a)²`. -/
lemma sum_z1F (B : ℕ) (hm : 1 ≤ m) (av : BigInt m (F p)) :
    (∑ k ∈ Finset.range (2 * m - 1), z1F B av k * 2 ^ (B * k))
      = BalancedZ.VZ B av * BalancedZ.VZ B av := by
  unfold z1F
  rw [BalancedZ.zconv_polyVal B m (BalancedZ.zdigits B av) (BalancedZ.zdigits B av),
    BalancedZ.sum_zdigits B hm av]

/-! ## The ℤ arithmetic core -/

/-- The lhs coefficient cap expression (balanced triple-product window). -/
abbrev capL (B tb tw : ℕ) (k : ℕ) : ℕ :=
  WindowCaps.wconv (2 * m - 1) m
    (WindowCaps.wconv m m (WindowCaps.balCap B tw m) (WindowCaps.balCap B tw m))
    (WindowCaps.limbCap B tb m) k

/-- **Soundness core.** From the `GroupedEqD` implication over the padded
`lhsPad`/`rhsS` vectors and the eval bridges connecting `Z1,Z2,Z3` to their
signed/unsigned convolution meanings, derive the ℤ congruence
`em.value ≡ VZ(a)²·b.value (mod n)`. -/
lemma soundness_core [Fact (p > 2)] {B XB tb tq tw i₀ : ℕ}
    (V VR : GroupedEqV.VParams) (hXBeq : XB = B) (hB1 : 1 ≤ B) (hm1 : 1 ≤ m)
    (hlhs_ad : ∀ k, k < 2 * m + m - 1 → capL (m := m) B tb tw k < V.Nf k)
    (hrhs_ad : ∀ k, k < 2 * m + m - 1 →
      capL (m := m) B tb tw k + WindowCaps.qnCapW B tb tq m k
        + (if k < m then WindowCaps.limbCap B tb m k else 0) < VR.Nf k)
    (hNfp : ∀ k, k < 2 * m + m - 1 → V.Nf k + VR.Nf k ≤ p)
    (env : Environment (F p)) (a b n em : Var (BigInt m) (F p))
    (Z1 : Vector (Expression (F p)) (2 * m - 1))
    (Z2 : Vector (Expression (F p)) ((2 * m - 1) + m - 1))
    (z3Low : Vector (Expression (F p)) ((2 * m) + m - 2))
    (av bv nv emv : BigInt m (F p))
    (qv : BigInt (2 * m) (F p))
    (h_a : Vector.map (Expression.eval env) a = av)
    (h_b : Vector.map (Expression.eval env) b = bv)
    (h_n : Vector.map (Expression.eval env) n = nv)
    (h_em : Vector.map (Expression.eval env) em = emv)
    (hq_def : qv = Vector.map (Expression.eval env)
      (Vector.mapRange (2 * m) fun i ↦ var { index := i₀ + i }))
    (ha_norm : av.Normalized B) (hb_norm : bv.Normalized B)
    (hn_norm : nv.Normalized B) (hem_norm : emv.Normalized B)
    (hq_norm : qv.Normalized B)
    (ha_top : (av[m - 1]'(by omega)).val < 2 ^ tw)
    (hb_top : (bv[m - 1]'(by omega)).val < 2 ^ tb)
    (hn_top : (nv[m - 1]'(by omega)).val < 2 ^ tb)
    (hem_top : (emv[m - 1]'(by omega)).val < 2 ^ tb)
    (hq_top : (qv[2 * m - 1]'(by omega)).val < 2 ^ tq)
    (heqZ1 : ∀ k : Fin (2 * m - 1),
      Expression.eval env Z1[k.val]
        = Expression.eval env (bigIntMulNoReduce (SquareModBalGT.shiftedA B a) (SquareModBalGT.shiftedA B a))[k.val])
    (heqZ2 : ∀ k : Fin ((2 * m - 1) + m - 1),
      Expression.eval env Z2[k.val] = Expression.eval env (MulMod.mulNoReduceX Z1 b)[k.val])
    (heqZ3 : ∀ k : Fin (2 * m + m - 1),
      Expression.eval env ((z3VecD XB (lhsPadVec Z2) z3Low em)[k.val])
        = Expression.eval env
            (MulMod.mulNoReduceX (Vector.mapRange (2 * m) fun i ↦ var { index := i₀ + i }) n)[k.val])
    (h_eq_impl :
      (∀ k : Fin (2 * m + m - 1), ∃ z : ℤ,
          ((z : ℤ) : F p) = Expression.eval env ((lhsPadVec Z2)[k.val])
              - (GroupedEqXV.rhsValD (L := 2 * m + m - 1) XB
                  (Vector.map (Expression.eval env) (lhsPadVec Z2))
                  (Vector.map (Expression.eval env) (rhsSVecD z3Low em)))[k.val] ∧
          -(VR.Nf k.val : ℤ) < z ∧ z < (V.Nf k.val : ℤ)) →
        (∑ k : Fin (2 * m + m - 1),
          GroupedEqD.zsval (V.Nf k.val)
            (Expression.eval env ((lhsPadVec Z2)[k.val])
              - (GroupedEqXV.rhsValD (L := 2 * m + m - 1) XB
                  (Vector.map (Expression.eval env) (lhsPadVec Z2))
                  (Vector.map (Expression.eval env) (rhsSVecD z3Low em)))[k.val]) * 2 ^ (XB * k.val)) = 0) :
    (emv.value B : ℤ) ≡ BalancedZ.VZ B av * BalancedZ.VZ B av * (bv.value B : ℤ)
      [ZMOD (nv.value B : ℤ)] := by
  subst XB
  set qVar := (Vector.mapRange (2 * m) fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  have hm : 0 < m := hm1
  -- Z1 bridge: eval Z1[k] = intCast (z1F B av k)
  have haS : ∀ i : Fin m,
      Expression.eval env ((SquareModBalGT.shiftedA B a)[i.val]'i.isLt)
        = ((BalancedZ.zdigits B av i.val : ℤ) : F p) := by
    intro i; rw [SquareModBalGT.eval_shiftedA hB1 env a i, h_a]
  have hZ1 : ∀ i : Fin (2 * m - 1),
      Expression.eval env Z1[i.val] = ((z1F B av i.val : ℤ) : F p) := by
    intro i; rw [heqZ1 i]
    exact WindowCaps.eval_bigIntMulNoReduce_intCast env _ _ _ _ haS haS i
  have hbU : ∀ i : Fin m, Expression.eval env (b[i.val]'i.isLt)
      = ((BalancedZ.udigits bv i.val : ℤ) : F p) := by
    intro i; rw [SquareModBalGT.eval_udigit env b i, h_b]
  have hnU : ∀ i : Fin m, Expression.eval env (n[i.val]'i.isLt)
      = ((BalancedZ.udigits nv i.val : ℤ) : F p) := by
    intro i; rw [SquareModBalGT.eval_udigit env n i, h_n]
  have hqU : ∀ i : Fin (2 * m), Expression.eval env (qVar[i.val]'i.isLt)
      = ((BalancedZ.udigits qv i.val : ℤ) : F p) := by
    intro i
    rw [hq_def, SquareModBalGT.eval_udigit env qVar i]
  -- Z2 bridge: eval Z2[k] = intCast (lhsF B av bv k)
  have hZ2 : ∀ k : Fin ((2 * m - 1) + m - 1),
      Expression.eval env Z2[k.val] = ((lhsF B av bv k.val : ℤ) : F p) := by
    intro k; rw [heqZ2 k]
    have := WindowCaps.eval_mulNoReduceX_intCast env Z1 b (z1F B av) (BalancedZ.udigits bv)
      hZ1 hbU ⟨k.val, k.isLt⟩
    rw [this]; rfl
  -- Z3 bridge: eval Z3[k] = intCast (zconv (2m) m (udigits q)(udigits n) k)
  have hZ3 : ∀ (k : ℕ) (hk : k < 2 * m + m - 1),
      Expression.eval env ((z3VecD B (lhsPadVec Z2) z3Low em)[k]'hk)
        = ((WindowCaps.zconv (2 * m) m (BalancedZ.udigits qv) (BalancedZ.udigits nv) k : ℤ) : F p) := by
    intro k hk
    rw [heqZ3 ⟨k, hk⟩]
    have := WindowCaps.eval_mulNoReduceX_intCast env qVar n (BalancedZ.udigits qv) (BalancedZ.udigits nv)
      hqU hnU ⟨k, hk⟩
    rw [this]
  have hemU : ∀ i : Fin m, Expression.eval env (em[i.val]'i.isLt)
      = ((BalancedZ.udigits emv i.val : ℤ) : F p) := by
    intro i; rw [SquareModBalGT.eval_udigit env em i, h_em]
  -- padded lhs / rhs eval bridges
  have hLbridge : ∀ (k : ℕ) (hk : k < 2 * m + m - 1),
      Expression.eval env (if h : k < (2 * m - 1) + m - 1 then Z2[k]'h else 0) = ((zlF B av bv k : ℤ) : F p) := by
    intro k hk
    simp only [zlF]
    by_cases h : k < (2 * m - 1) + m - 1
    · rw [dif_pos h, if_pos h]; exact hZ2 ⟨k, h⟩
    · rw [dif_neg h, if_neg h]; simp [Expression.eval]
  have hLbridge' : ∀ (k : ℕ) (hk : k < 2 * m + m - 1),
      Expression.eval env ((lhsPadVec Z2)[k]'hk) = ((zlF B av bv k : ℤ) : F p) := by
    intro k hk
    rw [lhsPadVec_getElem Z2 k hk]
    exact hLbridge k hk
  have hRbridge : ∀ (k : ℕ) (hk : k < 2 * m + m - 1),
      (GroupedEqXV.rhsValD (L := 2 * m + m - 1) B
          (Vector.map (Expression.eval env) (lhsPadVec Z2))
          (Vector.map (Expression.eval env) (rhsSVecD z3Low em)))[k]'hk
        = ((rhsF qv nv emv k : ℤ) : F p) := by
    intro k hk
    have hbr := GroupedEqXV.rhsD_eval_bridge (L := 2 * m + m - 1) B env
      (lhsPadVec Z2) (rhsSVecD z3Low em)
      (Vector.map (Expression.eval env) (lhsPadVec Z2))
      (Vector.map (Expression.eval env) (rhsSVecD z3Low em))
      (fun j hj => by rw [Vector.getElem_map]) (fun j hj => by rw [Vector.getElem_map])
    rw [← hbr k hk]
    by_cases hklow : k < 2 * m + m - 1 - 1
    · rw [GroupedEqXV.rhsD_getElem_low (L := 2 * m + m - 1) B
        (lhsPadVec Z2) (rhsSVecD z3Low em) k hklow]
      rw [rhsSVecD_getElem_low z3Low em k (by omega)]
      have hzl : Expression.eval env (z3Low[k]'(by omega))
          = ((WindowCaps.zconv (2 * m) m (BalancedZ.udigits qv) (BalancedZ.udigits nv) k : ℤ) : F p) := by
        have h := hZ3 k hk
        rwa [z3VecD_getElem_low B (lhsPadVec Z2) z3Low em k (by omega)] at h
      unfold rhsF
      by_cases hkm : k < m
      · rw [dif_pos hkm, if_pos hkm,
          show Expression.eval env (z3Low[k]'(by omega) + em[k]'hkm)
            = Expression.eval env (z3Low[k]'(by omega)) + Expression.eval env (em[k]'hkm) from rfl,
          hzl, hemU ⟨k, hkm⟩]
        push_cast; ring
      · rw [dif_neg hkm, if_neg hkm, add_zero]
        exact hzl
    · have hktop : k = 2 * m + m - 1 - 1 := by omega
      subst hktop
      rw [GroupedEqXV.rhsD_getElem_top (L := 2 * m + m - 1) B
        (lhsPadVec Z2) (rhsSVecD z3Low em)]
      have h := hZ3 (2 * m + m - 1 - 1) hk
      rw [z3VecD_getElem_top B (lhsPadVec Z2) z3Low em] at h
      rw [h]
      unfold rhsF
      rw [if_neg (by omega : ¬ (2 * m + m - 1 - 1 < m)), add_zero]
  -- windows
  have hwlo : ∀ k, k < 2 * m + m - 1 → -(VR.Nf k : ℤ) < zlF B av bv k - rhsF qv nv emv k := by
    intro k hk
    have hl : |zlF B av bv k| ≤ (capL (m := m) B tb tw k : ℤ) := by
      unfold zlF
      by_cases h : k < (2 * m - 1) + m - 1
      · rw [if_pos h]; exact abs_lhsF_le hB1 hm1 av bv ha_norm ha_top hb_norm hb_top k
      · rw [if_neg h, abs_zero]; exact Int.natCast_nonneg _
    have hr := abs_rhsF_le hm1 qv nv emv hq_norm hq_top hn_norm hn_top hem_norm hem_top k
    have hr0 := rhsF_nonneg qv nv emv k
    rw [abs_le] at hl
    have had := hrhs_ad k hk
    have hcast : (capL (m := m) B tb tw k + WindowCaps.qnCapW B tb tq m k
        + (if k < m then WindowCaps.limbCap B tb m k else 0) : ℤ) < (VR.Nf k : ℤ) := by
      exact_mod_cast had
    have hrle : (rhsF qv nv emv k : ℤ)
        ≤ (WindowCaps.qnCapW B tb tq m k + (if k < m then WindowCaps.limbCap B tb m k else 0) : ℕ) := hr
    push_cast at hcast hrle
    have : -(capL (m := m) B tb tw k : ℤ) ≤ zlF B av bv k := hl.1
    omega
  have hwhi : ∀ k, k < 2 * m + m - 1 → zlF B av bv k - rhsF qv nv emv k < (V.Nf k : ℤ) := by
    intro k hk
    have hl : |zlF B av bv k| ≤ (capL (m := m) B tb tw k : ℤ) := by
      unfold zlF
      by_cases h : k < (2 * m - 1) + m - 1
      · rw [if_pos h]; exact abs_lhsF_le hB1 hm1 av bv ha_norm ha_top hb_norm hb_top k
      · rw [if_neg h, abs_zero]; exact Int.natCast_nonneg _
    have hr0 := rhsF_nonneg qv nv emv k
    rw [abs_le] at hl
    have had := hlhs_ad k hk
    have hcast : (capL (m := m) B tb tw k : ℤ) < (V.Nf k : ℤ) := by exact_mod_cast had
    have : zlF B av bv k ≤ (capL (m := m) B tb tw k : ℤ) := hl.2
    omega
  -- extract the ℤ difference sum
  have hspec := h_eq_impl (by
    intro k
    refine ⟨zlF B av bv k.val - rhsF qv nv emv k.val, ?_, hwlo k.val k.isLt, hwhi k.val k.isLt⟩
    rw [hLbridge' k.val k.isLt, hRbridge k.val k.isLt]
    push_cast; ring)
  have hzsum : (∑ k ∈ Finset.range (2 * m + m - 1),
      (zlF B av bv k - rhsF qv nv emv k) * 2 ^ (B * k)) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => (zlF B av bv k - rhsF qv nv emv k) * 2 ^ (B * k))]
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hspec
    congr 1
    exact (GroupedEqD.zsval_eq_of_window (by
        rw [hLbridge' k.val k.isLt, hRbridge k.val k.isLt]; push_cast; ring)
      (hwlo k.val k.isLt) (hwhi k.val k.isLt) (hNfp k.val k.isLt)).symm
  -- the difference sum equals VZ(a)²·b - (q·n + em)
  have hsplit := BalancedZ.ztriple_sum_split B m hm1 (z1F B av) (BalancedZ.udigits bv)
    (BalancedZ.udigits qv) (BalancedZ.udigits nv) (BalancedZ.udigits emv)
  rw [sum_z1F B hm1 av, BalancedZ.sum_udigits B bv, BalancedZ.sum_udigits B qv,
    BalancedZ.sum_udigits B nv, BalancedZ.sum_udigits B emv] at hsplit
  have hzero : BalancedZ.VZ B av * BalancedZ.VZ B av * (bv.value B : ℤ)
      - ((qv.value B : ℤ) * (nv.value B : ℤ) + (emv.value B : ℤ)) = 0 := by
    rw [← hsplit]
    exact hzsum
  have hident : (emv.value B : ℤ)
      = BalancedZ.VZ B av * BalancedZ.VZ B av * (bv.value B : ℤ) - (qv.value B : ℤ) * (nv.value B : ℤ) := by
    linarith
  rw [Int.ModEq]
  rw [hident]
  have hdvd : (nv.value B : ℤ) ∣
      (BalancedZ.VZ B av * BalancedZ.VZ B av * (bv.value B : ℤ)
        - (BalancedZ.VZ B av * BalancedZ.VZ B av * (bv.value B : ℤ) - (qv.value B : ℤ) * (nv.value B : ℤ))) :=
    ⟨(qv.value B : ℤ), by ring⟩
  exact (Int.modEq_iff_dvd.mpr (by
    have : (nv.value B : ℤ) ∣
        (BalancedZ.VZ B av * BalancedZ.VZ B av * (bv.value B : ℤ) - (qv.value B : ℤ) * (nv.value B : ℤ))
          - BalancedZ.VZ B av * BalancedZ.VZ B av * (bv.value B : ℤ) := ⟨-(qv.value B : ℤ), by ring⟩
    exact this)).symm

/-- **Completeness core.** Given the honest quotient witness and the ℤ spec
`em.value ≡ VZ(a)²·b (mod n)` with `em` canonical, produce the `NormalizeTight q`
obligation and the `GroupedEqD` `Assumptions` + `Spec`. -/
lemma completeness_core [Fact (p > 2)] {B XB PB tb tq tw i₀ : ℕ}
    (V VR : GroupedEqV.VParams) (hPBeq : PB = B) (hXBeq : XB = B) (hB : 2 ^ B < p)
    (hB1 : 1 ≤ B) (hm1 : 1 ≤ m) (htqB : tq ≤ B) (htbq : 2 * tb ≤ B + tq)
    (hlhs_ad : ∀ k, k < 2 * m + m - 1 → capL (m := m) B tb tw k < V.Nf k)
    (hrhs_ad : ∀ k, k < 2 * m + m - 1 →
      capL (m := m) B tb tw k + WindowCaps.qnCapW B tb tq m k
        + (if k < m then WindowCaps.limbCap B tb m k else 0) < VR.Nf k)
    (hNfp : ∀ k, k < 2 * m + m - 1 → V.Nf k + VR.Nf k ≤ p)
    (env : Environment (F p)) (a b n em : Var (BigInt m) (F p))
    (Z1 : Vector (Expression (F p)) (2 * m - 1))
    (Z2 : Vector (Expression (F p)) ((2 * m - 1) + m - 1))
    (z3Low : Vector (Expression (F p)) ((2 * m) + m - 2))
    (av bv nv emv : BigInt m (F p))
    (h_a : Vector.map (Expression.eval env) a = av)
    (h_b : Vector.map (Expression.eval env) b = bv)
    (h_n : Vector.map (Expression.eval env) n = nv)
    (h_em : Vector.map (Expression.eval env) em = emv)
    (ha_norm : av.Normalized B) (hb_norm : bv.Normalized B)
    (hn_norm : nv.Normalized B) (hem_norm : emv.Normalized B)
    (ha_ltT : av.value B < 2 ^ ((m - 1) * B + tw))
    (hb_ltN : bv.value B < nv.value B)
    (hem_ltN : emv.value B < nv.value B)
    (hn_ltT : nv.value B < 2 ^ ((m - 1) * B + tb))
    (hn_pos : 0 < nv.value B)
    (hbal_le : BalancedZ.balShift B m ≤ av.value B)
    (hbal_lt : av.value B - BalancedZ.balShift B m < nv.value B)
    (h_spec : (emv.value B : ℤ) ≡ BalancedZ.VZ B av * BalancedZ.VZ B av * (bv.value B : ℤ)
      [ZMOD (nv.value B : ℤ)])
    (hqwit : ∀ i : Fin (2 * m), env.get (i₀ + i.val)
      = (((av.value B - BalancedZ.balShift B m) * (av.value B - BalancedZ.balShift B m) * bv.value B
          / nv.value B / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (heqZ1 : ∀ k : Fin (2 * m - 1),
      Expression.eval env Z1[k.val]
        = Expression.eval env (bigIntMulNoReduce (SquareModBalGT.shiftedA B a) (SquareModBalGT.shiftedA B a))[k.val])
    (heqZ2 : ∀ k : Fin ((2 * m - 1) + m - 1),
      Expression.eval env Z2[k.val] = Expression.eval env (MulMod.mulNoReduceX Z1 b)[k.val])
    (hz3low : ∀ (k : ℕ) (hk : k < (2 * m) + m - 2),
      Expression.eval env (z3Low[k]'hk)
        = Expression.eval env
            ((MulMod.mulNoReduceX (Vector.mapRange (2 * m) fun i ↦ var { index := i₀ + i })
              n)[k]'(by omega))) :
    BigInt.NormalizedTight PB tq (Vector.map (Expression.eval env)
        (Vector.mapRange (2 * m) fun i ↦ var { index := i₀ + i })) ∧
      ((∀ k : Fin (2 * m + m - 1),
          Expression.eval env ((z3VecD XB (lhsPadVec Z2) z3Low em)[k.val])
            = Expression.eval env
                (MulMod.mulNoReduceX (Vector.mapRange (2 * m) fun i ↦ var { index := i₀ + i }) n)[k.val]) ∧
        (∀ k : Fin (2 * m + m - 1), ∃ z : ℤ,
          ((z : ℤ) : F p) = Expression.eval env ((lhsPadVec Z2)[k.val])
              - (GroupedEqXV.rhsValD (L := 2 * m + m - 1) XB
                  (Vector.map (Expression.eval env) (lhsPadVec Z2))
                  (Vector.map (Expression.eval env) (rhsSVecD z3Low em)))[k.val] ∧
          -(VR.Nf k.val : ℤ) < z ∧ z < (V.Nf k.val : ℤ)) ∧
        (∑ k : Fin (2 * m + m - 1),
          GroupedEqD.zsval (V.Nf k.val)
            (Expression.eval env ((lhsPadVec Z2)[k.val])
              - (GroupedEqXV.rhsValD (L := 2 * m + m - 1) XB
                  (Vector.map (Expression.eval env) (lhsPadVec Z2))
                  (Vector.map (Expression.eval env) (rhsSVecD z3Low em)))[k.val]) * 2 ^ (XB * k.val)) = 0) := by
  subst PB
  subst XB
  set qVar := (Vector.mapRange (2 * m) fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  have hm : 0 < m := hm1
  set vN := av.value B - BalancedZ.balShift B m with hvN
  set nval := nv.value B with hnval
  set qval := vN * vN * bv.value B / nval with hqval
  have hVZa : BalancedZ.VZ B av = (vN : ℤ) := by
    rw [BalancedZ.VZ, hvN]; push_cast [Nat.cast_sub hbal_le]; ring
  have hvN_lt : vN < nval := hbal_lt
  -- honest quotient bound: q < 2^((2m-1)B + tq)
  have hva_ltT : vN < 2 ^ ((m - 1) * B + tb) := lt_trans hvN_lt hn_ltT
  have hrw2m : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
  have hexp2 : (2 * m - 1) * B = 2 * ((m - 1) * B) + B := by rw [hrw2m]; ring
  have hqval_ltT : qval < 2 ^ ((2 * m - 1) * B + tq) := by
    rw [hqval]
    apply Nat.div_lt_of_lt_mul
    calc vN * vN * bv.value B < 2 ^ ((2 * m - 1) * B + tq) * nval := by
          refine Nat.mul_lt_mul_of_lt_of_le ?_ hb_ltN.le (by omega)
          calc vN * vN < 2 ^ ((m - 1) * B + tb) * 2 ^ ((m - 1) * B + tb) :=
                Nat.mul_lt_mul'' hva_ltT hva_ltT
            _ = 2 ^ (2 * ((m - 1) * B + tb)) := by rw [← pow_add]; ring_nf
            _ ≤ 2 ^ ((2 * m - 1) * B + tq) := by
                apply Nat.pow_le_pow_right (by norm_num); rw [hexp2]; omega
      _ = nval * 2 ^ ((2 * m - 1) * B + tq) := Nat.mul_comm _ _
  have h2m1 : 2 * m - 1 + 1 = 2 * m := by omega
  have hTle : (2 * m - 1) * B + tq ≤ B * (2 * m) := by
    calc (2 * m - 1) * B + tq ≤ (2 * m - 1) * B + B := by omega
      _ = (2 * m - 1 + 1) * B := by ring
      _ = (2 * m) * B := by rw [h2m1]
      _ = B * (2 * m) := Nat.mul_comm _ _
  have hqval_lt : qval < 2 ^ (B * (2 * m)) :=
    lt_of_lt_of_le hqval_ltT (Nat.pow_le_pow_right (by norm_num) hTle)
  have hqwit' : ∀ i : Fin (2 * m), env.get (i₀ + i.val)
      = ((qval / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
    intro i; rw [hqwit i]
  have hqv_val : BigInt.value B (Vector.map (Expression.eval env) qVar) = qval :=
    BigInt.value_mapRange i₀ qval env hB hqval_lt (fun i => hqwit' i)
  have hqv_norm : BigInt.Normalized B (Vector.map (Expression.eval env) qVar) :=
    MulMod.normalized_mapRange i₀ qval env hB (fun i => hqwit' i)
  set qv := Vector.map (Expression.eval env) qVar with hqvdef
  have hqtop : BigInt.NormalizedTight B tq qv := by
    refine ⟨hqv_norm, ?_⟩
    have hget : qv[2 * m - 1]'(by omega) = env.get (i₀ + (2 * m - 1)) := by
      simp [hqvdef, hqVar, circuit_norm]
    rw [hget, hqwit' ⟨2 * m - 1, by omega⟩,
      ZMod.val_natCast_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) hB.le)]
    calc qval / 2 ^ (B * (2 * m - 1)) % 2 ^ B ≤ qval / 2 ^ (B * (2 * m - 1)) := Nat.mod_le _ _
      _ < 2 ^ tq := by
          apply Nat.div_lt_of_lt_mul
          rw [show (2 : ℕ) ^ (B * (2 * m - 1)) * 2 ^ tq = 2 ^ ((2 * m - 1) * B + tq) from by
            rw [← pow_add]; congr 1; ring]
          exact hqval_ltT
  -- honest identity: em.value = vN²·b mod n
  have hem_eq : emv.value B = vN * vN * bv.value B % nval := by
    have h1 : (emv.value B : ℤ) ≡ ((vN * vN * bv.value B : ℕ) : ℤ) [ZMOD (nval : ℤ)] := by
      have := h_spec
      rw [hVZa, hnval] at this
      refine this.trans ?_
      push_cast; exact Int.ModEq.refl _
    have hmod : (emv.value B : ℤ) % (nval : ℤ) = ((vN * vN * bv.value B : ℕ) : ℤ) % (nval : ℤ) := h1
    have hlhs : (emv.value B : ℤ) % (nval : ℤ) = (emv.value B : ℤ) := by
      apply Int.emod_eq_of_lt (by positivity)
      exact_mod_cast (hnval ▸ hem_ltN)
    have hrhs : ((vN * vN * bv.value B : ℕ) : ℤ) % (nval : ℤ)
        = ((vN * vN * bv.value B % nval : ℕ) : ℤ) := by
      exact (Int.natCast_mod _ _)
    rw [hlhs, hrhs] at hmod
    exact_mod_cast hmod
  have hidN : qval * nval + emv.value B = vN * vN * bv.value B := by
    rw [hqval, hem_eq, Nat.mul_comm, Nat.div_add_mod]
  -- bridges (same as soundness_core)
  have haS : ∀ i : Fin m,
      Expression.eval env ((SquareModBalGT.shiftedA B a)[i.val]'i.isLt)
        = ((BalancedZ.zdigits B av i.val : ℤ) : F p) := by
    intro i; rw [SquareModBalGT.eval_shiftedA hB1 env a i, h_a]
  have hZ1 : ∀ i : Fin (2 * m - 1),
      Expression.eval env Z1[i.val] = ((z1F B av i.val : ℤ) : F p) := by
    intro i; rw [heqZ1 i]
    exact WindowCaps.eval_bigIntMulNoReduce_intCast env _ _ _ _ haS haS i
  have hbU : ∀ i : Fin m, Expression.eval env (b[i.val]'i.isLt)
      = ((BalancedZ.udigits bv i.val : ℤ) : F p) := by
    intro i; rw [SquareModBalGT.eval_udigit env b i, h_b]
  have hnU : ∀ i : Fin m, Expression.eval env (n[i.val]'i.isLt)
      = ((BalancedZ.udigits nv i.val : ℤ) : F p) := by
    intro i; rw [SquareModBalGT.eval_udigit env n i, h_n]
  have hqU : ∀ i : Fin (2 * m), Expression.eval env (qVar[i.val]'i.isLt)
      = ((BalancedZ.udigits qv i.val : ℤ) : F p) := by
    intro i; rw [hqvdef, SquareModBalGT.eval_udigit env qVar i]
  have hZ2 : ∀ k : Fin ((2 * m - 1) + m - 1),
      Expression.eval env Z2[k.val] = ((lhsF B av bv k.val : ℤ) : F p) := by
    intro k; rw [heqZ2 k]
    have := WindowCaps.eval_mulNoReduceX_intCast env Z1 b (z1F B av) (BalancedZ.udigits bv)
      hZ1 hbU ⟨k.val, k.isLt⟩
    rw [this]; rfl
  have hemU : ∀ i : Fin m, Expression.eval env (em[i.val]'i.isLt)
      = ((BalancedZ.udigits emv i.val : ℤ) : F p) := by
    intro i; rw [SquareModBalGT.eval_udigit env em i, h_em]
  have hLbridge : ∀ (k : ℕ) (hk : k < 2 * m + m - 1),
      Expression.eval env (if h : k < (2 * m - 1) + m - 1 then Z2[k]'h else 0) = ((zlF B av bv k : ℤ) : F p) := by
    intro k hk
    simp only [zlF]
    by_cases h : k < (2 * m - 1) + m - 1
    · rw [dif_pos h, if_pos h]; exact hZ2 ⟨k, h⟩
    · rw [dif_neg h, if_neg h]; simp [Expression.eval]
  have hLbridge' : ∀ (k : ℕ) (hk : k < 2 * m + m - 1),
      Expression.eval env ((lhsPadVec Z2)[k]'hk) = ((zlF B av bv k : ℤ) : F p) := by
    intro k hk
    rw [lhsPadVec_getElem Z2 k hk]
    exact hLbridge k hk
  -- tops
  have ha_top : (av[m - 1]'(by omega)).val < 2 ^ tw := WindowCaps.top_lt_of_value_lt ha_ltT
  have hb_top : (bv[m - 1]'(by omega)).val < 2 ^ tb :=
    WindowCaps.top_lt_of_value_lt (lt_trans hb_ltN hn_ltT)
  have hn_top : (nv[m - 1]'(by omega)).val < 2 ^ tb := WindowCaps.top_lt_of_value_lt hn_ltT
  have hem_top : (emv[m - 1]'(by omega)).val < 2 ^ tb :=
    WindowCaps.top_lt_of_value_lt (lt_trans hem_ltN hn_ltT)
  have hq_top : (qv[2 * m - 1]'(by omega)).val < 2 ^ tq := hqtop.2
  -- windows
  have hwlo : ∀ k, k < 2 * m + m - 1 → -(VR.Nf k : ℤ) < zlF B av bv k - rhsF qv nv emv k := by
    intro k hk
    have hl : |zlF B av bv k| ≤ (capL (m := m) B tb tw k : ℤ) := by
      unfold zlF
      by_cases h : k < (2 * m - 1) + m - 1
      · rw [if_pos h]; exact abs_lhsF_le hB1 hm1 av bv ha_norm ha_top hb_norm hb_top k
      · rw [if_neg h, abs_zero]; exact Int.natCast_nonneg _
    have hr := abs_rhsF_le hm1 qv nv emv hqv_norm hq_top hn_norm hn_top hem_norm hem_top k
    have hr0 := rhsF_nonneg qv nv emv k
    rw [abs_le] at hl
    have had := hrhs_ad k hk
    have hcast : (capL (m := m) B tb tw k + WindowCaps.qnCapW B tb tq m k
        + (if k < m then WindowCaps.limbCap B tb m k else 0) : ℤ) < (VR.Nf k : ℤ) := by
      exact_mod_cast had
    have hrle : (rhsF qv nv emv k : ℤ)
        ≤ (WindowCaps.qnCapW B tb tq m k + (if k < m then WindowCaps.limbCap B tb m k else 0) : ℕ) := hr
    push_cast at hcast hrle
    have : -(capL (m := m) B tb tw k : ℤ) ≤ zlF B av bv k := hl.1
    omega
  have hwhi : ∀ k, k < 2 * m + m - 1 → zlF B av bv k - rhsF qv nv emv k < (V.Nf k : ℤ) := by
    intro k hk
    have hl : |zlF B av bv k| ≤ (capL (m := m) B tb tw k : ℤ) := by
      unfold zlF
      by_cases h : k < (2 * m - 1) + m - 1
      · rw [if_pos h]; exact abs_lhsF_le hB1 hm1 av bv ha_norm ha_top hb_norm hb_top k
      · rw [if_neg h, abs_zero]; exact Int.natCast_nonneg _
    have hr0 := rhsF_nonneg qv nv emv k
    rw [abs_le] at hl
    have had := hlhs_ad k hk
    have hcast : (capL (m := m) B tb tw k : ℤ) < (V.Nf k : ℤ) := by exact_mod_cast had
    have : zlF B av bv k ≤ (capL (m := m) B tb tw k : ℤ) := hl.2
    omega
  -- the sum = 0 from the identity
  have hsplit := BalancedZ.ztriple_sum_split B m hm1 (z1F B av) (BalancedZ.udigits bv)
    (BalancedZ.udigits qv) (BalancedZ.udigits nv) (BalancedZ.udigits emv)
  rw [sum_z1F B hm1 av, BalancedZ.sum_udigits B bv, BalancedZ.sum_udigits B qv,
    BalancedZ.sum_udigits B nv, BalancedZ.sum_udigits B emv] at hsplit
  have hzsum : (∑ k ∈ Finset.range (2 * m + m - 1),
      (zlF B av bv k - rhsF qv nv emv k) * 2 ^ (B * k)) = 0 := by
    rw [show (∑ k ∈ Finset.range (2 * m + m - 1), (zlF B av bv k - rhsF qv nv emv k) * 2 ^ (B * k))
        = BalancedZ.VZ B av * BalancedZ.VZ B av * (bv.value B : ℤ)
          - ((BigInt.value B qv : ℤ) * (nv.value B : ℤ) + (emv.value B : ℤ)) from hsplit]
    rw [hVZa, hqv_val, hqval]
    have : ((vN * vN * bv.value B : ℕ) : ℤ)
        = ((qval * nval + emv.value B : ℕ) : ℤ) := by rw [hidN]
    rw [hqval] at this
    push_cast at this ⊢
    rw [← hnval]
    linarith
  -- reconstructed-top derivation chain
  have hz3conv : ∀ (k : ℕ) (hk : k < (2 * m) + m - 2),
      Expression.eval env (z3Low[k]'hk)
        = ((WindowCaps.zconv (2 * m) m (BalancedZ.udigits qv) (BalancedZ.udigits nv) k : ℤ) : F p) := by
    intro k hk
    rw [hz3low k hk]
    have := WindowCaps.eval_mulNoReduceX_intCast env qVar n
      (BalancedZ.udigits qv) (BalancedZ.udigits nv) hqU hnU ⟨k, by omega⟩
    rw [this]
  have hSlow : ∀ (k : ℕ) (hk : k < 2 * m + m - 1 - 1),
      Expression.eval env ((rhsSVecD z3Low em)[k]'(by omega))
        = ((rhsF qv nv emv k : ℤ) : F p) := by
    intro k hk
    rw [rhsSVecD_getElem_low z3Low em k (by omega)]
    unfold rhsF
    by_cases hkm : k < m
    · rw [dif_pos hkm, if_pos hkm,
        show Expression.eval env (z3Low[k]'(by omega) + em[k]'hkm)
          = Expression.eval env (z3Low[k]'(by omega)) + Expression.eval env (em[k]'hkm) from rfl,
        hz3conv k (by omega), hemU ⟨k, hkm⟩]
      push_cast; ring
    · rw [dif_neg hkm, if_neg hkm, add_zero]
      exact hz3conv k (by omega)
  have hStop : Expression.eval env
      (GroupedEqXV.topExprD (L := 2 * m + m - 1) B (lhsPadVec Z2) (rhsSVecD z3Low em))
      = ((rhsF qv nv emv (2 * m + m - 1 - 1) : ℤ) : F p) :=
    GroupedEqXV.topExprD_eval_of_sum_eq_zero (L := 2 * m + m - 1) B env
      (lhsPadVec Z2) (rhsSVecD z3Low em)
      (fun k => zlF B av bv k) (fun k => rhsF qv nv emv k)
      hLbridge' hSlow hzsum
  have hZ3 : ∀ (k : ℕ) (hk : k < 2 * m + m - 1),
      Expression.eval env ((z3VecD B (lhsPadVec Z2) z3Low em)[k]'hk)
        = ((WindowCaps.zconv (2 * m) m (BalancedZ.udigits qv) (BalancedZ.udigits nv) k : ℤ) : F p) := by
    intro k hk
    by_cases hklow : k < (2 * m) + m - 2
    · rw [z3VecD_getElem_low B (lhsPadVec Z2) z3Low em k hklow]
      exact hz3conv k hklow
    · have hktop : k = 2 * m + m - 1 - 1 := by omega
      subst hktop
      rw [z3VecD_getElem_top B (lhsPadVec Z2) z3Low em, hStop]
      unfold rhsF
      rw [if_neg (by omega : ¬ (2 * m + m - 1 - 1 < m)), add_zero]
  have heqZ3pin : ∀ k : Fin (2 * m + m - 1),
      Expression.eval env ((z3VecD B (lhsPadVec Z2) z3Low em)[k.val])
        = Expression.eval env
            (MulMod.mulNoReduceX (Vector.mapRange (2 * m) fun i ↦ var { index := i₀ + i }) n)[k.val] := by
    intro k
    rw [hZ3 k.val k.isLt]
    have := WindowCaps.eval_mulNoReduceX_intCast env qVar n
      (BalancedZ.udigits qv) (BalancedZ.udigits nv) hqU hnU k
    rw [this]
  have hRbridge : ∀ (k : ℕ) (hk : k < 2 * m + m - 1),
      (GroupedEqXV.rhsValD (L := 2 * m + m - 1) B
          (Vector.map (Expression.eval env) (lhsPadVec Z2))
          (Vector.map (Expression.eval env) (rhsSVecD z3Low em)))[k]'hk
        = ((rhsF qv nv emv k : ℤ) : F p) := by
    intro k hk
    have hbr := GroupedEqXV.rhsD_eval_bridge (L := 2 * m + m - 1) B env
      (lhsPadVec Z2) (rhsSVecD z3Low em)
      (Vector.map (Expression.eval env) (lhsPadVec Z2))
      (Vector.map (Expression.eval env) (rhsSVecD z3Low em))
      (fun j hj => by rw [Vector.getElem_map]) (fun j hj => by rw [Vector.getElem_map])
    rw [← hbr k hk]
    by_cases hklow : k < 2 * m + m - 1 - 1
    · rw [GroupedEqXV.rhsD_getElem_low (L := 2 * m + m - 1) B
        (lhsPadVec Z2) (rhsSVecD z3Low em) k hklow]
      exact hSlow k hklow
    · have hktop : k = 2 * m + m - 1 - 1 := by omega
      subst hktop
      rw [GroupedEqXV.rhsD_getElem_top (L := 2 * m + m - 1) B
        (lhsPadVec Z2) (rhsSVecD z3Low em)]
      exact hStop
  refine ⟨hqtop, heqZ3pin, ?_, ?_⟩
  · intro k
    refine ⟨zlF B av bv k.val - rhsF qv nv emv k.val, ?_, hwlo k.val k.isLt, hwhi k.val k.isLt⟩
    rw [hLbridge' k.val k.isLt, hRbridge k.val k.isLt]
    push_cast; ring
  · refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_)
      (Eq.trans (Fin.sum_univ_eq_sum_range (fun k =>
        (zlF B av bv k - rhsF qv nv emv k) * 2 ^ (B * k)) (2 * m + m - 1)) hzsum)
    congr 1
    exact GroupedEqD.zsval_eq_of_window (by
        rw [hLbridge' k.val k.isLt, hRbridge k.val k.isLt]; push_cast; ring)
      (hwlo k.val k.isLt) (hwhi k.val k.isLt) (hNfp k.val k.isLt)

/-! ## The balanced fused formal assertion -/

set_option maxHeartbeats 12000000 in
/-- The balanced fused square-multiply-mod assertion as a `GeneralFormalCircuit`:
soundness needs only the window facts; completeness assumes `a` encodes a
canonical residue. -/
def generalCircuit (P : BigIntParams p m) (P2 : BigIntParams p (2 * m)) (XB tb tw : ℕ)
    (tq : ℕ) (htq : 1 ≤ tq ∧ 2 ^ tq < p) (htqB : tq ≤ P2.B)
    (htb1 : 1 ≤ tb) (htbq : 2 * tb ≤ P.B + tq) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m + m - 1) XB gf posOf G V VR) (hXB1 : 1 ≤ XB)
    (hlhs_ad : ∀ k, k < 2 * m + m - 1 → capL (m := m) P.B tb tw k < V.Nf k)
    (hrhs_ad : ∀ k, k < 2 * m + m - 1 →
      capL (m := m) P.B tb tw k + WindowCaps.qnCapW P.B tb tq m k
        + (if k < m then WindowCaps.limbCap P.B tb m k else 0) < VR.Nf k)
    (hNfp : ∀ k, k < 2 * m + m - 1 → V.Nf k + VR.Nf k ≤ p)
    (hB2 : P2.B = P.B) (hXB : XB = P.B) [Fact (p > 2)] :
    GeneralFormalCircuit (F p) (InputsTo m) unit where
  main := main P P2 XB tw tq htq htqB gf posOf G V VR hgv hXB1 hB2 hXB
  Assumptions := fun input _ => Assumptions P.B tb tw input
  Spec := fun input _ _ => Spec P.B input
  ProverAssumptions := fun input _ _ => ProverAssumptions P.B tb tw input
  ProverSpec := fun _ _ _ => True
  soundness := by
    obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
    circuit_proof_start [NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      NormalizeTight.Assumptions, NormalizeTight.Spec,
      GroupedEqD.circuitD_assumptions_eq, GroupedEqD.circuitD_spec_eq,
      GroupedEqD.AssumptionsD, GroupedEqD.SpecD]
    obtain ⟨ha_norm, hb_norm, hn_norm, hem_norm, hab_ltT, hbb_ltN, hem_lt, hnb_ltT⟩ := h_assumptions
    obtain ⟨hq_tight, hZ1_ops, hZ2_ops, hZ3_ops, h_eq_impl⟩ := h_holds
    have hm : 0 < m := Nat.pos_of_neZero m
    have htqB' : tq ≤ B := by have h := htqB; rw [hB2] at h; exact h
    have ha_top : (input.a[m - 1]'(by omega)).val < 2 ^ tw :=
      WindowCaps.top_lt_of_value_lt hab_ltT
    have hb_top : (input.b[m - 1]'(by omega)).val < 2 ^ tb :=
      WindowCaps.top_lt_of_value_lt (lt_trans hbb_ltN hnb_ltT)
    have hn_top : (input.modulus[m - 1]'(by omega)).val < 2 ^ tb :=
      WindowCaps.top_lt_of_value_lt hnb_ltT
    have hem_top : (input.em[m - 1]'(by omega)).val < 2 ^ tb :=
      WindowCaps.top_lt_of_value_lt (lt_trans hem_lt hnb_ltT)
    have h3m : 3 * m - 1 < p := SqMulModTo.three_m_sub_one_lt hp
    have hpm1 : 2 * m - 1 < p := by omega
    have hpm2 : (2 * m - 1) + m - 1 < p := by omega
    have hpm3 : (2 * m) + m - 1 < p := by omega
    set z1Off := i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) with hz1Off
    set Z1T := (MulMod.interpolatedMul (SquareModBalGT.shiftedA B input_var.a)
      (SquareModBalGT.shiftedA B input_var.a) z1Off).1 with hZ1T
    set z2Off := z1Off + Operations.localLength (MulMod.interpolatedMul
      (SquareModBalGT.shiftedA B input_var.a) (SquareModBalGT.shiftedA B input_var.a) z1Off).2
      with hz2Off
    set Z2T := (MulMod.interpolatedMulX Z1T input_var.b z2Off).1 with hZ2T
    set z3Off := z2Off + Operations.localLength (MulMod.interpolatedMulX Z1T input_var.b z2Off).2
      with hz3Off
    set lowT := (Vector.mapRange ((2 * m) + m - 2) fun i => var (F := F p)
      { index := (z3Off + i) }) with hlowT
    have h_pZ1 := MulMod.interpolatedMul_soundness z1Off
      (SquareModBalGT.shiftedA B input_var.a) (SquareModBalGT.shiftedA B input_var.a) env hZ1_ops
    have h_pZ2 := MulMod.interpolatedMulX_soundness z2Off Z1T input_var.b env hZ2_ops
    have h_pZ3 := MulMod.interpolatedMulXAssert_soundness _ _ _ _ env hZ3_ops
    refine ⟨?_, MulMod.interpolatedMul_requirements _ _ _ _, MulMod.interpolatedMulX_requirements _ _ _ _,
      MulMod.interpolatedMulXAssert_requirements _ _ _ _ _,
      Or.inl (GroupedEqD.circuitD_channels_req_eq _ _ _ _ _ _ _ _)⟩
    have h_a : Vector.map (Expression.eval env) input_var.a = input.a := by simp only [← h_input]
    have h_b : Vector.map (Expression.eval env) input_var.b = input.b := by simp only [← h_input]
    have h_n : Vector.map (Expression.eval env) input_var.modulus = input.modulus := by
      simp only [← h_input]
    have h_em : Vector.map (Expression.eval env) input_var.em = input.em := by simp only [← h_input]
    have hq_norm' : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange (2 * m) fun i => var { index := i₀ + i })) := by
      have h := hq_tight.1; rw [hB2] at h; exact h
    have heqZ1_get := MulMod.interpolatedMul_eval_bridge env z1Off
      (SquareModBalGT.shiftedA B input_var.a) (SquareModBalGT.shiftedA B input_var.a) hpm1 h_pZ1
    have heqZ2_get := MulMod.interpolatedMulX_eval_bridge env z2Off Z1T input_var.b hpm2 h_pZ2
    have heqZ3_get := MulMod.interpolatedMulXAssertZ_eval_bridge env _ _ _ hpm3 h_pZ3
    exact soundness_core (i₀ := i₀) V VR hXB hB1 hm hlhs_ad hrhs_ad hNfp env
      input_var.a input_var.b input_var.modulus input_var.em
      Z1T Z2T lowT
      input.a input.b input.modulus input.em
      (Vector.map (Expression.eval env) (Vector.mapRange (2 * m) fun i => var { index := i₀ + i }))
      h_a h_b h_n h_em rfl ha_norm hb_norm hn_norm hem_norm hq_norm'
      ha_top hb_top hn_top hem_top hq_tight.2
      heqZ1_get heqZ2_get heqZ3_get h_eq_impl
  completeness := by
    obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
    circuit_proof_start [NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      NormalizeTight.Assumptions, NormalizeTight.Spec,
      GroupedEqD.circuitD_assumptions_eq, GroupedEqD.circuitD_spec_eq,
      GroupedEqD.AssumptionsD, GroupedEqD.SpecD]
    obtain ⟨⟨ha_norm, hb_norm, hn_norm, hem_norm, hab_ltT, hbb_ltN, hem_lt, hnb_ltT⟩, hbal_le, hbal_lt, h_spec⟩ := h_assumptions
    obtain ⟨hq_env, hZ1_uses, hZ2_uses, hz3_env, -⟩ := h_env
    have hm : 0 < m := Nat.pos_of_neZero m
    have htqB' : tq ≤ B := by have h := htqB; rw [hB2] at h; exact h
    set z1Off := i₀ + 2 * m + ((2 * m - 1) * (P2.B - 1) + (tq - 1)) with hz1Off
    set Z1T := (MulMod.interpolatedMul (SquareModBalGT.shiftedA B input_var.a)
      (SquareModBalGT.shiftedA B input_var.a) z1Off).1 with hZ1T
    set z2Off := z1Off + Operations.localLength (MulMod.interpolatedMul
      (SquareModBalGT.shiftedA B input_var.a) (SquareModBalGT.shiftedA B input_var.a) z1Off).2
      with hz2Off
    set Z2T := (MulMod.interpolatedMulX Z1T input_var.b z2Off).1 with hZ2T
    set z3Off := z2Off + Operations.localLength (MulMod.interpolatedMulX Z1T input_var.b z2Off).2
      with hz3Off
    set lowT := (Vector.mapRange ((2 * m) + m - 2) fun i => var (F := F p)
      { index := (z3Off + i) }) with hlowT
    have h_pvZ1 := MulMod.interpolatedMul_usesLocalWitnesses z1Off z1Off
      (SquareModBalGT.shiftedA B input_var.a) (SquareModBalGT.shiftedA B input_var.a) env rfl hZ1_uses
    have h_pvZ2 := MulMod.interpolatedMulX_usesLocalWitnesses z2Off
      (Operations.localLength (MulMod.interpolatedMul (SquareModBalGT.shiftedA B input_var.a)
        (SquareModBalGT.shiftedA B input_var.a) z1Off).2 + z1Off)
      Z1T input_var.b env (by rw [hz2Off]; ring) hZ2_uses
    have hz3wit : ∀ i : Fin ((2 * m) + m - 2),
        env.toEnvironment.get (Operations.localLength (MulMod.interpolatedMulX Z1T input_var.b z2Off).2
            + z2Off + i.val)
          = Expression.eval env.toEnvironment
              ((MulMod.mulNoReduceX (Vector.mapRange (2 * m) fun i => var (F := F p) { index := i₀ + i })
                input_var.modulus)[i.val]'(by have := i.isLt; omega)) := by
      intro i
      have h := hz3_env i
      rw [Vector.getElem_ofFn] at h
      have hswap : Operations.localLength (MulMod.interpolatedMulX Z1T input_var.b z2Off).2
            + (Operations.localLength (MulMod.interpolatedMul (SquareModBalGT.shiftedA B input_var.a)
                (SquareModBalGT.shiftedA B input_var.a) z1Off).2 + z1Off) + i.val
          = Operations.localLength (MulMod.interpolatedMulX Z1T input_var.b z2Off).2 + z2Off + i.val := by
        rw [hz2Off]
        ring
      rw [hswap] at h
      exact h
    have heva : MulMod.evalValue B env input_var.a = BigInt.value B input.a := by
      rw [MulMod.evalValue, BigInt.value, ← h_input]
    have hevb : MulMod.evalValue B env input_var.b = BigInt.value B input.b := by
      rw [MulMod.evalValue, BigInt.value, ← h_input]
    have hevn : MulMod.evalValue B env input_var.modulus = BigInt.value B input.modulus := by
      rw [MulMod.evalValue, BigInt.value, ← h_input]
    have hqwit : ∀ i : Fin (2 * m), env.toEnvironment.get (i₀ + i.val)
        = (((BigInt.value B input.a - BalancedZ.balShift B m) * (BigInt.value B input.a - BalancedZ.balShift B m)
            * BigInt.value B input.b / BigInt.value B input.modulus / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
      intro i; rw [hq_env i, Vector.getElem_ofFn, heva, hevb, hevn]
    have h_a : Vector.map (Expression.eval env.toEnvironment) input_var.a = input.a := by simp only [← h_input]
    have h_b : Vector.map (Expression.eval env.toEnvironment) input_var.b = input.b := by simp only [← h_input]
    have h_n : Vector.map (Expression.eval env.toEnvironment) input_var.modulus = input.modulus := by simp only [← h_input]
    have h_em : Vector.map (Expression.eval env.toEnvironment) input_var.em = input.em := by simp only [← h_input]
    have heqZ1_get := MulMod.interpolatedMul_eval_bridge_uses env.toEnvironment z1Off
      (SquareModBalGT.shiftedA B input_var.a) (SquareModBalGT.shiftedA B input_var.a) h_pvZ1
    have heqZ2_get := MulMod.interpolatedMulX_eval_bridge_uses env.toEnvironment z2Off
      Z1T input_var.b h_pvZ2
    have hz3low : ∀ (k : ℕ) (hk : k < (2 * m) + m - 2),
        Expression.eval env.toEnvironment (lowT[k]'hk)
          = Expression.eval env.toEnvironment
              ((MulMod.mulNoReduceX (Vector.mapRange (2 * m) fun i ↦ var { index := i₀ + i })
                input_var.modulus)[k]'(by omega)) := by
      intro k hk
      have hswap : (z3Off + k)
          = (Operations.localLength (MulMod.interpolatedMulX Z1T input_var.b z2Off).2 + z2Off + k) := by
        rw [hz3Off]; ring
      have hget : Expression.eval env.toEnvironment (lowT[k]'hk)
          = env.toEnvironment.get (Operations.localLength
              (MulMod.interpolatedMulX Z1T input_var.b z2Off).2 + z2Off + k) := by
        rw [hlowT, Vector.getElem_mapRange, hswap]
        rfl
      rw [hget]
      exact hz3wit ⟨k, hk⟩
    have hn_pos : 0 < BigInt.value B input.modulus := lt_of_le_of_lt (Nat.zero_le _) hbb_ltN
    have core := completeness_core (i₀ := i₀) V VR hB2 hXB hB hB1 hm htqB' htbq hlhs_ad hrhs_ad hNfp
      env.toEnvironment input_var.a input_var.b input_var.modulus input_var.em
      Z1T Z2T lowT
      input.a input.b input.modulus input.em h_a h_b h_n h_em
      ha_norm hb_norm hn_norm hem_norm hab_ltT hbb_ltN hem_lt hnb_ltT hn_pos hbal_le hbal_lt h_spec hqwit
      heqZ1_get heqZ2_get hz3low
    exact ⟨core.1,
      MulMod.interpolatedMul_completeness z1Off (SquareModBalGT.shiftedA B input_var.a)
        (SquareModBalGT.shiftedA B input_var.a) env h_pvZ1,
      MulMod.interpolatedMulX_completeness z2Off Z1T input_var.b env h_pvZ2,
      MulMod.interpolatedMulXAssert_completeness _
        (Vector.mapRange (2 * m) fun i => var { index := i₀ + i }) input_var.modulus _ env core.2.1,
      core.2.2⟩

end SqMulModBalTo

end

/-! ## Cost / R1CS certificates for the balanced fused assertion -/

namespace GadgetCost

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Challenge.CostR1CS
open Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostInfra

variable {m : ℕ}

/-- `shiftedA` preserves affineness (subtracting a constant). -/
theorem affineW_shiftedA [NeZero m] (B : ℕ) (a : Var (BigInt m) (F circomPrime))
    (ha : AffineW a) : AffineW (SquareModBalGT.shiftedA B a) := by
  intro i hi
  rw [SquareModBalGT.shiftedA, Vector.getElem_mapFinRange]
  split
  · exact ha i hi
  · exact Affine.sub (ha i hi) (Affine.const _)

/-- The padded lhs vector is affine coordinatewise. -/
theorem affineW_lhsPadVecTo [NeZero m]
    (Z2 : Vector (Expression (F circomPrime)) ((2 * m - 1) + m - 1))
    (hZ2 : AffineW Z2) : AffineW (SqMulModTo.lhsPadVec Z2) := by
  intro i hi
  unfold SqMulModTo.lhsPadVec
  rw [Vector.getElem_mapFinRange]
  split
  · exact hZ2 i (by assumption)
  · exact (Affine.zero : Affine (0 : Expression (F circomPrime)))

/-- The definitional-top fused rhs vector is affine coordinatewise. -/
theorem affineW_rhsSVecDTo [NeZero m]
    (z3Low : Vector (Expression (F circomPrime)) ((2 * m) + m - 2))
    (em : Var (BigInt m) (F circomPrime))
    (hlow : AffineW z3Low) (hem : AffineW em) :
    AffineW (SqMulModBalTo.rhsSVecD z3Low em) := by
  intro i hi
  unfold SqMulModBalTo.rhsSVecD
  rw [Vector.getElem_mapFinRange]
  split
  · split
    · exact Affine.add (hlow i (by assumption)) (hem i (by assumption))
    · exact hlow i (by assumption)
  · exact (Affine.zero : Affine (0 : Expression (F circomPrime)))

/-- The spliced fused `q·n` coefficient vector is affine coordinatewise. -/
theorem affineW_z3VecD [NeZero m] (XB : ℕ)
    (lhsPad : Vector (Expression (F circomPrime)) (2 * m + m - 1))
    (z3Low : Vector (Expression (F circomPrime)) ((2 * m) + m - 2))
    (em : Var (BigInt m) (F circomPrime))
    (hpad : AffineW lhsPad) (hlow : AffineW z3Low) (hem : AffineW em) :
    AffineW (SqMulModBalTo.z3VecD XB lhsPad z3Low em) := by
  intro i hi
  unfold SqMulModBalTo.z3VecD
  rw [Vector.getElem_mapFinRange]
  split
  · exact hlow i (by assumption)
  · exact affine_topExprD XB lhsPad (SqMulModBalTo.rhsSVecD z3Low em) hpad
      (affineW_rhsSVecDTo z3Low em hlow hem)

/-- Per-gadget `Count` of the balanced fused assertion (identical shape to
`SqMulModTo`: the `GroupedEqD` block has the same width cost as `GroupedEqXV`). -/
def sqMulModBalToCount (B tq G : ℕ) (Wf : ℕ → ℕ) : Count :=
  ⟨2 * m, 0⟩ + ((⟨(2 * m - 1) * (B - 1), (2 * m - 1) * B⟩ + ⟨tq - 1, tq⟩) +
    (⟨2 * m - 1, 2 * m - 1⟩ +
      (⟨(2 * m - 1) + m - 1, (2 * m - 1) + m - 1⟩ +
        (⟨(2 * m) + m - 2, 0⟩ +
          (⟨0, (2 * m) + m - 1⟩ +
            ⟨GroupedEqXV.widthAllocFrom Wf (G - 2) 0,
              GroupedEqXV.widthConsFrom Wf (G - 2) 0⟩)))))

theorem costIs_sqMulModBalTo (P : BigIntParams circomPrime m) (P2 : BigIntParams circomPrime (2 * m))
    (XB tw : ℕ) (tq : ℕ)
    (htq : 1 ≤ tq ∧ (2 : ℕ) ^ tq < circomPrime) (htqB : tq ≤ P2.B) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m + m - 1) XB gf posOf G V VR) (hXB1 : 1 ≤ XB)
    (hB2 : P2.B = P.B) (hXB : XB = P.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (MulModTo.InputsTo m) (F circomPrime)) :
    CostIs (SqMulModBalTo.main P P2 XB tw tq htq htqB gf posOf G V VR hgv hXB1 hB2 hXB input)
      (sqMulModBalToCount (m := m) P.B tq G V.Wf) := by
  have hm : 0 < m := Nat.pos_of_neZero m
  rw [show sqMulModBalToCount (m := m) P.B tq G V.Wf = sqMulModBalToCount (m := m) P2.B tq G V.Wf from by
    rw [hB2]]
  unfold SqMulModBalTo.main sqMulModBalToCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (costIs_assertion_normalizeTight P2 tq htq htqB _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun z1 => ?_
  refine CostIs.bind (costIs_interpolatedMulX _ _) fun z2 => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun z3Low => ?_
  refine CostIs.bind (costIs_interpolatedMulXAssert _ _ _) fun _ => ?_
  exact costIs_assertion_groupedEqDD XB gf posOf G V VR hgv hXB1 _

theorem costIs_sub_sqMulModBalTo (P : BigIntParams circomPrime m) (P2 : BigIntParams circomPrime (2 * m))
    (XB tb tw : ℕ) (tq : ℕ)
    (htq : 1 ≤ tq ∧ (2 : ℕ) ^ tq < circomPrime) (htqB : tq ≤ P2.B)
    (htb1 : 1 ≤ tb) (htbq : 2 * tb ≤ P.B + tq) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m + m - 1) XB gf posOf G V VR) (hXB1 : 1 ≤ XB)
    (hlhs_ad : ∀ k, k < 2 * m + m - 1 → SqMulModBalTo.capL (m := m) P.B tb tw k < V.Nf k)
    (hrhs_ad : ∀ k, k < 2 * m + m - 1 →
      SqMulModBalTo.capL (m := m) P.B tb tw k + WindowCaps.qnCapW P.B tb tq m k
        + (if k < m then WindowCaps.limbCap P.B tb m k else 0) < VR.Nf k)
    (hNfp : ∀ k, k < 2 * m + m - 1 → V.Nf k + VR.Nf k ≤ circomPrime)
    (hB2 : P2.B = P.B) (hXB : XB = P.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulModTo.InputsTo m) (F circomPrime)) :
    CostIs (subcircuitWithAssertion
      (SqMulModBalTo.generalCircuit P P2 XB tb tw tq htq htqB htb1 htbq gf posOf G V VR hgv hXB1
        hlhs_ad hrhs_ad hNfp hB2 hXB) b)
      (sqMulModBalToCount (m := m) P.B tq G V.Wf) :=
  CostIs.subcircuitWithAssertion
    (fun n => costIs_sqMulModBalTo P P2 XB tw tq htq htqB gf posOf G V VR hgv hXB1 hB2 hXB b n)

theorem isR1CS_sqMulModBalTo (P : BigIntParams circomPrime m) (P2 : BigIntParams circomPrime (2 * m))
    (XB tw : ℕ) (tq : ℕ)
    (htq : 1 ≤ tq ∧ (2 : ℕ) ^ tq < circomPrime) (htqB : tq ≤ P2.B) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m + m - 1) XB gf posOf G V VR) (hXB1 : 1 ≤ XB)
    (hB2 : P2.B = P.B) (hXB : XB = P.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (MulModTo.InputsTo m) (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hn : AffineW input.modulus)
    (hem : AffineW input.em) :
    IsR1CSCirc (SqMulModBalTo.main P P2 XB tw tq htq htqB gf posOf G V VR hgv hXB1 hB2 hXB input) := by
  have hm : 0 < m := Nat.pos_of_neZero m
  unfold SqMulModBalTo.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalizeTight P2 tq htq htqB _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  have haS := affineW_shiftedA P.B input.a ha
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ haS haS) fun nz1 => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_interpolatedMulX _ _ (affineW_interpolatedMul_output _ _ _) hb) fun nz2 => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nz3 => ?_
  refine IsR1CSCirc.bind (isR1CS_interpolatedMulXAssert _ _ _
    (affineW_provableWitness_bigInt _ nq) hn
    (affineW_z3VecD XB _ _ _ (affineW_lhsPadVecTo _ (affineW_mapRange_var _))
      (affineW_provableWitness_bigInt _ nz3) hem)) fun _ => ?_
  refine GadgetCost.isR1CS_assertion_groupedEqDD XB gf posOf G V VR hgv hXB1 _ ?_ ?_
  · exact affineW_lhsPadVecTo _ (affineW_mapRange_var _)
  · exact affineW_rhsSVecDTo _ _ (affineW_provableWitness_bigInt _ nz3) hem

theorem isR1CS_sub_sqMulModBalTo (P : BigIntParams circomPrime m) (P2 : BigIntParams circomPrime (2 * m))
    (XB tb tw : ℕ) (tq : ℕ)
    (htq : 1 ≤ tq ∧ (2 : ℕ) ^ tq < circomPrime) (htqB : tq ≤ P2.B)
    (htb1 : 1 ≤ tb) (htbq : 2 * tb ≤ P.B + tq) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m + m - 1) XB gf posOf G V VR) (hXB1 : 1 ≤ XB)
    (hlhs_ad : ∀ k, k < 2 * m + m - 1 → SqMulModBalTo.capL (m := m) P.B tb tw k < V.Nf k)
    (hrhs_ad : ∀ k, k < 2 * m + m - 1 →
      SqMulModBalTo.capL (m := m) P.B tb tw k + WindowCaps.qnCapW P.B tb tq m k
        + (if k < m then WindowCaps.limbCap P.B tb m k else 0) < VR.Nf k)
    (hNfp : ∀ k, k < 2 * m + m - 1 → V.Nf k + VR.Nf k ≤ circomPrime)
    (hB2 : P2.B = P.B) (hXB : XB = P.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulModTo.InputsTo m) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus) (hem : AffineW b.em) :
    IsR1CSCirc (subcircuitWithAssertion
      (SqMulModBalTo.generalCircuit P P2 XB tb tw tq htq htqB htb1 htbq gf posOf G V VR hgv hXB1
        hlhs_ad hrhs_ad hNfp hB2 hXB) b) :=
  IsR1CSCirc.subcircuitWithAssertion
    (fun n => isR1CS_sqMulModBalTo P P2 XB tw tq htq htqB gf posOf G V VR hgv hXB1 hB2 hXB b ha hb hn hem n)

end GadgetCost

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
