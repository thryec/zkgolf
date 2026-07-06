import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulMod
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.SquareModLazy
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.BalancedZ

/-!
# Balanced signed-digit modular squaring batteries (phase 3)

Two variants of the lazy modular squaring battery whose residue output is
witnessed in *balanced* signed-digit form: the residue limbs `u_i` are the
plain base-`2^B` digits of `r + balShift` (range-checked `< 2^B` below the top
and `< 2^tw` at the top), and the coefficient evaluations feed the two-sided
window grouped equality `GroupedEqD` through the *signed* digit windows
(`d_i = u_i − 2^(B−1)` below the top).

* `SquareModBalGT` — the middle battery: balanced input `a`, unsigned `q`/`n`,
  balanced output `r`, certifying `VZ(r) ≡ VZ(a)² (mod n)` over ℤ.
* `SquareModBalFirstGT` — the first battery: unsigned tight input `a` (= `sig`),
  balanced output `r`, certifying `VZ(r) ≡ (a.value)² (mod n)` over ℤ.

Both keep the quotient `q` fully unsigned (`NormalizeTight` at top width `tb`);
soundness recovers the ℤ identity `lhs² = q·n + VZ(r)` from `GroupedEqD`'s
windowed-lift difference sum via the phase-2 `BalancedZ` machinery.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

instance : NeZero (2 * m - 1) := ⟨by have := Nat.pos_of_neZero m; omega⟩

namespace SquareModBalGT

open SquareModLazy (Inputs)

/-- Natural-number value of a witnessed limb vector (used only in witness generators). -/
private def evalValue (B : ℕ) (env : ProverEnvironment (F p))
    (x : Var (BigInt m) (F p)) : ℕ :=
  Specs.RSA.fromLimbs B ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)

/-- The shifted-coefficient view of a balanced operand: subtract the constant
`2^(B−1)` from every limb below the top, so each entry evaluates to the field
image of the *signed* digit. -/
def shiftedA (B : ℕ) (a : Var (BigInt m) (F p)) : Var (BigInt m) (F p) :=
  Vector.mapFinRange m fun i =>
    if i.val = m - 1 then a[i.val]'i.isLt
    else a[i.val]'i.isLt - (((2 ^ (B - 1) : ℕ) : F p) : Expression (F p))

/-- The definitional-top rhs vector: witnessed low `q·n` cells plus the shifted
balanced `r`-digit on the low `m` positions; the top entry is a dummy `0`
(replaced inside `GroupedEqD.circuitD` by the affine reconstruction). -/
def rhsSVecD (B : ℕ) (sqnLow : Vector (Expression (F p)) (2 * m - 2))
    (r : Var (BigInt m) (F p)) : Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapFinRange (2 * m - 1) fun k =>
    if hlow : k.val < 2 * m - 2 then
      (if h : k.val < m then
        (if k.val = m - 1 then sqnLow[k.val]'hlow + r[k.val]'h
         else sqnLow[k.val]'hlow + r[k.val]'h - (((2 ^ (B - 1) : ℕ) : F p) : Expression (F p)))
       else sqnLow[k.val]'hlow)
    else 0

/-- The spliced `q·n` coefficient vector fed to the point-row assertion: the
witnessed low cells, with the top coefficient replaced by the affine
reconstruction `topExprD` of the equality's deleted final row. -/
def sqnVecD (B : ℕ) (Pc : Vector (Expression (F p)) (2 * m - 1))
    (sqnLow : Vector (Expression (F p)) (2 * m - 2))
    (r : Var (BigInt m) (F p)) : Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapFinRange (2 * m - 1) fun k =>
    if hlow : k.val < 2 * m - 2 then sqnLow[k.val]'hlow
    else GroupedEqXV.topExprD (L := 2 * m - 1) B Pc (rhsSVecD B sqnLow r)

lemma rhsSVecD_getElem_low (B : ℕ) (sqnLow : Vector (Expression (F p)) (2 * m - 2))
    (r : Var (BigInt m) (F p)) (k : ℕ) (hk : k < 2 * m - 2) :
    (rhsSVecD B sqnLow r)[k]'(by omega)
      = (if h : k < m then
          (if k = m - 1 then sqnLow[k]'hk + r[k]'h
           else sqnLow[k]'hk + r[k]'h - (((2 ^ (B - 1) : ℕ) : F p) : Expression (F p)))
         else sqnLow[k]'hk) := by
  unfold rhsSVecD
  rw [Vector.getElem_mapFinRange]
  simp only [dif_pos hk]

lemma rhsSVecD_getElem_low_var (B : ℕ) (sqnLow : Vector (Expression (F p)) (2 * m - 2))
    (i₀ : ℕ) (k : ℕ) (hk : k < 2 * m - 2) :
    (rhsSVecD B sqnLow (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))[k]'(by omega)
      = (if h : k < m then
          (if k = m - 1 then sqnLow[k]'hk + var (F := F p) { index := i₀ + m + k }
           else sqnLow[k]'hk + var (F := F p) { index := i₀ + m + k }
             - (((2 ^ (B - 1) : ℕ) : F p) : Expression (F p)))
         else sqnLow[k]'hk) := by
  rw [rhsSVecD_getElem_low B sqnLow _ k hk]
  by_cases h : k < m
  · by_cases h2 : k = m - 1
    · rw [dif_pos h, dif_pos h, if_pos h2, if_pos h2, Vector.getElem_mapRange]
    · rw [dif_pos h, dif_pos h, if_neg h2, if_neg h2, Vector.getElem_mapRange]
  · rw [dif_neg h, dif_neg h]

lemma sqnVecD_getElem_low (B : ℕ) (Pc : Vector (Expression (F p)) (2 * m - 1))
    (sqnLow : Vector (Expression (F p)) (2 * m - 2))
    (r : Var (BigInt m) (F p)) (k : ℕ) (hk : k < 2 * m - 2) :
    (sqnVecD B Pc sqnLow r)[k]'(by omega) = sqnLow[k]'hk := by
  unfold sqnVecD
  rw [Vector.getElem_mapFinRange]
  simp only [dif_pos hk]

lemma sqnVecD_getElem_top (B : ℕ) (Pc : Vector (Expression (F p)) (2 * m - 1))
    (sqnLow : Vector (Expression (F p)) (2 * m - 2))
    (r : Var (BigInt m) (F p)) :
    (sqnVecD B Pc sqnLow r)[2 * m - 1 - 1]'(by have := Nat.pos_of_neZero m; omega)
      = GroupedEqXV.topExprD (L := 2 * m - 1) B Pc (rhsSVecD B sqnLow r) := by
  unfold sqnVecD
  rw [Vector.getElem_mapFinRange]
  simp only [dif_neg (by omega : ¬ (2 * m - 1 - 1 < 2 * m - 2))]

/-- The `main` circuit: witness `q = ⌊VZ(a)²/n⌋` (unsigned digits) and the
balanced digits `u` of `r = VZ(a)² mod n` (plain digits of `r + balShift`),
range-check both (`q` top `tb` bits, `u` top `tw` bits), build the signed
convolutions `aS·aS` and `q·n` by interpolation, and assert the difference
through the two-sided window grouped equality `GroupedEqD`. Returns `u`. -/
def main (P : BigIntParams p m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htw : 1 ≤ tw ∧ 2 ^ tw < p)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m - 1) P.B gf posOf G V VR)
    [Fact (p > 2)] (input : Var (Inputs m) (F p)) :
    Circuit (F p) (Var (BigInt m) (F p)) := do
  let a := input.a
  let n := input.modulus

  let q ← ProvableType.witness (α := BigInt m) fun env =>
    let vN := evalValue P.B env a - BalancedZ.balShift P.B m
    let qval : ℕ := vN * vN / evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let r ← ProvableType.witness (α := BigInt m) fun env =>
    let vN := evalValue P.B env a - BalancedZ.balShift P.B m
    let rval : ℕ := vN * vN % evalValue P.B env n + BalancedZ.balShift P.B m
    Vector.ofFn fun k : Fin m => ((rval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  NormalizeTight.circuit P tb htb (Nat.le_of_succ_le htbB) q
  NormalizeTight.circuit P tw htw htwB r

  let aS := shiftedA P.B a
  let Pc ← MulMod.interpolatedMul aS aS
  let sqnLow ← ProvableType.witness (α := fields (2 * m - 2)) fun env =>
    Vector.ofFn fun k : Fin (2 * m - 2) =>
      Expression.eval env.toEnvironment
        ((bigIntMulNoReduce q n)[k.val]'(by have := k.isLt; omega))
  MulMod.interpolatedMulAssert q n (sqnVecD P.B Pc sqnLow r)
  GroupedEqD.circuitD (L := 2 * m - 1) P.B gf posOf G V VR hgv P.hB1
    { lhs := Pc, rhs := rhsSVecD P.B sqnLow r }
  return r

instance elaborated (P : BigIntParams p m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htw : 1 ≤ tw ∧ 2 ^ tw < p)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m - 1) P.B gf posOf G V VR) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) (BigInt m)
      (main P tb tw htb htw htbB htwB gf posOf G V VR hgv) where
  localLength _ :=
    m + m + ((m - 1) * (P.B - 1) + (tb - 1)) + ((m - 1) * (P.B - 1) + (tw - 1))
      + (2 * m - 1) + (2 * m - 2)
      + GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0
  output _ i0 := varFromOffset (BigInt m) (i0 + m)
  localLength_eq := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, MulMod.interpolatedMulAssert, circuit_norm,
      Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, GroupedEqD.circuitD, GroupedEqD.elaboratedD, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]
    omega
  output_eq := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, MulMod.interpolatedMulAssert, circuit_norm,
      Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, GroupedEqD.circuitD, GroupedEqD.elaboratedD, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, MulMod.interpolatedMul, MulMod.interpolatedMulAssert, circuit_norm,
      Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, GroupedEqD.circuitD, GroupedEqD.elaboratedD, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, MulMod.interpolatedMulAssert, circuit_norm,
      Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, GroupedEqD.circuitD, GroupedEqD.elaboratedD, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]

/-- Verifier-side assumptions for the balanced middle battery: `a`'s limbs are
window-checked (`Normalized` with a `tw`-bit top, packaged as the value bound),
`n` is a normalized 4096-bit modulus with the usual bounds. -/
def SoundAssumptions (B tb tw : ℕ) (input : Inputs m (F p)) : Prop :=
  input.a.Normalized B ∧ input.modulus.Normalized B ∧
    input.a.value B < 2 ^ ((m - 1) * B + tw) ∧
    input.modulus.value B < 2 ^ ((m - 1) * B + tb) ∧
    0 < input.modulus.value B ∧
    2 ^ ((m - 1) * B + tb - 1) ≤ input.modulus.value B

/-- Honest-prover assumptions: additionally, `a` is the balanced encoding of a
canonical residue (`balShift ≤ a.value` and `a.value − balShift < n`). -/
def Assumptions (B tb tw : ℕ) (input : Inputs m (F p)) : Prop :=
  SoundAssumptions B tb tw input ∧
    BalancedZ.balShift B m ≤ input.a.value B ∧
    input.a.value B - BalancedZ.balShift B m < input.modulus.value B

/-- Postcondition: the output is window-checked (balanced-normalized) and its
balanced ℤ reading is congruent to `VZ(a)²` mod `n` over ℤ. -/
def Spec (B tw : ℕ) (input : Inputs m (F p)) (out : BigInt m (F p)) : Prop :=
  BigInt.NormalizedTight B tw out ∧
    BalancedZ.VZ B out ≡ BalancedZ.VZ B input.a * BalancedZ.VZ B input.a
      [ZMOD (input.modulus.value B : ℤ)]

/-- Honest-prover side fact: the output is the balanced encoding of the
canonical remainder. -/
def ProverSpec (B : ℕ) (input : Inputs m (F p)) (out : BigInt m (F p)) : Prop :=
  BalancedZ.balShift B m ≤ out.value B ∧
    out.value B - BalancedZ.balShift B m < input.modulus.value B

/-- Adequacy of the two-sided window bounds for the balanced middle battery:
`V.Nf` (= `NfP`) dominates the balanced square window plus one balanced
`r`-digit; `VR.Nf` (= `NfN`) additionally absorbs the unsigned `q·n` window. -/
def NfOkD (B tb tw : ℕ) (V VR : GroupedEqV.VParams) : Prop :=
  (∀ j, j < 2 * m - 1 →
    WindowCaps.wconv m m (WindowCaps.balCap B tw m) (WindowCaps.balCap B tw m) j
      + (if j < m then WindowCaps.balCap B tw m j else 0) < V.Nf j) ∧
  (∀ j, j < 2 * m - 1 →
    WindowCaps.wconv m m (WindowCaps.balCap B tw m) (WindowCaps.balCap B tw m) j
      + WindowCaps.wconv m m (WindowCaps.limbCap B tb m) (WindowCaps.limbCap B tb m) j
      + (if j < m then WindowCaps.balCap B tw m j else 0) < VR.Nf j)

/-! ## Shared eval-bridge / window context

Both soundness and completeness need: the field-level bridges expressing the
evaluated lhs/rhs coefficients as ℤ-casts of the digit-family convolutions, and
the two-sided windows on their difference. The digit families are fixed
functions of the *evaluated* limb vectors. -/

section Core
variable {B tb tw : ℕ}

/-- The signed lhs digit-convolution family. -/
def zlF (B : ℕ) (av : BigInt m (F p)) : ℕ → ℤ :=
  fun k => WindowCaps.zconv m m (BalancedZ.zdigits B av) (BalancedZ.zdigits B av) k

/-- The rhs family: unsigned `q·n` convolution plus one signed `r` digit on the
low positions. -/
def zrF (B : ℕ) (qv nv rv : BigInt m (F p)) : ℕ → ℤ :=
  fun k => WindowCaps.zconv m m (BalancedZ.udigits qv) (BalancedZ.udigits nv) k
    + (if k < m then BalancedZ.zdigits B rv k else 0)


/-- Evaluate the shifted operand: field image of the signed digit. -/
lemma eval_shiftedA (hB1 : 1 ≤ B) (env : Environment (F p)) (a : Var (BigInt m) (F p))
    (i : Fin m) :
    Expression.eval env ((shiftedA B a)[i.val]'i.isLt)
      = ((BalancedZ.zdigits B (Vector.map (Expression.eval env) a) i.val : ℤ) : F p) := by
  have hm := Nat.pos_of_neZero m
  rw [shiftedA, Vector.getElem_mapFinRange, BalancedZ.zdigits, dif_pos i.isLt]
  by_cases h : i.val = m - 1
  · rw [if_pos h, if_pos h]
    simp only [Vector.getElem_map, Int.cast_natCast]
    exact (ZMod.natCast_zmod_val _).symm
  · rw [if_neg h, if_neg h]
    rw [show Expression.eval env
        (a[i.val]'i.isLt - (((2 ^ (B - 1) : ℕ) : F p) : Expression (F p)))
        = Expression.eval env (a[i.val]'i.isLt) - ((2 ^ (B - 1) : ℕ) : F p) from by
      simp only [Expression.eval]
      push_cast
      ring]
    simp only [Vector.getElem_map]
    push_cast
    rw [ZMod.natCast_zmod_val]


/-- Unsigned limb vectors evaluate to ℤ-casts of their digit families. -/
lemma eval_udigit (env : Environment (F p)) (x : Var (BigInt m) (F p)) (i : Fin m) :
    Expression.eval env (x[i.val]'i.isLt)
      = ((BalancedZ.udigits (Vector.map (Expression.eval env) x) i.val : ℤ) : F p) := by
  rw [BalancedZ.udigits, dif_pos i.isLt]
  simp only [Vector.getElem_map, Int.cast_natCast]
  exact (ZMod.natCast_zmod_val _).symm

/-- Windows on the difference `zlF − zrF` from the per-limb caps: the two-sided
`GroupedEqD` window. -/
lemma window_facts (hB1 : 1 ≤ B) (hm : 1 ≤ m)
    (V VR : GroupedEqV.VParams) (hNf : NfOkD (m := m) B tb tw V VR)
    (av qv nv rv : BigInt m (F p))
    (ha_norm : av.Normalized B) (ha_top : (av[m - 1]'(by omega)).val < 2 ^ tw)
    (hq_norm : qv.Normalized B) (hq_top : (qv[m - 1]'(by omega)).val < 2 ^ tb)
    (hn_norm : nv.Normalized B) (hn_top : (nv[m - 1]'(by omega)).val < 2 ^ tb)
    (hr_norm : rv.Normalized B) (hr_top : (rv[m - 1]'(by omega)).val < 2 ^ tw) :
    (∀ k, k < 2 * m - 1 → -(VR.Nf k : ℤ) < zlF B av k - zrF B qv nv rv k) ∧
    (∀ k, k < 2 * m - 1 → zlF B av k - zrF B qv nv rv k < (V.Nf k : ℤ)) := by
  have hza := BalancedZ.abs_zdigits_le hB1 hm av ha_norm ha_top
  have hzr := BalancedZ.abs_zdigits_le hB1 hm rv hr_norm hr_top
  have hzq := BalancedZ.abs_udigits_le_limbCap hm qv hq_norm hq_top
  have hzn := BalancedZ.abs_udigits_le_limbCap hm nv hn_norm hn_top
  have key : ∀ k, k < 2 * m - 1 →
      -(VR.Nf k : ℤ) < zlF B av k - zrF B qv nv rv k ∧
      zlF B av k - zrF B qv nv rv k < (V.Nf k : ℤ) := by
    intro k hk
    have hA := WindowCaps.abs_zconv_le m m _ _ _ _ hza hza k
    have hQ := WindowCaps.abs_zconv_le m m _ _ _ _ hzq hzn k
    have hQ0 := WindowCaps.zconv_nonneg m m _ _
      (BalancedZ.udigits_nonneg qv) (BalancedZ.udigits_nonneg nv) k
    have hP := hNf.1 k hk
    have hN := hNf.2 k hk
    rw [abs_le] at hA hQ
    unfold zlF zrF
    by_cases hkm : k < m
    · rw [if_pos hkm] at hP hN ⊢
      have hR := hzr k
      rw [abs_le] at hR
      have hP' : (WindowCaps.wconv m m (WindowCaps.balCap B tw m) (WindowCaps.balCap B tw m) k
          + WindowCaps.balCap B tw m k : ℤ) < (V.Nf k : ℤ) := by exact_mod_cast hP
      have hN' : (WindowCaps.wconv m m (WindowCaps.balCap B tw m) (WindowCaps.balCap B tw m) k
          + WindowCaps.wconv m m (WindowCaps.limbCap B tb m) (WindowCaps.limbCap B tb m) k
          + WindowCaps.balCap B tw m k : ℤ) < (VR.Nf k : ℤ) := by exact_mod_cast hN
      push_cast at hP' hN' ⊢
      constructor <;> omega
    · rw [if_neg hkm] at hP hN ⊢
      have hP' : (WindowCaps.wconv m m (WindowCaps.balCap B tw m) (WindowCaps.balCap B tw m) k
          : ℤ) < (V.Nf k : ℤ) := by exact_mod_cast (by omega : WindowCaps.wconv m m
            (WindowCaps.balCap B tw m) (WindowCaps.balCap B tw m) k < V.Nf k)
      have hN' : (WindowCaps.wconv m m (WindowCaps.balCap B tw m) (WindowCaps.balCap B tw m) k
          + WindowCaps.wconv m m (WindowCaps.limbCap B tb m) (WindowCaps.limbCap B tb m) k
          : ℤ) < (VR.Nf k : ℤ) := by exact_mod_cast (by omega : _ < VR.Nf k)
      push_cast at hP' hN' ⊢
      constructor <;> omega
  exact ⟨fun k hk => (key k hk).1, fun k hk => (key k hk).2⟩

/-- Evaluate one rhs coefficient (the `q·n` interpolation output plus a shifted
balanced `r`-digit on the low positions) as the field image of `zrF`. -/
lemma eval_rhsS (hB1 : 1 ≤ B) (hm : 1 ≤ m) (env : Environment (F p))
    (n : Var (BigInt m) (F p)) (i₀ : ℕ)
    (Qv : Vector (Expression (F p)) (2 * m - 1))
    (heqQ : ∀ k : Fin (2 * m - 1),
      Expression.eval env Qv[k.val]
        = Expression.eval env
            (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])
    (k : ℕ) (hk : k < 2 * m - 1) :
    Expression.eval env
      (if h : k < m then
          (if k = m - 1 then Qv[k]'hk + var { index := i₀ + m + k }
           else Qv[k]'hk + var { index := i₀ + m + k }
             - (((2 ^ (B - 1) : ℕ) : F p) : Expression (F p)))
        else Qv[k]'hk)
      = ((zrF B
            (Vector.map (Expression.eval env) (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i }))
            (Vector.map (Expression.eval env) n)
            (Vector.map (Expression.eval env) (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))
            k : ℤ) : F p) := by
  set qVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  set rVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i }) with hrVar
  have hQz : ∀ kk : Fin (2 * m - 1),
      Expression.eval env Qv[kk.val]
        = ((WindowCaps.zconv m m
            (BalancedZ.udigits (Vector.map (Expression.eval env) qVar))
            (BalancedZ.udigits (Vector.map (Expression.eval env) n)) kk.val : ℤ) : F p) := by
    intro kk
    rw [heqQ kk]
    exact WindowCaps.eval_bigIntMulNoReduce_intCast env qVar n _ _
      (fun i => eval_udigit env qVar i) (fun i => eval_udigit env n i) kk
  have hrget : ∀ (j : ℕ) (hj : j < m),
      Expression.eval env (var (F := F p) { index := i₀ + m + j })
        = (Vector.map (Expression.eval env) rVar)[j]'hj := by
    intro j hj
    simp [hrVar, circuit_norm]
  unfold zrF
  by_cases h : k < m
  · rw [dif_pos h, if_pos h]
    have hzd : BalancedZ.zdigits B (Vector.map (Expression.eval env) rVar) k
        = (if k = m - 1
            then (((Vector.map (Expression.eval env) rVar)[k]'h).val : ℤ)
            else (((Vector.map (Expression.eval env) rVar)[k]'h).val : ℤ) - 2 ^ (B - 1)) := by
      rw [BalancedZ.zdigits, dif_pos h]
    by_cases htop : k = m - 1
    · rw [if_pos htop]
      rw [show Expression.eval env (Qv[k]'hk + var { index := i₀ + m + k })
          = Expression.eval env (Qv[k]'hk)
            + Expression.eval env (var (F := F p) { index := i₀ + m + k }) from by
        simp [Expression.eval]]
      rw [hQz ⟨k, hk⟩, hrget k h, hzd, if_pos htop]
      push_cast
      rw [ZMod.natCast_zmod_val]
    · rw [if_neg htop]
      rw [show Expression.eval env (Qv[k]'hk + var { index := i₀ + m + k }
            - (((2 ^ (B - 1) : ℕ) : F p) : Expression (F p)))
          = Expression.eval env (Qv[k]'hk)
            + Expression.eval env (var (F := F p) { index := i₀ + m + k })
            - ((2 ^ (B - 1) : ℕ) : F p) from by
        simp only [Expression.eval]
        push_cast
        ring]
      rw [hQz ⟨k, hk⟩, hrget k h, hzd, if_neg htop]
      push_cast
      rw [ZMod.natCast_zmod_val]
      ring
  · rw [dif_neg h, if_neg h, hQz ⟨k, hk⟩]
    push_cast
    ring

/-- Pointwise variant of `eval_rhsS`: evaluate one rhs coefficient from a
single pinned `q·n` coefficient expression `Qk`. -/
lemma eval_rhsS_low (hB1 : 1 ≤ B) (hm : 1 ≤ m) (env : Environment (F p))
    (n : Var (BigInt m) (F p)) (i₀ : ℕ) (Qk : Expression (F p)) (k : ℕ) (hk : k < 2 * m - 1)
    (hQk : Expression.eval env Qk
        = ((WindowCaps.zconv m m
            (BalancedZ.udigits (Vector.map (Expression.eval env)
              (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i })))
            (BalancedZ.udigits (Vector.map (Expression.eval env) n)) k : ℤ) : F p)) :
    Expression.eval env
      (if h : k < m then
          (if k = m - 1 then Qk + var { index := i₀ + m + k }
           else Qk + var { index := i₀ + m + k }
             - (((2 ^ (B - 1) : ℕ) : F p) : Expression (F p)))
        else Qk)
      = ((zrF B
            (Vector.map (Expression.eval env) (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i }))
            (Vector.map (Expression.eval env) n)
            (Vector.map (Expression.eval env) (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))
            k : ℤ) : F p) := by
  set rVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i }) with hrVar
  have hrget : ∀ (j : ℕ) (hj : j < m),
      Expression.eval env (var (F := F p) { index := i₀ + m + j })
        = (Vector.map (Expression.eval env) rVar)[j]'hj := by
    intro j hj
    simp [hrVar, circuit_norm]
  unfold zrF
  by_cases h : k < m
  · rw [dif_pos h, if_pos h]
    have hzd : BalancedZ.zdigits B (Vector.map (Expression.eval env) rVar) k
        = (if k = m - 1
            then (((Vector.map (Expression.eval env) rVar)[k]'h).val : ℤ)
            else (((Vector.map (Expression.eval env) rVar)[k]'h).val : ℤ) - 2 ^ (B - 1)) := by
      rw [BalancedZ.zdigits, dif_pos h]
    by_cases htop : k = m - 1
    · rw [if_pos htop]
      rw [show Expression.eval env (Qk + var { index := i₀ + m + k })
          = Expression.eval env Qk
            + Expression.eval env (var (F := F p) { index := i₀ + m + k }) from by
        simp [Expression.eval]]
      rw [hQk, hrget k h, hzd, if_pos htop]
      push_cast
      rw [ZMod.natCast_zmod_val]
    · rw [if_neg htop]
      rw [show Expression.eval env (Qk + var { index := i₀ + m + k }
            - (((2 ^ (B - 1) : ℕ) : F p) : Expression (F p)))
          = Expression.eval env Qk
            + Expression.eval env (var (F := F p) { index := i₀ + m + k })
            - ((2 ^ (B - 1) : ℕ) : F p) from by
        simp only [Expression.eval]
        push_cast
        ring]
      rw [hQk, hrget k h, hzd, if_neg htop]
      push_cast
      rw [ZMod.natCast_zmod_val]
      ring
  · rw [dif_neg h, if_neg h, hQk]
    push_cast
    ring

/-- **Definitional-top glue.** Coordinatewise value of the reconstructed rhs
vector `rhsValD`: on the low positions it is the evaluated rhs shape (pinned
`q·n` coefficient plus the shifted balanced `r`-digit), and at the top it is
the evaluated affine reconstruction, which the interpolation pinning identifies
with the top `q·n` convolution coefficient. Both read as `zrF`-casts. -/
lemma rhsValD_bridge [Fact (p > 2)] (hB1 : 1 ≤ B) (hm2 : 2 ≤ m) (env : Environment (F p))
    (n : Var (BigInt m) (F p)) (i₀ : ℕ)
    (Pc' : Vector (Expression (F p)) (2 * m - 1))
    (sqnLow : Vector (Expression (F p)) (2 * m - 2))
    (hsqn : ∀ (k : ℕ) (hk : k < 2 * m - 1),
      Expression.eval env
          ((sqnVecD B Pc' sqnLow
            (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))[k]'hk)
        = ((WindowCaps.zconv m m
            (BalancedZ.udigits (Vector.map (Expression.eval env)
              (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i })))
            (BalancedZ.udigits (Vector.map (Expression.eval env) n)) k : ℤ) : F p)) :
    ∀ (k : ℕ) (hk : k < 2 * m - 1),
      (GroupedEqXV.rhsValD (L := 2 * m - 1) B
          (Vector.map (Expression.eval env) Pc')
          (Vector.map (Expression.eval env)
            (rhsSVecD B sqnLow
              (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))))[k]'hk
        = ((zrF B
              (Vector.map (Expression.eval env) (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i }))
              (Vector.map (Expression.eval env) n)
              (Vector.map (Expression.eval env) (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))
              k : ℤ) : F p) := by
  intro k hk
  set rT := (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }) with hrT
  have hbr := GroupedEqXV.rhsD_eval_bridge (L := 2 * m - 1) B env Pc' (rhsSVecD B sqnLow rT)
    (Vector.map (Expression.eval env) Pc')
    (Vector.map (Expression.eval env) (rhsSVecD B sqnLow rT))
    (fun j hj => by rw [Vector.getElem_map]) (fun j hj => by rw [Vector.getElem_map])
  rw [← hbr k hk]
  by_cases hklow : k < 2 * m - 1 - 1
  · rw [GroupedEqXV.rhsD_getElem_low (L := 2 * m - 1) B Pc' (rhsSVecD B sqnLow rT) k hklow]
    rw [hrT, rhsSVecD_getElem_low_var B sqnLow i₀ k (by omega)]
    have hQk := hsqn k hk
    rw [sqnVecD_getElem_low B Pc' sqnLow rT k (by omega)] at hQk
    exact eval_rhsS_low hB1 (by omega) env n i₀ (sqnLow[k]'(by omega)) k hk hQk
  · have hktop : k = 2 * m - 1 - 1 := by omega
    subst hktop
    rw [GroupedEqXV.rhsD_getElem_top (L := 2 * m - 1) B Pc' (rhsSVecD B sqnLow rT)]
    have hQk := hsqn (2 * m - 1 - 1) hk
    rw [sqnVecD_getElem_top B Pc' sqnLow rT] at hQk
    rw [hQk]
    unfold zrF
    rw [if_neg (by omega : ¬ (2 * m - 1 - 1 < m)), add_zero]

end Core

/-! ## The general formal circuit -/

set_option maxHeartbeats 16000000 in
/-- The balanced middle squaring battery: soundness needs only the window
checks on the inputs; completeness assumes `a` encodes a canonical residue and
exposes the honest fact that the output does too. -/
def generalCircuit (P : BigIntParams p m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htw : 1 ≤ tw ∧ 2 ^ tw < p)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : NfOkD (m := m) P.B tb tw V VR) [Fact (p > 2)] :
    GeneralFormalCircuit (F p) (Inputs m) (BigInt m) where
  main := main P tb tw htb htw htbB htwB gf posOf G V VR hgv
  Assumptions := fun input _ => SoundAssumptions P.B tb tw input
  Spec := fun input out _ => Spec P.B tw input out
  ProverAssumptions := fun input _ _ => Assumptions P.B tb tw input
  ProverSpec := fun input out _ => ProverSpec P.B input out
  soundness := by
    circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
      Normalize.Assumptions, Normalize.Spec,
      NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      NormalizeTight.Assumptions, NormalizeTight.Spec,
      GroupedEqD.circuitD_assumptions_eq, GroupedEqD.circuitD_spec_eq,
      GroupedEqD.AssumptionsD, GroupedEqD.SpecD]
    obtain ⟨ha_norm, hn_norm, ha_ltT, hn_ltT, hn_pos, hn_ge⟩ := h_assumptions
    obtain ⟨hq_tight, hr_tight, hPc_ops, hQN_ops, h_eq_impl⟩ := h_holds
    have hm : 0 < m := Nat.pos_of_neZero m
    have hm2 : 2 ≤ m := by
      have hgvx := hgv.1
      obtain ⟨hpos0, hposS, hgf1, _, _, _, hG3, hlast, _, _⟩ := hgvx
      have hposMono : ∀ a b, a ≤ b → posOf a ≤ posOf b :=
        fun a b hab => monotone_nat_of_le_succ (fun j => by rw [hposS j]; have := hgf1 j; omega) hab
      have h1 : posOf 1 = posOf 0 + gf 0 := hposS 0
      have h2 : posOf 2 = posOf 1 + gf 1 := hposS 1
      have hg0 := hgf1 0
      have hg1 := hgf1 1
      have := hposMono 2 (G - 1) (by omega)
      omega
    have hpm : 2 * m - 1 < p := MulMod.two_m_sub_one_lt P.hp
    have hmapa : Vector.map (Expression.eval env) input_var.a = input.a :=
      congrArg SquareModLazy.Inputs.a h_input
    have hmapn : Vector.map (Expression.eval env) input_var.modulus = input.modulus :=
      congrArg SquareModLazy.Inputs.modulus h_input
    set pcOff := i₀ + m + m + ((m - 1) * (P.B - 1) + (tb - 1)) + ((m - 1) * (P.B - 1) + (tw - 1)) with hpcOff
    set PcT := (MulMod.interpolatedMul (shiftedA P.B input_var.a) (shiftedA P.B input_var.a) pcOff).1 with hPcT
    set lowT := (Vector.mapRange (2 * m - 2) fun i => var (F := F p)
      { index := (pcOff
        + Operations.localLength (MulMod.interpolatedMul (shiftedA P.B input_var.a)
            (shiftedA P.B input_var.a) pcOff).2 + i) }) with hlowT
    have h_pPc := MulMod.interpolatedMul_soundness pcOff
      (shiftedA P.B input_var.a) (shiftedA P.B input_var.a) env hPc_ops
    have h_pQN := MulMod.interpolatedMulAssert_soundness _ _ _ _ env hQN_ops
    refine ⟨⟨hr_tight, ?_⟩, MulMod.interpolatedMul_requirements _ _ _ _,
      MulMod.interpolatedMulAssert_requirements _ _ _ _ _,
      Or.inl (GroupedEqD.circuitD_channels_req_eq _ _ _ _ _ _ _ _)⟩
    have heqPc_get := MulMod.interpolatedMul_eval_bridge env pcOff
      (shiftedA P.B input_var.a) (shiftedA P.B input_var.a) hpm h_pPc
    have heqQN_get := MulMod.interpolatedMulAssertZ_map_eval env _ _ _ hpm h_pQN
    -- evaluated q / r vectors
    set qv := Vector.map (Expression.eval env)
      (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i }) with hqv
    set rv := Vector.map (Expression.eval env)
      (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }) with hrv
    -- the signed lhs bridge
    have haS : ∀ i : Fin m, Expression.eval env ((shiftedA P.B input_var.a)[i.val]'i.isLt)
        = ((BalancedZ.zdigits P.B input.a i.val : ℤ) : F p) := by
      intro i
      rw [eval_shiftedA P.hB1 env input_var.a i, hmapa]
    have hL : ∀ (k : ℕ) (hk : k < 2 * m - 1),
        Expression.eval env (PcT[k]'hk)
          = ((zlF P.B input.a k : ℤ) : F p) := by
      intro k hk
      rw [hPcT, heqPc_get ⟨k, hk⟩]
      exact WindowCaps.eval_bigIntMulNoReduce_intCast env _ _ _ _ haS haS ⟨k, hk⟩
    have hsqn_pin : ∀ (k : ℕ) (hk : k < 2 * m - 1),
        Expression.eval env
          ((sqnVecD P.B PcT lowT
            (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))[k]'hk)
          = ((WindowCaps.zconv m m
              (BalancedZ.udigits (Vector.map (Expression.eval env)
                (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i })))
              (BalancedZ.udigits (Vector.map (Expression.eval env) input_var.modulus)) k : ℤ) : F p) := by
      intro k hk
      rw [heqQN_get ⟨k, hk⟩]
      exact WindowCaps.eval_bigIntMulNoReduce_intCast env _ _ _ _
        (fun i => eval_udigit env _ i) (fun i => eval_udigit env input_var.modulus i) ⟨k, hk⟩
    have hR0 := rhsValD_bridge P.hB1 hm2 env input_var.modulus i₀ PcT lowT hsqn_pin
    rw [hmapn, ← hqv, ← hrv] at hR0
    -- windows
    have ha_top : (input.a[m - 1]'(by omega)).val < 2 ^ tw :=
      WindowCaps.top_lt_of_value_lt ha_ltT
    have hn_top : (input.modulus[m - 1]'(by omega)).val < 2 ^ tb :=
      WindowCaps.top_lt_of_value_lt hn_ltT
    have hwin := window_facts (tb := tb) (tw := tw) P.hB1 hm V VR hNf
      input.a qv input.modulus rv ha_norm ha_top hq_tight.1 hq_tight.2 hn_norm hn_top
      hr_tight.1 hr_tight.2
    have hNfp : ∀ j, j < 2 * m - 1 → V.Nf j + VR.Nf j ≤ p := fun j hj => hgv.2 j hj
    have hspec := h_eq_impl (by
      intro k
      refine ⟨zlF P.B input.a k.val - zrF P.B qv input.modulus rv k.val, ?_,
        hwin.1 k.val k.isLt, hwin.2 k.val k.isLt⟩
      rw [hL k.val k.isLt, hR0 k.val k.isLt]
      push_cast
      ring)
    have hzsum : (∑ k ∈ Finset.range (2 * m - 1),
        (zlF P.B input.a k - zrF P.B qv input.modulus rv k) * 2 ^ (P.B * k)) = 0 := by
      rw [← Fin.sum_univ_eq_sum_range (fun k =>
        (zlF P.B input.a k - zrF P.B qv input.modulus rv k) * 2 ^ (P.B * k))]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hspec
      congr 1
      exact (GroupedEqD.zsval_eq_of_window (by
          rw [hL k.val k.isLt, hR0 k.val k.isLt]
          push_cast
          ring)
        (hwin.1 k.val k.isLt) (hwin.2 k.val k.isLt) (hNfp k.val k.isLt)).symm
    -- convert to the value identity
    have hsplit := BalancedZ.zsquare_sum_split P.B m hm (BalancedZ.zdigits P.B input.a)
      (BalancedZ.udigits qv) (BalancedZ.udigits input.modulus) (BalancedZ.zdigits P.B rv)
    rw [BalancedZ.sum_zdigits P.B hm input.a, BalancedZ.sum_udigits P.B qv,
      BalancedZ.sum_udigits P.B input.modulus, BalancedZ.sum_zdigits P.B hm rv] at hsplit
    have hzero : BalancedZ.VZ P.B input.a * BalancedZ.VZ P.B input.a
        - ((BigInt.value P.B qv : ℤ) * (BigInt.value P.B input.modulus : ℤ) + BalancedZ.VZ P.B rv)
          = 0 := by
      rw [← hsplit]
      simpa only [zlF, zrF] using hzsum
    exact BalancedZ.modEq_of_identity (Q := (BigInt.value P.B qv : ℤ)) (by linarith)
  completeness := by
    circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
      Normalize.Assumptions, Normalize.Spec,
      NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      NormalizeTight.Assumptions, NormalizeTight.Spec,
      GroupedEqD.circuitD_assumptions_eq, GroupedEqD.circuitD_spec_eq,
      GroupedEqD.AssumptionsD, GroupedEqD.SpecD]
    obtain ⟨⟨ha_norm, hn_norm, ha_ltT, hn_ltT, hn_pos, hn_ge⟩, hbal_le, hbal_lt⟩ := h_assumptions
    obtain ⟨hq_env, hr_env, hPc_uses, hsqn_env, -⟩ := h_env
    have hm : 0 < m := Nat.pos_of_neZero m
    have hm2 : 2 ≤ m := by
      have hgvx := hgv.1
      obtain ⟨hpos0, hposS, hgf1, _, _, _, hG3, hlast, _, _⟩ := hgvx
      have hposMono : ∀ a b, a ≤ b → posOf a ≤ posOf b :=
        fun a b hab => monotone_nat_of_le_succ (fun j => by rw [hposS j]; have := hgf1 j; omega) hab
      have h1 : posOf 1 = posOf 0 + gf 0 := hposS 0
      have h2 : posOf 2 = posOf 1 + gf 1 := hposS 1
      have hg0 := hgf1 0
      have hg1 := hgf1 1
      have := hposMono 2 (G - 1) (by omega)
      omega
    have hpm : 2 * m - 1 < p := MulMod.two_m_sub_one_lt P.hp
    have hmapa : Vector.map (Expression.eval env.toEnvironment) input_var.a = input.a :=
      congrArg SquareModLazy.Inputs.a h_input
    have hmapn : Vector.map (Expression.eval env.toEnvironment) input_var.modulus = input.modulus :=
      congrArg SquareModLazy.Inputs.modulus h_input
    set pcOff := i₀ + m + m + ((m - 1) * (P.B - 1) + (tb - 1)) + ((m - 1) * (P.B - 1) + (tw - 1)) with hpcOff
    set PcT := (MulMod.interpolatedMul (shiftedA P.B input_var.a) (shiftedA P.B input_var.a) pcOff).1 with hPcT
    set lowT := (Vector.mapRange (2 * m - 2) fun i => var (F := F p)
      { index := (pcOff
        + Operations.localLength (MulMod.interpolatedMul (shiftedA P.B input_var.a)
            (shiftedA P.B input_var.a) pcOff).2 + i) }) with hlowT
    have h_pvPc := MulMod.interpolatedMul_usesLocalWitnesses pcOff pcOff
      (shiftedA P.B input_var.a) (shiftedA P.B input_var.a) env rfl hPc_uses
    have hsqnwit : ∀ i : Fin (2 * m - 2),
        env.toEnvironment.get (Operations.localLength (MulMod.interpolatedMul (shiftedA P.B input_var.a)
            (shiftedA P.B input_var.a) pcOff).2 + pcOff + i.val)
          = Expression.eval env.toEnvironment
              ((bigIntMulNoReduce (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i })
                input_var.modulus)[i.val]'(by have := i.isLt; omega)) := by
      intro i
      have h := hsqn_env i
      rwa [Vector.getElem_ofFn] at h
    have heva : evalValue P.B env input_var.a = BigInt.value P.B input.a := by
      rw [evalValue, BigInt.value, ← h_input]
    have hevn : evalValue P.B env input_var.modulus = BigInt.value P.B input.modulus := by
      rw [evalValue, BigInt.value, ← h_input]
    set vN := BigInt.value P.B input.a - BalancedZ.balShift P.B m with hvN
    set nval := BigInt.value P.B input.modulus with hnval
    have hqwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + i.val)
        = ((vN * vN / nval / 2 ^ (P.B * i.val) % 2 ^ P.B : ℕ) : F p) := by
      intro i
      rw [hq_env i, Vector.getElem_ofFn, heva, hevn]
    have hrwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + m + i.val)
        = (((vN * vN % nval + BalancedZ.balShift P.B m) / 2 ^ (P.B * i.val) % 2 ^ P.B : ℕ) : F p) := by
      intro i
      rw [hr_env i, Vector.getElem_ofFn, heva, hevn]
    -- q is tight-normalized
    have hvN_lt_n : vN < nval := hbal_lt
    have hvN_ltT : vN < 2 ^ ((m - 1) * P.B + tb) := lt_trans hvN_lt_n hn_ltT
    have hqtight := MulMod.qwit_tight_lt (B := P.B) (tb := tb) (tq := tb) P.hB
      (Nat.le_of_succ_le htbB) (le_refl tb) i₀ env.toEnvironment vN vN nval
      hvN_ltT hvN_lt_n hqwit
    have hq_norm := hqtight.1
    -- r block: value / normalization / top window
    set rval := vN * vN % nval with hrval
    set Nr := rval + BalancedZ.balShift P.B m with hNr
    have hrval_lt : rval < nval := Nat.mod_lt _ hn_pos
    have hrval_ltw : rval < 2 ^ ((m - 1) * P.B + tw - 1) := by
      have h1 : (2 : ℕ) ^ ((m - 1) * P.B + tb) ≤ 2 ^ ((m - 1) * P.B + tw - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      exact lt_of_lt_of_le (lt_trans hrval_lt hn_ltT) h1
    have hNr_lt : Nr < 2 ^ ((m - 1) * P.B + tw) :=
      BalancedZ.add_balShift_lt P.B m tw rval P.hB1 htw.1 hrval_ltw
    have hNr_ltBm : Nr < 2 ^ (P.B * m) := by
      refine lt_of_lt_of_le hNr_lt (Nat.pow_le_pow_right (by norm_num) ?_)
      have h1 : (m - 1) * P.B + P.B = m * P.B := by
        calc (m - 1) * P.B + P.B = ((m - 1) + 1) * P.B := by ring
          _ = m * P.B := by rw [show m - 1 + 1 = m from by omega]
      have h2 : m * P.B = P.B * m := Nat.mul_comm m P.B
      omega
    have hr_norm := MulMod.normalized_mapRange (i₀ + m) Nr env.toEnvironment P.hB
      (fun i => hrwit i)
    have hr_val := BigInt.value_mapRange (i₀ + m) Nr env.toEnvironment P.hB hNr_ltBm
      (fun i => hrwit i)
    have hr_top : ((Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))[m - 1]'(by
          omega)).val < 2 ^ tw := by
      have hget : (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i }))[m - 1]'(by omega)
            = env.toEnvironment.get (i₀ + m + (m - 1)) := by
        simp [circuit_norm]
      rw [hget, hrwit ⟨m - 1, by omega⟩,
        ZMod.val_natCast_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos P.B)) P.hB.le)]
      calc Nr / 2 ^ (P.B * (m - 1)) % 2 ^ P.B ≤ Nr / 2 ^ (P.B * (m - 1)) := Nat.mod_le _ _
        _ < 2 ^ tw := by
            apply Nat.div_lt_of_lt_mul
            rw [show (2 : ℕ) ^ (P.B * (m - 1)) * 2 ^ tw = 2 ^ ((m - 1) * P.B + tw) from by
              rw [← pow_add]; congr 1; ring]
            exact hNr_lt
    have hrtight : BigInt.NormalizedTight P.B tw (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i })) :=
      ⟨hr_norm, hr_top⟩
    -- eval bridges (prover side)
    have heqPc_get := MulMod.interpolatedMul_eval_bridge_uses env.toEnvironment pcOff
      (shiftedA P.B input_var.a) (shiftedA P.B input_var.a) h_pvPc
    set qv := Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i }) with hqv
    set rv := Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }) with hrv
    have haS : ∀ i : Fin m,
        Expression.eval env.toEnvironment ((shiftedA P.B input_var.a)[i.val]'i.isLt)
          = ((BalancedZ.zdigits P.B input.a i.val : ℤ) : F p) := by
      intro i
      rw [eval_shiftedA P.hB1 env.toEnvironment input_var.a i, hmapa]
    have hL : ∀ (k : ℕ) (hk : k < 2 * m - 1),
        Expression.eval env.toEnvironment (PcT[k]'hk)
          = ((zlF P.B input.a k : ℤ) : F p) := by
      intro k hk
      rw [hPcT, heqPc_get ⟨k, hk⟩]
      exact WindowCaps.eval_bigIntMulNoReduce_intCast env.toEnvironment _ _ _ _ haS haS ⟨k, hk⟩
    have hQzU : ∀ k : Fin (2 * m - 1),
        Expression.eval env.toEnvironment
            ((bigIntMulNoReduce (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i })
              input_var.modulus)[k.val])
          = ((WindowCaps.zconv m m
              (BalancedZ.udigits (Vector.map (Expression.eval env.toEnvironment)
                (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i })))
              (BalancedZ.udigits (Vector.map (Expression.eval env.toEnvironment) input_var.modulus))
              k.val : ℤ) : F p) :=
      fun k => WindowCaps.eval_bigIntMulNoReduce_intCast env.toEnvironment _ _ _ _
        (fun i => eval_udigit env.toEnvironment _ i)
        (fun i => eval_udigit env.toEnvironment input_var.modulus i) k
    -- windows
    have ha_top : (input.a[m - 1]'(by omega)).val < 2 ^ tw :=
      WindowCaps.top_lt_of_value_lt ha_ltT
    have hn_top : (input.modulus[m - 1]'(by omega)).val < 2 ^ tb :=
      WindowCaps.top_lt_of_value_lt hn_ltT
    have hwin := window_facts (tb := tb) (tw := tw) P.hB1 hm V VR hNf
      input.a qv input.modulus rv ha_norm ha_top hqtight.1 hqtight.2 hn_norm hn_top
      hrtight.1 hrtight.2
    have hNfp : ∀ j, j < 2 * m - 1 → V.Nf j + VR.Nf j ≤ p := fun j hj => hgv.2 j hj
    -- the ℤ identity, honest side: vN² = q·n + rval
    have hqv_val : BigInt.value P.B qv = vN * vN / nval := by
      have hqval_lt : vN * vN / nval < 2 ^ (P.B * m) := by
        have h1 : vN * vN / nval < 2 ^ ((m - 1) * P.B + tb) := by
          rcases Nat.eq_zero_or_pos vN with h0 | h0
          · rw [h0, Nat.zero_mul, Nat.zero_div]
            positivity
          · have h2 : vN * vN < nval * vN := by
              exact Nat.mul_lt_mul_of_lt_of_le hvN_lt_n (le_refl vN) h0
            have h3 : vN * vN / nval < vN := Nat.div_lt_of_lt_mul (by
              calc vN * vN < nval * vN := h2
                _ = nval * vN := rfl)
            exact lt_trans h3 hvN_ltT
        refine lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) ?_)
        have h4 : (m - 1) * P.B + P.B = m * P.B := by
          calc (m - 1) * P.B + P.B = ((m - 1) + 1) * P.B := by ring
            _ = m * P.B := by rw [show m - 1 + 1 = m from by omega]
        have h5 : m * P.B = P.B * m := Nat.mul_comm m P.B
        have h6 : tb ≤ P.B := Nat.le_of_succ_le htbB
        omega
      exact BigInt.value_mapRange i₀ (vN * vN / nval) env.toEnvironment P.hB hqval_lt
        (fun i => hqwit i)
    have hVZa : BalancedZ.VZ P.B input.a = (vN : ℤ) := by
      rw [BalancedZ.VZ, hvN]
      push_cast [Nat.cast_sub hbal_le]
      ring
    have hVZr : BalancedZ.VZ P.B rv = (rval : ℤ) := by
      rw [BalancedZ.VZ, hr_val, hNr]
      push_cast
      ring
    have hidN : (vN * vN / nval) * nval + rval = vN * vN := by
      rw [hrval, Nat.mul_comm]
      exact Nat.div_add_mod _ _
    have hzero : (∑ k ∈ Finset.range (2 * m - 1),
        (zlF P.B input.a k - zrF P.B qv input.modulus rv k) * 2 ^ (P.B * k)) = 0 := by
      have hsplit := BalancedZ.zsquare_sum_split P.B m hm (BalancedZ.zdigits P.B input.a)
        (BalancedZ.udigits qv) (BalancedZ.udigits input.modulus) (BalancedZ.zdigits P.B rv)
      rw [BalancedZ.sum_zdigits P.B hm input.a, BalancedZ.sum_udigits P.B qv,
        BalancedZ.sum_udigits P.B input.modulus, BalancedZ.sum_zdigits P.B hm rv,
        hVZa, hVZr, hqv_val] at hsplit
      have hcast : ((vN : ℤ) * vN) = ((vN * vN / nval : ℕ) : ℤ) * (nval : ℤ) + (rval : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hidN.symm
      simp only [zlF, zrF]
      rw [hsplit, ← hnval]
      linarith
    have hSlow : ∀ (k : ℕ) (hk : k < 2 * m - 1 - 1),
        Expression.eval env.toEnvironment
            ((rhsSVecD P.B lowT
              (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))[k]'(by omega))
          = ((zrF P.B qv input.modulus rv k : ℤ) : F p) := by
      intro k hk
      rw [rhsSVecD_getElem_low_var P.B lowT i₀ k (by omega)]
      have hQk : Expression.eval env.toEnvironment (lowT[k]'(by omega))
          = ((WindowCaps.zconv m m
              (BalancedZ.udigits (Vector.map (Expression.eval env.toEnvironment)
                (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i })))
              (BalancedZ.udigits (Vector.map (Expression.eval env.toEnvironment) input_var.modulus))
              k : ℤ) : F p) := by
        have hswap : (pcOff + Operations.localLength (MulMod.interpolatedMul
              (shiftedA P.B input_var.a) (shiftedA P.B input_var.a) pcOff).2 + k)
            = (Operations.localLength (MulMod.interpolatedMul
              (shiftedA P.B input_var.a) (shiftedA P.B input_var.a) pcOff).2 + pcOff + k) := by
          omega
        have hget : Expression.eval env.toEnvironment (lowT[k]'(by omega))
            = env.toEnvironment.get (Operations.localLength (MulMod.interpolatedMul
                (shiftedA P.B input_var.a) (shiftedA P.B input_var.a) pcOff).2 + pcOff + k) := by
          rw [hlowT, Vector.getElem_mapRange, hswap]
          rfl
        rw [hget, hsqnwit ⟨k, by omega⟩]
        exact hQzU ⟨k, by omega⟩
      have h1 := eval_rhsS_low P.hB1 hm env.toEnvironment input_var.modulus i₀
        (lowT[k]'(by omega)) k (by omega) hQk
      rw [hmapn, ← hqv, ← hrv] at h1
      exact h1
    have hStop : Expression.eval env.toEnvironment
        (GroupedEqXV.topExprD (L := 2 * m - 1) P.B PcT
          (rhsSVecD P.B lowT (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i })))
        = ((zrF P.B qv input.modulus rv (2 * m - 1 - 1) : ℤ) : F p) :=
      GroupedEqXV.topExprD_eval_of_sum_eq_zero (L := 2 * m - 1) P.B env.toEnvironment
        PcT (rhsSVecD P.B lowT (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))
        (fun k => zlF P.B input.a k) (fun k => zrF P.B qv input.modulus rv k)
        hL hSlow hzero
    have hsqn_pin_all : ∀ k : Fin (2 * m - 1),
        Expression.eval env.toEnvironment
            ((sqnVecD P.B PcT lowT
              (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))[k.val])
          = Expression.eval env.toEnvironment
              ((bigIntMulNoReduce (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i })
                input_var.modulus)[k.val]) := by
      intro k
      by_cases hklow : k.val < 2 * m - 2
      · rw [sqnVecD_getElem_low P.B PcT lowT _ k.val hklow]
        rw [hlowT, Vector.getElem_mapRange]
        show env.toEnvironment.get _ = _
        rw [show pcOff + Operations.localLength (MulMod.interpolatedMul (shiftedA P.B input_var.a)
              (shiftedA P.B input_var.a) pcOff).2 + k.val
            = Operations.localLength (MulMod.interpolatedMul (shiftedA P.B input_var.a)
              (shiftedA P.B input_var.a) pcOff).2 + pcOff + k.val from by omega]
        exact hsqnwit ⟨k.val, hklow⟩
      · have hktop : k.val = 2 * m - 1 - 1 := by have := k.isLt; omega
        have h1 : ∀ (j : ℕ) (hj : j < 2 * m - 1), j = 2 * m - 1 - 1 →
            (sqnVecD P.B PcT lowT
              (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))[j]'hj
              = GroupedEqXV.topExprD (L := 2 * m - 1) P.B PcT
                  (rhsSVecD P.B lowT (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i })) := by
          intro j hj hjeq
          subst hjeq
          exact sqnVecD_getElem_top P.B PcT lowT _
        rw [h1 k.val k.isLt hktop, hStop, hQzU k]
        rw [show BalancedZ.udigits (Vector.map (Expression.eval env.toEnvironment)
              (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i }))
            = BalancedZ.udigits qv from by rw [hqv]]
        rw [show BalancedZ.udigits (Vector.map (Expression.eval env.toEnvironment) input_var.modulus)
            = BalancedZ.udigits input.modulus from by rw [hmapn]]
        unfold zrF
        rw [if_neg (by omega : ¬ (2 * m - 1 - 1 < m)), add_zero, hktop]
    have hsqn_pinC : ∀ (k : ℕ) (hk : k < 2 * m - 1),
        Expression.eval env.toEnvironment
            ((sqnVecD P.B PcT lowT
              (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))[k]'hk)
          = ((WindowCaps.zconv m m
              (BalancedZ.udigits (Vector.map (Expression.eval env.toEnvironment)
                (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i })))
              (BalancedZ.udigits (Vector.map (Expression.eval env.toEnvironment) input_var.modulus))
              k : ℤ) : F p) := by
      intro k hk
      rw [hsqn_pin_all ⟨k, hk⟩]
      exact hQzU ⟨k, hk⟩
    have hR0 := rhsValD_bridge P.hB1 hm2 env.toEnvironment input_var.modulus i₀ PcT lowT hsqn_pinC
    rw [hmapn, ← hqv, ← hrv] at hR0
    refine ⟨⟨hqtight, hrtight,
      MulMod.interpolatedMul_completeness _ (shiftedA P.B input_var.a) (shiftedA P.B input_var.a) env h_pvPc,
      MulMod.interpolatedMulAssert_completeness _ (Vector.mapRange m fun i => var { index := i₀ + i })
        input_var.modulus _ env hsqn_pin_all,
      ?_, ?_⟩, ?_, ?_⟩
    · -- GroupedEqD.Assumptions
      intro k
      refine ⟨zlF P.B input.a k.val - zrF P.B qv input.modulus rv k.val, ?_,
        hwin.1 k.val k.isLt, hwin.2 k.val k.isLt⟩
      rw [hL k.val k.isLt, hR0 k.val k.isLt]
      push_cast
      ring
    · -- GroupedEqD.Spec (the zsval difference sum vanishes)
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_)
        (Eq.trans (Fin.sum_univ_eq_sum_range (fun k =>
          (zlF P.B input.a k - zrF P.B qv input.modulus rv k) * 2 ^ (P.B * k)) (2 * m - 1)) hzero)
      congr 1
      exact GroupedEqD.zsval_eq_of_window (by
          rw [hL k.val k.isLt, hR0 k.val k.isLt]
          push_cast
          ring)
        (hwin.1 k.val k.isLt) (hwin.2 k.val k.isLt) (hNfp k.val k.isLt)
    · rw [hr_val, hNr]
      omega
    · rw [hr_val, hNr]
      omega
end SquareModBalGT

namespace SquareModBalFirstGT

open SquareModLazy (Inputs)
open SquareModBalGT (zrF eval_rhsS eval_udigit)

/-- The first battery: unsigned tight input `a` (`sig < n`), balanced output. -/
def main (P : BigIntParams p m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htw : 1 ≤ tw ∧ 2 ^ tw < p)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m - 1) P.B gf posOf G V VR)
    [Fact (p > 2)] (input : Var (Inputs m) (F p)) :
    Circuit (F p) (Var (BigInt m) (F p)) := do
  let a := input.a
  let n := input.modulus

  let q ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := SquareModBalGT.evalValue P.B env a * SquareModBalGT.evalValue P.B env a
    let qval : ℕ := prod / SquareModBalGT.evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let r ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := SquareModBalGT.evalValue P.B env a * SquareModBalGT.evalValue P.B env a
    let rval : ℕ := prod % SquareModBalGT.evalValue P.B env n + BalancedZ.balShift P.B m
    Vector.ofFn fun k : Fin m => ((rval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  NormalizeTight.circuit P tb htb (Nat.le_of_succ_le htbB) q
  NormalizeTight.circuit P tw htw htwB r

  let Pc ← MulMod.interpolatedMul a a
  let sqnLow ← ProvableType.witness (α := fields (2 * m - 2)) fun env =>
    Vector.ofFn fun k : Fin (2 * m - 2) =>
      Expression.eval env.toEnvironment
        ((bigIntMulNoReduce q n)[k.val]'(by have := k.isLt; omega))
  MulMod.interpolatedMulAssert q n (SquareModBalGT.sqnVecD P.B Pc sqnLow r)
  GroupedEqD.circuitD (L := 2 * m - 1) P.B gf posOf G V VR hgv P.hB1
    { lhs := Pc, rhs := SquareModBalGT.rhsSVecD P.B sqnLow r }
  return r

instance elaborated (P : BigIntParams p m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htw : 1 ≤ tw ∧ 2 ^ tw < p)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m - 1) P.B gf posOf G V VR) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) (BigInt m)
      (main P tb tw htb htw htbB htwB gf posOf G V VR hgv) where
  localLength _ :=
    m + m + ((m - 1) * (P.B - 1) + (tb - 1)) + ((m - 1) * (P.B - 1) + (tw - 1))
      + (2 * m - 1) + (2 * m - 2)
      + GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0
  output _ i0 := varFromOffset (BigInt m) (i0 + m)
  localLength_eq := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, MulMod.interpolatedMulAssert, circuit_norm,
      Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, GroupedEqD.circuitD, GroupedEqD.elaboratedD, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]
    omega
  output_eq := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, MulMod.interpolatedMulAssert, circuit_norm,
      Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, GroupedEqD.circuitD, GroupedEqD.elaboratedD, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, MulMod.interpolatedMul, MulMod.interpolatedMulAssert, circuit_norm,
      Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, GroupedEqD.circuitD, GroupedEqD.elaboratedD, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, MulMod.interpolatedMulAssert, circuit_norm,
      Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, GroupedEqD.circuitD, GroupedEqD.elaboratedD, RangeCheck.circuit,
      Gadgets.ToBits.rangeCheck]

/-- Verifier-side assumptions (as for the old tight first squaring). -/
def SoundAssumptions (B tb : ℕ) (input : Inputs m (F p)) : Prop :=
  input.a.Normalized B ∧ input.modulus.Normalized B ∧
    input.a.value B < 2 ^ ((m - 1) * B + tb) ∧
    input.modulus.value B < 2 ^ ((m - 1) * B + tb) ∧
    0 < input.modulus.value B ∧
    2 ^ ((m - 1) * B + tb - 1) ≤ input.modulus.value B

/-- Honest-prover assumptions: additionally `a < n` (canonical first operand). -/
def Assumptions (B tb : ℕ) (input : Inputs m (F p)) : Prop :=
  SoundAssumptions B tb input ∧ input.a.value B < input.modulus.value B

/-- Postcondition: the balanced output reads congruent to `a.value²` mod `n`. -/
def Spec (B tw : ℕ) (input : Inputs m (F p)) (out : BigInt m (F p)) : Prop :=
  BigInt.NormalizedTight B tw out ∧
    BalancedZ.VZ B out ≡ (input.a.value B : ℤ) * (input.a.value B : ℤ)
      [ZMOD (input.modulus.value B : ℤ)]

/-- Honest-prover side fact: the output encodes the canonical remainder. -/
def ProverSpec (B : ℕ) (input : Inputs m (F p)) (out : BigInt m (F p)) : Prop :=
  BalancedZ.balShift B m ≤ out.value B ∧
    out.value B - BalancedZ.balShift B m < input.modulus.value B

/-- Adequacy of the two-sided window bounds for the first battery: both flanks
dominate the unsigned square window plus one balanced `r`-digit (the lhs is
nonnegative, so the two flanks coincide). -/
def NfOkF (B tb tw : ℕ) (V VR : GroupedEqV.VParams) : Prop :=
  (∀ j, j < 2 * m - 1 →
    WindowCaps.wconv m m (WindowCaps.limbCap B tb m) (WindowCaps.limbCap B tb m) j
      + (if j < m then WindowCaps.balCap B tw m j else 0) < V.Nf j) ∧
  (∀ j, j < 2 * m - 1 →
    WindowCaps.wconv m m (WindowCaps.limbCap B tb m) (WindowCaps.limbCap B tb m) j
      + (if j < m then WindowCaps.balCap B tw m j else 0) < VR.Nf j)

section Core
variable {B tb tw : ℕ}

/-- The unsigned lhs digit-convolution family. -/
def zlFU (av : BigInt m (F p)) : ℕ → ℤ :=
  fun k => WindowCaps.zconv m m (BalancedZ.udigits av) (BalancedZ.udigits av) k

/-- Windows on the difference for the first battery. -/
lemma window_factsU (hB1 : 1 ≤ B) (hm : 1 ≤ m)
    (V VR : GroupedEqV.VParams) (hNf : NfOkF (m := m) B tb tw V VR)
    (av qv nv rv : BigInt m (F p))
    (ha_norm : av.Normalized B) (ha_top : (av[m - 1]'(by omega)).val < 2 ^ tb)
    (hq_norm : qv.Normalized B) (hq_top : (qv[m - 1]'(by omega)).val < 2 ^ tb)
    (hn_norm : nv.Normalized B) (hn_top : (nv[m - 1]'(by omega)).val < 2 ^ tb)
    (hr_norm : rv.Normalized B) (hr_top : (rv[m - 1]'(by omega)).val < 2 ^ tw) :
    (∀ k, k < 2 * m - 1 → -(VR.Nf k : ℤ) < zlFU av k - zrF B qv nv rv k) ∧
    (∀ k, k < 2 * m - 1 → zlFU av k - zrF B qv nv rv k < (V.Nf k : ℤ)) := by
  have hza := BalancedZ.abs_udigits_le_limbCap hm av ha_norm ha_top
  have hzr := BalancedZ.abs_zdigits_le hB1 hm rv hr_norm hr_top
  have hzq := BalancedZ.abs_udigits_le_limbCap hm qv hq_norm hq_top
  have hzn := BalancedZ.abs_udigits_le_limbCap hm nv hn_norm hn_top
  have key : ∀ k, k < 2 * m - 1 →
      -(VR.Nf k : ℤ) < zlFU av k - zrF B qv nv rv k ∧
      zlFU av k - zrF B qv nv rv k < (V.Nf k : ℤ) := by
    intro k hk
    have hA := WindowCaps.abs_zconv_le m m _ _ _ _ hza hza k
    have hA0 := WindowCaps.zconv_nonneg m m _ _
      (BalancedZ.udigits_nonneg av) (BalancedZ.udigits_nonneg av) k
    have hQ := WindowCaps.abs_zconv_le m m _ _ _ _ hzq hzn k
    have hQ0 := WindowCaps.zconv_nonneg m m _ _
      (BalancedZ.udigits_nonneg qv) (BalancedZ.udigits_nonneg nv) k
    have hP := hNf.1 k hk
    have hN := hNf.2 k hk
    rw [abs_le] at hA hQ
    unfold zlFU zrF
    by_cases hkm : k < m
    · rw [if_pos hkm] at hP hN ⊢
      have hR := hzr k
      rw [abs_le] at hR
      have hP' : (WindowCaps.wconv m m (WindowCaps.limbCap B tb m) (WindowCaps.limbCap B tb m) k
          + WindowCaps.balCap B tw m k : ℤ) < (V.Nf k : ℤ) := by exact_mod_cast hP
      have hN' : (WindowCaps.wconv m m (WindowCaps.limbCap B tb m) (WindowCaps.limbCap B tb m) k
          + WindowCaps.balCap B tw m k : ℤ) < (VR.Nf k : ℤ) := by exact_mod_cast hN
      push_cast at hP' hN' ⊢
      constructor <;> omega
    · rw [if_neg hkm] at hP hN ⊢
      have hP' : (WindowCaps.wconv m m (WindowCaps.limbCap B tb m) (WindowCaps.limbCap B tb m) k
          : ℤ) < (V.Nf k : ℤ) := by exact_mod_cast (by omega : WindowCaps.wconv m m
            (WindowCaps.limbCap B tb m) (WindowCaps.limbCap B tb m) k < V.Nf k)
      have hN' : (WindowCaps.wconv m m (WindowCaps.limbCap B tb m) (WindowCaps.limbCap B tb m) k
          : ℤ) < (VR.Nf k : ℤ) := by exact_mod_cast (by omega : _ < VR.Nf k)
      push_cast at hP' hN' ⊢
      constructor <;> omega
  exact ⟨fun k hk => (key k hk).1, fun k hk => (key k hk).2⟩

end Core

set_option maxHeartbeats 16000000 in
/-- The first battery as a general formal circuit: soundness needs the usual
tight-square assumptions; completeness additionally assumes `a < n` and exposes
the canonical-remainder fact for the balanced output. -/
def generalCircuit (P : BigIntParams p m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htw : 1 ≤ tw ∧ 2 ^ tw < p)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : NfOkF (m := m) P.B tb tw V VR) [Fact (p > 2)] :
    GeneralFormalCircuit (F p) (Inputs m) (BigInt m) where
  main := main P tb tw htb htw htbB htwB gf posOf G V VR hgv
  Assumptions := fun input _ => SoundAssumptions P.B tb input
  Spec := fun input out _ => Spec P.B tw input out
  ProverAssumptions := fun input _ _ => Assumptions P.B tb input
  ProverSpec := fun input out _ => ProverSpec P.B input out
  soundness := by
    circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
      Normalize.Assumptions, Normalize.Spec,
      NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      NormalizeTight.Assumptions, NormalizeTight.Spec,
      GroupedEqD.circuitD_assumptions_eq, GroupedEqD.circuitD_spec_eq,
      GroupedEqD.AssumptionsD, GroupedEqD.SpecD]
    obtain ⟨ha_norm, hn_norm, ha_ltT, hn_ltT, hn_pos, hn_ge⟩ := h_assumptions
    obtain ⟨hq_tight, hr_tight, hPc_ops, hQN_ops, h_eq_impl⟩ := h_holds
    have hm : 0 < m := Nat.pos_of_neZero m
    have hm2 : 2 ≤ m := by
      have hgvx := hgv.1
      obtain ⟨hpos0, hposS, hgf1, _, _, _, hG3, hlast, _, _⟩ := hgvx
      have hposMono : ∀ a b, a ≤ b → posOf a ≤ posOf b :=
        fun a b hab => monotone_nat_of_le_succ (fun j => by rw [hposS j]; have := hgf1 j; omega) hab
      have h1 : posOf 1 = posOf 0 + gf 0 := hposS 0
      have h2 : posOf 2 = posOf 1 + gf 1 := hposS 1
      have hg0 := hgf1 0
      have hg1 := hgf1 1
      have := hposMono 2 (G - 1) (by omega)
      omega
    have hpm : 2 * m - 1 < p := MulMod.two_m_sub_one_lt P.hp
    have hmapa : Vector.map (Expression.eval env) input_var.a = input.a :=
      congrArg SquareModLazy.Inputs.a h_input
    have hmapn : Vector.map (Expression.eval env) input_var.modulus = input.modulus :=
      congrArg SquareModLazy.Inputs.modulus h_input
    set pcOff := i₀ + m + m + ((m - 1) * (P.B - 1) + (tb - 1)) + ((m - 1) * (P.B - 1) + (tw - 1)) with hpcOff
    set PcT := (MulMod.interpolatedMul input_var.a input_var.a pcOff).1 with hPcT
    set lowT := (Vector.mapRange (2 * m - 2) fun i => var (F := F p)
      { index := (pcOff
        + Operations.localLength (MulMod.interpolatedMul input_var.a
            input_var.a pcOff).2 + i) }) with hlowT
    have h_pPc := MulMod.interpolatedMul_soundness pcOff
      input_var.a input_var.a env hPc_ops
    have h_pQN := MulMod.interpolatedMulAssert_soundness _ _ _ _ env hQN_ops
    refine ⟨⟨hr_tight, ?_⟩, MulMod.interpolatedMul_requirements _ _ _ _,
      MulMod.interpolatedMulAssert_requirements _ _ _ _ _,
      Or.inl (GroupedEqD.circuitD_channels_req_eq _ _ _ _ _ _ _ _)⟩
    have heqPc_get := MulMod.interpolatedMul_eval_bridge env pcOff
      input_var.a input_var.a hpm h_pPc
    have heqQN_get := MulMod.interpolatedMulAssertZ_map_eval env _ _ _ hpm h_pQN
    set qv := Vector.map (Expression.eval env)
      (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i }) with hqv
    set rv := Vector.map (Expression.eval env)
      (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }) with hrv
    have haU : ∀ i : Fin m, Expression.eval env (input_var.a[i.val]'i.isLt)
        = ((BalancedZ.udigits input.a i.val : ℤ) : F p) := by
      intro i
      rw [eval_udigit env input_var.a i, hmapa]
    have hL : ∀ (k : ℕ) (hk : k < 2 * m - 1),
        Expression.eval env (PcT[k]'hk)
          = ((zlFU input.a k : ℤ) : F p) := by
      intro k hk
      rw [hPcT, heqPc_get ⟨k, hk⟩]
      exact WindowCaps.eval_bigIntMulNoReduce_intCast env _ _ _ _ haU haU ⟨k, hk⟩
    have hsqn_pin : ∀ (k : ℕ) (hk : k < 2 * m - 1),
        Expression.eval env
          ((SquareModBalGT.sqnVecD P.B PcT lowT
            (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))[k]'hk)
          = ((WindowCaps.zconv m m
              (BalancedZ.udigits (Vector.map (Expression.eval env)
                (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i })))
              (BalancedZ.udigits (Vector.map (Expression.eval env) input_var.modulus)) k : ℤ) : F p) := by
      intro k hk
      rw [heqQN_get ⟨k, hk⟩]
      exact WindowCaps.eval_bigIntMulNoReduce_intCast env _ _ _ _
        (fun i => eval_udigit env _ i) (fun i => eval_udigit env input_var.modulus i) ⟨k, hk⟩
    have hR0 := SquareModBalGT.rhsValD_bridge P.hB1 hm2 env input_var.modulus i₀ PcT lowT hsqn_pin
    rw [hmapn, ← hqv, ← hrv] at hR0
    have ha_top : (input.a[m - 1]'(by omega)).val < 2 ^ tb :=
      WindowCaps.top_lt_of_value_lt ha_ltT
    have hn_top : (input.modulus[m - 1]'(by omega)).val < 2 ^ tb :=
      WindowCaps.top_lt_of_value_lt hn_ltT
    have hwin := window_factsU (tb := tb) (tw := tw) P.hB1 hm V VR hNf
      input.a qv input.modulus rv ha_norm ha_top hq_tight.1 hq_tight.2 hn_norm hn_top
      hr_tight.1 hr_tight.2
    have hNfp : ∀ j, j < 2 * m - 1 → V.Nf j + VR.Nf j ≤ p := fun j hj => hgv.2 j hj
    have hspec := h_eq_impl (by
      intro k
      refine ⟨zlFU input.a k.val - zrF P.B qv input.modulus rv k.val, ?_,
        hwin.1 k.val k.isLt, hwin.2 k.val k.isLt⟩
      rw [hL k.val k.isLt, hR0 k.val k.isLt]
      push_cast
      ring)
    have hzsum : (∑ k ∈ Finset.range (2 * m - 1),
        (zlFU input.a k - zrF P.B qv input.modulus rv k) * 2 ^ (P.B * k)) = 0 := by
      rw [← Fin.sum_univ_eq_sum_range (fun k =>
        (zlFU input.a k - zrF P.B qv input.modulus rv k) * 2 ^ (P.B * k))]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hspec
      congr 1
      exact (GroupedEqD.zsval_eq_of_window (by
          rw [hL k.val k.isLt, hR0 k.val k.isLt]
          push_cast
          ring)
        (hwin.1 k.val k.isLt) (hwin.2 k.val k.isLt) (hNfp k.val k.isLt)).symm
    have hsplit := BalancedZ.zsquare_sum_split P.B m hm (BalancedZ.udigits input.a)
      (BalancedZ.udigits qv) (BalancedZ.udigits input.modulus) (BalancedZ.zdigits P.B rv)
    rw [BalancedZ.sum_udigits P.B input.a, BalancedZ.sum_udigits P.B qv,
      BalancedZ.sum_udigits P.B input.modulus, BalancedZ.sum_zdigits P.B hm rv] at hsplit
    have hzero : (BigInt.value P.B input.a : ℤ) * (BigInt.value P.B input.a : ℤ)
        - ((BigInt.value P.B qv : ℤ) * (BigInt.value P.B input.modulus : ℤ) + BalancedZ.VZ P.B rv)
          = 0 := by
      rw [← hsplit]
      simpa only [zlFU, zrF] using hzsum
    exact BalancedZ.modEq_of_identity (Q := (BigInt.value P.B qv : ℤ)) (by linarith)
  completeness := by
    circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
      Normalize.Assumptions, Normalize.Spec,
      NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
      NormalizeTight.Assumptions, NormalizeTight.Spec,
      GroupedEqD.circuitD_assumptions_eq, GroupedEqD.circuitD_spec_eq,
      GroupedEqD.AssumptionsD, GroupedEqD.SpecD]
    obtain ⟨⟨ha_norm, hn_norm, ha_ltT, hn_ltT, hn_pos, hn_ge⟩, ha_lt_n⟩ := h_assumptions
    obtain ⟨hq_env, hr_env, hPc_uses, hsqn_env, -⟩ := h_env
    have hm : 0 < m := Nat.pos_of_neZero m
    have hm2 : 2 ≤ m := by
      have hgvx := hgv.1
      obtain ⟨hpos0, hposS, hgf1, _, _, _, hG3, hlast, _, _⟩ := hgvx
      have hposMono : ∀ a b, a ≤ b → posOf a ≤ posOf b :=
        fun a b hab => monotone_nat_of_le_succ (fun j => by rw [hposS j]; have := hgf1 j; omega) hab
      have h1 : posOf 1 = posOf 0 + gf 0 := hposS 0
      have h2 : posOf 2 = posOf 1 + gf 1 := hposS 1
      have hg0 := hgf1 0
      have hg1 := hgf1 1
      have := hposMono 2 (G - 1) (by omega)
      omega
    have hpm : 2 * m - 1 < p := MulMod.two_m_sub_one_lt P.hp
    have hmapa : Vector.map (Expression.eval env.toEnvironment) input_var.a = input.a :=
      congrArg SquareModLazy.Inputs.a h_input
    have hmapn : Vector.map (Expression.eval env.toEnvironment) input_var.modulus = input.modulus :=
      congrArg SquareModLazy.Inputs.modulus h_input
    set pcOff := i₀ + m + m + ((m - 1) * (P.B - 1) + (tb - 1)) + ((m - 1) * (P.B - 1) + (tw - 1)) with hpcOff
    set PcT := (MulMod.interpolatedMul input_var.a input_var.a pcOff).1 with hPcT
    set lowT := (Vector.mapRange (2 * m - 2) fun i => var (F := F p)
      { index := (pcOff
        + Operations.localLength (MulMod.interpolatedMul input_var.a
            input_var.a pcOff).2 + i) }) with hlowT
    have h_pvPc := MulMod.interpolatedMul_usesLocalWitnesses pcOff pcOff
      input_var.a input_var.a env rfl hPc_uses
    have hsqnwit : ∀ i : Fin (2 * m - 2),
        env.toEnvironment.get (Operations.localLength (MulMod.interpolatedMul input_var.a
            input_var.a pcOff).2 + pcOff + i.val)
          = Expression.eval env.toEnvironment
              ((bigIntMulNoReduce (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i })
                input_var.modulus)[i.val]'(by have := i.isLt; omega)) := by
      intro i
      have h := hsqn_env i
      rwa [Vector.getElem_ofFn] at h
    have heva : SquareModBalGT.evalValue P.B env input_var.a = BigInt.value P.B input.a := by
      rw [SquareModBalGT.evalValue, BigInt.value, ← h_input]
    have hevn : SquareModBalGT.evalValue P.B env input_var.modulus = BigInt.value P.B input.modulus := by
      rw [SquareModBalGT.evalValue, BigInt.value, ← h_input]
    set aval := BigInt.value P.B input.a with haval
    set nval := BigInt.value P.B input.modulus with hnval
    have hqwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + i.val)
        = ((aval * aval / nval / 2 ^ (P.B * i.val) % 2 ^ P.B : ℕ) : F p) := by
      intro i
      rw [hq_env i, Vector.getElem_ofFn, heva, hevn]
    have hrwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + m + i.val)
        = (((aval * aval % nval + BalancedZ.balShift P.B m) / 2 ^ (P.B * i.val) % 2 ^ P.B : ℕ) : F p) := by
      intro i
      rw [hr_env i, Vector.getElem_ofFn, heva, hevn]
    have hqtight := MulMod.qwit_tight_lt (B := P.B) (tb := tb) (tq := tb) P.hB
      (Nat.le_of_succ_le htbB) (le_refl tb) i₀ env.toEnvironment aval aval nval
      ha_ltT ha_lt_n hqwit
    set rval := aval * aval % nval with hrval
    set Nr := rval + BalancedZ.balShift P.B m with hNr
    have hrval_lt : rval < nval := Nat.mod_lt _ hn_pos
    have hrval_ltw : rval < 2 ^ ((m - 1) * P.B + tw - 1) := by
      have h1 : (2 : ℕ) ^ ((m - 1) * P.B + tb) ≤ 2 ^ ((m - 1) * P.B + tw - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      exact lt_of_lt_of_le (lt_trans hrval_lt hn_ltT) h1
    have hNr_lt : Nr < 2 ^ ((m - 1) * P.B + tw) :=
      BalancedZ.add_balShift_lt P.B m tw rval P.hB1 htw.1 hrval_ltw
    have hNr_ltBm : Nr < 2 ^ (P.B * m) := by
      refine lt_of_lt_of_le hNr_lt (Nat.pow_le_pow_right (by norm_num) ?_)
      have h1 : (m - 1) * P.B + P.B = m * P.B := by
        calc (m - 1) * P.B + P.B = ((m - 1) + 1) * P.B := by ring
          _ = m * P.B := by rw [show m - 1 + 1 = m from by omega]
      have h2 : m * P.B = P.B * m := Nat.mul_comm m P.B
      omega
    have hr_norm := MulMod.normalized_mapRange (i₀ + m) Nr env.toEnvironment P.hB
      (fun i => hrwit i)
    have hr_val := BigInt.value_mapRange (i₀ + m) Nr env.toEnvironment P.hB hNr_ltBm
      (fun i => hrwit i)
    have hr_top : ((Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))[m - 1]'(by
          omega)).val < 2 ^ tw := by
      have hget : (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i }))[m - 1]'(by omega)
            = env.toEnvironment.get (i₀ + m + (m - 1)) := by
        simp [circuit_norm]
      rw [hget, hrwit ⟨m - 1, by omega⟩,
        ZMod.val_natCast_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos P.B)) P.hB.le)]
      calc Nr / 2 ^ (P.B * (m - 1)) % 2 ^ P.B ≤ Nr / 2 ^ (P.B * (m - 1)) := Nat.mod_le _ _
        _ < 2 ^ tw := by
            apply Nat.div_lt_of_lt_mul
            rw [show (2 : ℕ) ^ (P.B * (m - 1)) * 2 ^ tw = 2 ^ ((m - 1) * P.B + tw) from by
              rw [← pow_add]; congr 1; ring]
            exact hNr_lt
    have hrtight : BigInt.NormalizedTight P.B tw (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i })) :=
      ⟨hr_norm, hr_top⟩
    have heqPc_get := MulMod.interpolatedMul_eval_bridge_uses env.toEnvironment pcOff
      input_var.a input_var.a h_pvPc
    set qv := Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i }) with hqv
    set rv := Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }) with hrv
    have haU : ∀ i : Fin m, Expression.eval env.toEnvironment (input_var.a[i.val]'i.isLt)
        = ((BalancedZ.udigits input.a i.val : ℤ) : F p) := by
      intro i
      rw [eval_udigit env.toEnvironment input_var.a i, hmapa]
    have hL : ∀ (k : ℕ) (hk : k < 2 * m - 1),
        Expression.eval env.toEnvironment (PcT[k]'hk)
          = ((zlFU input.a k : ℤ) : F p) := by
      intro k hk
      rw [hPcT, heqPc_get ⟨k, hk⟩]
      exact WindowCaps.eval_bigIntMulNoReduce_intCast env.toEnvironment _ _ _ _ haU haU ⟨k, hk⟩
    have hQzU : ∀ k : Fin (2 * m - 1),
        Expression.eval env.toEnvironment
            ((bigIntMulNoReduce (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i })
              input_var.modulus)[k.val])
          = ((WindowCaps.zconv m m
              (BalancedZ.udigits (Vector.map (Expression.eval env.toEnvironment)
                (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i })))
              (BalancedZ.udigits (Vector.map (Expression.eval env.toEnvironment) input_var.modulus))
              k.val : ℤ) : F p) :=
      fun k => WindowCaps.eval_bigIntMulNoReduce_intCast env.toEnvironment _ _ _ _
        (fun i => eval_udigit env.toEnvironment _ i)
        (fun i => eval_udigit env.toEnvironment input_var.modulus i) k
    have ha_top : (input.a[m - 1]'(by omega)).val < 2 ^ tb :=
      WindowCaps.top_lt_of_value_lt ha_ltT
    have hn_top : (input.modulus[m - 1]'(by omega)).val < 2 ^ tb :=
      WindowCaps.top_lt_of_value_lt hn_ltT
    have hwin := window_factsU (tb := tb) (tw := tw) P.hB1 hm V VR hNf
      input.a qv input.modulus rv ha_norm ha_top hqtight.1 hqtight.2 hn_norm hn_top
      hrtight.1 hrtight.2
    have hNfp : ∀ j, j < 2 * m - 1 → V.Nf j + VR.Nf j ≤ p := fun j hj => hgv.2 j hj
    have hqv_val : BigInt.value P.B qv = aval * aval / nval := by
      have hqval_lt : aval * aval / nval < 2 ^ (P.B * m) := by
        have h1 : aval * aval / nval < 2 ^ ((m - 1) * P.B + tb) := by
          rcases Nat.eq_zero_or_pos aval with h0 | h0
          · rw [h0, Nat.zero_mul, Nat.zero_div]
            positivity
          · have h2 : aval * aval < nval * aval := by
              exact Nat.mul_lt_mul_of_lt_of_le ha_lt_n (le_refl aval) h0
            have h3 : aval * aval / nval < aval := Nat.div_lt_of_lt_mul h2
            exact lt_trans h3 ha_ltT
        refine lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) ?_)
        have h4 : (m - 1) * P.B + P.B = m * P.B := by
          calc (m - 1) * P.B + P.B = ((m - 1) + 1) * P.B := by ring
            _ = m * P.B := by rw [show m - 1 + 1 = m from by omega]
        have h5 : m * P.B = P.B * m := Nat.mul_comm m P.B
        have h6 : tb ≤ P.B := Nat.le_of_succ_le htbB
        omega
      exact BigInt.value_mapRange i₀ (aval * aval / nval) env.toEnvironment P.hB hqval_lt
        (fun i => hqwit i)
    have hVZr : BalancedZ.VZ P.B rv = (rval : ℤ) := by
      rw [BalancedZ.VZ, hr_val, hNr]
      push_cast
      ring
    have hidN : (aval * aval / nval) * nval + rval = aval * aval := by
      rw [hrval, Nat.mul_comm]
      exact Nat.div_add_mod _ _
    have hzero : (∑ k ∈ Finset.range (2 * m - 1),
        (zlFU input.a k - zrF P.B qv input.modulus rv k) * 2 ^ (P.B * k)) = 0 := by
      have hsplit := BalancedZ.zsquare_sum_split P.B m hm (BalancedZ.udigits input.a)
        (BalancedZ.udigits qv) (BalancedZ.udigits input.modulus) (BalancedZ.zdigits P.B rv)
      rw [BalancedZ.sum_udigits P.B input.a, BalancedZ.sum_udigits P.B qv,
        BalancedZ.sum_udigits P.B input.modulus, BalancedZ.sum_zdigits P.B hm rv,
        hVZr, hqv_val] at hsplit
      have hcast : ((aval : ℤ) * aval) = ((aval * aval / nval : ℕ) : ℤ) * (nval : ℤ) + (rval : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hidN.symm
      simp only [zlFU, zrF]
      rw [hsplit, ← hnval, ← haval]
      linarith
    have hSlow : ∀ (k : ℕ) (hk : k < 2 * m - 1 - 1),
        Expression.eval env.toEnvironment
            ((SquareModBalGT.rhsSVecD P.B lowT
              (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))[k]'(by omega))
          = ((zrF P.B qv input.modulus rv k : ℤ) : F p) := by
      intro k hk
      rw [SquareModBalGT.rhsSVecD_getElem_low_var P.B lowT i₀ k (by omega)]
      have hswap : (pcOff + Operations.localLength (MulMod.interpolatedMul
            input_var.a input_var.a pcOff).2 + k)
          = (Operations.localLength (MulMod.interpolatedMul
            input_var.a input_var.a pcOff).2 + pcOff + k) := by
        omega
      have hQk : Expression.eval env.toEnvironment (lowT[k]'(by omega))
          = ((WindowCaps.zconv m m
              (BalancedZ.udigits (Vector.map (Expression.eval env.toEnvironment)
                (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i })))
              (BalancedZ.udigits (Vector.map (Expression.eval env.toEnvironment) input_var.modulus))
              k : ℤ) : F p) := by
        have hget : Expression.eval env.toEnvironment (lowT[k]'(by omega))
            = env.toEnvironment.get (Operations.localLength (MulMod.interpolatedMul
                input_var.a input_var.a pcOff).2 + pcOff + k) := by
          rw [hlowT, Vector.getElem_mapRange, hswap]
          rfl
        rw [hget, hsqnwit ⟨k, by omega⟩]
        exact hQzU ⟨k, by omega⟩
      have h1 := SquareModBalGT.eval_rhsS_low P.hB1 hm env.toEnvironment input_var.modulus i₀
        (lowT[k]'(by omega)) k (by omega) hQk
      rw [hmapn, ← hqv, ← hrv] at h1
      exact h1
    have hStop : Expression.eval env.toEnvironment
        (GroupedEqXV.topExprD (L := 2 * m - 1) P.B PcT
          (SquareModBalGT.rhsSVecD P.B lowT (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i })))
        = ((zrF P.B qv input.modulus rv (2 * m - 1 - 1) : ℤ) : F p) :=
      GroupedEqXV.topExprD_eval_of_sum_eq_zero (L := 2 * m - 1) P.B env.toEnvironment
        PcT (SquareModBalGT.rhsSVecD P.B lowT (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))
        (fun k => zlFU input.a k) (fun k => zrF P.B qv input.modulus rv k)
        hL hSlow hzero
    have hsqn_pin_all : ∀ k : Fin (2 * m - 1),
        Expression.eval env.toEnvironment
            ((SquareModBalGT.sqnVecD P.B PcT lowT
              (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))[k.val])
          = Expression.eval env.toEnvironment
              ((bigIntMulNoReduce (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i })
                input_var.modulus)[k.val]) := by
      intro k
      by_cases hklow : k.val < 2 * m - 2
      · rw [SquareModBalGT.sqnVecD_getElem_low P.B PcT lowT _ k.val hklow]
        rw [hlowT, Vector.getElem_mapRange]
        show env.toEnvironment.get _ = _
        rw [show pcOff + Operations.localLength (MulMod.interpolatedMul input_var.a
              input_var.a pcOff).2 + k.val
            = Operations.localLength (MulMod.interpolatedMul input_var.a
              input_var.a pcOff).2 + pcOff + k.val from by omega]
        exact hsqnwit ⟨k.val, hklow⟩
      · have hktop : k.val = 2 * m - 1 - 1 := by have := k.isLt; omega
        have h1 : ∀ (j : ℕ) (hj : j < 2 * m - 1), j = 2 * m - 1 - 1 →
            (SquareModBalGT.sqnVecD P.B PcT lowT
              (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))[j]'hj
              = GroupedEqXV.topExprD (L := 2 * m - 1) P.B PcT
                  (SquareModBalGT.rhsSVecD P.B lowT (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i })) := by
          intro j hj hjeq
          subst hjeq
          exact SquareModBalGT.sqnVecD_getElem_top P.B PcT lowT _
        rw [h1 k.val k.isLt hktop, hStop, hQzU k]
        rw [show BalancedZ.udigits (Vector.map (Expression.eval env.toEnvironment)
              (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i }))
            = BalancedZ.udigits qv from by rw [hqv]]
        rw [show BalancedZ.udigits (Vector.map (Expression.eval env.toEnvironment) input_var.modulus)
            = BalancedZ.udigits input.modulus from by rw [hmapn]]
        unfold zrF
        rw [if_neg (by omega : ¬ (2 * m - 1 - 1 < m)), add_zero, hktop]
    have hsqn_pinC : ∀ (k : ℕ) (hk : k < 2 * m - 1),
        Expression.eval env.toEnvironment
            ((SquareModBalGT.sqnVecD P.B PcT lowT
              (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i }))[k]'hk)
          = ((WindowCaps.zconv m m
              (BalancedZ.udigits (Vector.map (Expression.eval env.toEnvironment)
                (Vector.mapRange m fun i => var (F := F p) { index := i₀ + i })))
              (BalancedZ.udigits (Vector.map (Expression.eval env.toEnvironment) input_var.modulus))
              k : ℤ) : F p) := by
      intro k hk
      rw [hsqn_pin_all ⟨k, hk⟩]
      exact hQzU ⟨k, hk⟩
    have hR0 := SquareModBalGT.rhsValD_bridge P.hB1 hm2 env.toEnvironment input_var.modulus i₀ PcT lowT hsqn_pinC
    rw [hmapn, ← hqv, ← hrv] at hR0
    refine ⟨⟨hqtight, hrtight,
      MulMod.interpolatedMul_completeness _ input_var.a input_var.a env h_pvPc,
      MulMod.interpolatedMulAssert_completeness _ (Vector.mapRange m fun i => var { index := i₀ + i })
        input_var.modulus _ env hsqn_pin_all,
      ?_, ?_⟩, ?_, ?_⟩
    · intro k
      refine ⟨zlFU input.a k.val - zrF P.B qv input.modulus rv k.val, ?_,
        hwin.1 k.val k.isLt, hwin.2 k.val k.isLt⟩
      rw [hL k.val k.isLt, hR0 k.val k.isLt]
      push_cast
      ring
    · refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_)
        (Eq.trans (Fin.sum_univ_eq_sum_range (fun k =>
          (zlFU input.a k - zrF P.B qv input.modulus rv k) * 2 ^ (P.B * k)) (2 * m - 1)) hzero)
      congr 1
      exact GroupedEqD.zsval_eq_of_window (by
          rw [hL k.val k.isLt, hR0 k.val k.isLt]
          push_cast
          ring)
        (hwin.1 k.val k.isLt) (hwin.2 k.val k.isLt) (hNfp k.val k.isLt)
    · rw [hr_val, hNr]
      omega
    · rw [hr_val, hNr]
      omega

end SquareModBalFirstGT

end

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
