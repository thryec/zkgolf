import Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostG
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.GroupedEqDCost
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.SquareModBalGT
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.SqMulModBalTo

/-!
# Cost / R1CS certificates for the balanced signed-digit residue chain

Certificates for the balanced squaring batteries (`SquareModBalGT`,
`SquareModBalFirstGT`) and the balanced power-of-two squaring chain
(`ModExpSqGT`), mirroring the `SquareModLazyGT`/old-`ModExpSqGT` certificates.
The `GroupedEqD` block has the same width cost as `GroupedEqXV`.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace GadgetCost

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Challenge.CostR1CS
open Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostInfra

variable {m : ℕ}

/-! ## Balanced squaring battery cost -/

/-- Per-gadget `Count` of one balanced squaring battery (middle or first): the
`r`-normalization uses top-limb width `tw` (`tw`-bit balanced top). -/
def squareModBalGTCount (B tb tw G : ℕ) (Wf : ℕ → ℕ) : Count :=
  ⟨m, 0⟩ + (⟨m, 0⟩ + ((⟨(m - 1) * (B - 1), (m - 1) * B⟩ + ⟨tb - 1, tb⟩) +
    ((⟨(m - 1) * (B - 1), (m - 1) * B⟩ + ⟨tw - 1, tw⟩) +
    (⟨2 * m - 1, 2 * m - 1⟩ + (⟨2 * m - 2, 0⟩ + (⟨0, 2 * m - 1⟩ +
    (⟨GroupedEqXV.widthAllocFrom Wf (G - 2) 0,
      GroupedEqXV.widthConsFrom Wf (G - 2) 0⟩ + Count.zero)))))))

/-- The definitional-top rhs vector is affine coordinatewise. -/
theorem affineW_rhsSVecD [NeZero m] (B : ℕ)
    (sqnLow : Vector (Expression (F circomPrime)) (2 * m - 2))
    (r : Var (BigInt m) (F circomPrime))
    (hlow : AffineW sqnLow) (hr : AffineW r) :
    AffineW (SquareModBalGT.rhsSVecD B sqnLow r) := by
  intro i hi
  unfold SquareModBalGT.rhsSVecD
  rw [Vector.getElem_mapFinRange]
  split
  · split
    · split
      · exact Affine.add (hlow i (by assumption)) (hr i (by assumption))
      · exact Affine.sub (Affine.add (hlow i (by assumption)) (hr i (by assumption)))
          (Affine.const _)
    · exact hlow i (by assumption)
  · exact (Affine.zero : Affine (0 : Expression (F circomPrime)))

/-- The spliced `q·n` coefficient vector is affine coordinatewise (the top is
the affine reconstruction `topExprD`). -/
theorem affineW_sqnVecD [NeZero m] (B : ℕ)
    (Pc : Vector (Expression (F circomPrime)) (2 * m - 1))
    (sqnLow : Vector (Expression (F circomPrime)) (2 * m - 2))
    (r : Var (BigInt m) (F circomPrime))
    (hPc : AffineW Pc) (hlow : AffineW sqnLow) (hr : AffineW r) :
    AffineW (SquareModBalGT.sqnVecD B Pc sqnLow r) := by
  intro i hi
  unfold SquareModBalGT.sqnVecD
  rw [Vector.getElem_mapFinRange]
  split
  · exact hlow i (by assumption)
  · exact affine_topExprD B Pc (SquareModBalGT.rhsSVecD B sqnLow r) hPc
      (affineW_rhsSVecD B sqnLow r hlow hr)

theorem costIs_squareModBalGT (P : BigIntParams circomPrime m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htw : 1 ≤ tw ∧ (2 : ℕ) ^ tw < circomPrime)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (SquareModLazy.Inputs m) (F circomPrime)) :
    CostIs (SquareModBalGT.main P tb tw htb htw htbB htwB gf posOf G V VR hgv input)
      (squareModBalGTCount (m := m) P.B tb tw G V.Wf) := by
  unfold SquareModBalGT.main squareModBalGTCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_normalizeTight P tb htb (Nat.le_of_succ_le htbB) _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalizeTight P tw htw htwB _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pc => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun sqnLow => ?_
  refine CostIs.bind (costIs_interpolatedMulAssert _ _ _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_groupedEqDD P.B gf posOf G V VR hgv P.hB1 _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_squareModBalGT (P : BigIntParams circomPrime m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htw : 1 ≤ tw ∧ (2 : ℕ) ^ tw < circomPrime)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (SquareModLazy.Inputs m) (F circomPrime)) :
    CostIs (subcircuitWithAssertion
      (SquareModBalGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf) b)
      (squareModBalGTCount (m := m) P.B tb tw G V.Wf) :=
  CostIs.subcircuitWithAssertion
    (fun n => costIs_squareModBalGT P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf b n)

theorem isR1CS_squareModBalGT (P : BigIntParams circomPrime m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htw : 1 ≤ tw ∧ (2 : ℕ) ^ tw < circomPrime)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (SquareModLazy.Inputs m) (F circomPrime))
    (ha : AffineW input.a) (hn : AffineW input.modulus) :
    IsR1CSCirc (SquareModBalGT.main P tb tw htb htw htbB htwB gf posOf G V VR hgv input) := by
  unfold SquareModBalGT.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalizeTight P tb htb (Nat.le_of_succ_le htbB) _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalizeTight P tw htw htwB _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  have haS := affineW_shiftedA P.B input.a ha
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ haS haS) fun nPc => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nlow => ?_
  refine IsR1CSCirc.bind (isR1CS_interpolatedMulAssert _ _ _
    (affineW_provableWitness_bigInt _ nq) hn
    (affineW_sqnVecD P.B _ _ _ (affineW_mapRange_var _)
      (affineW_provableWitness_bigInt _ nlow)
      (affineW_provableWitness_bigInt _ nr))) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_groupedEqDD P.B gf posOf G V VR hgv P.hB1 _ ?_ ?_) fun _ => ?_
  · exact affineW_mapRange_var _
  · exact affineW_rhsSVecD P.B _ _ (affineW_provableWitness_bigInt _ nlow)
      (affineW_provableWitness_bigInt _ nr)
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_squareModBalGT (P : BigIntParams circomPrime m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htw : 1 ≤ tw ∧ (2 : ℕ) ^ tw < circomPrime)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (SquareModLazy.Inputs m) (F circomPrime))
    (ha : AffineW b.a) (hn : AffineW b.modulus) :
    IsR1CSCirc (subcircuitWithAssertion
      (SquareModBalGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf) b) :=
  IsR1CSCirc.subcircuitWithAssertion
    (fun n => isR1CS_squareModBalGT P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf b ha hn n)

theorem affineW_sub_squareModBalGT (P : BigIntParams circomPrime m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htw : 1 ≤ tw ∧ (2 : ℕ) ^ tw < circomPrime)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (SquareModLazy.Inputs m) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuitWithAssertion
      (SquareModBalGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf) b).output n) := by
  have h : (subcircuitWithAssertion
        (SquareModBalGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf) b).output n
      = varFromOffset (BigInt m) (n + m) := by
    simp only [circuit_norm, subcircuitWithAssertion, SquareModBalGT.generalCircuit,
      SquareModBalGT.elaborated]
  rw [h]
  exact affineW_varFromOffset _ _

/-! ## Balanced first squaring battery cost (unsigned input) -/

theorem costIs_squareModBalFirstGT (P : BigIntParams circomPrime m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htw : 1 ≤ tw ∧ (2 : ℕ) ^ tw < circomPrime)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalFirstGT.NfOkF (m := m) P.B tb tw V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (SquareModLazy.Inputs m) (F circomPrime)) :
    CostIs (SquareModBalFirstGT.main P tb tw htb htw htbB htwB gf posOf G V VR hgv input)
      (squareModBalGTCount (m := m) P.B tb tw G V.Wf) := by
  unfold SquareModBalFirstGT.main squareModBalGTCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_normalizeTight P tb htb (Nat.le_of_succ_le htbB) _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalizeTight P tw htw htwB _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pc => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun sqnLow => ?_
  refine CostIs.bind (costIs_interpolatedMulAssert _ _ _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_groupedEqDD P.B gf posOf G V VR hgv P.hB1 _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_squareModBalFirstGT (P : BigIntParams circomPrime m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htw : 1 ≤ tw ∧ (2 : ℕ) ^ tw < circomPrime)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalFirstGT.NfOkF (m := m) P.B tb tw V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (SquareModLazy.Inputs m) (F circomPrime)) :
    CostIs (subcircuitWithAssertion
      (SquareModBalFirstGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf) b)
      (squareModBalGTCount (m := m) P.B tb tw G V.Wf) :=
  CostIs.subcircuitWithAssertion
    (fun n => costIs_squareModBalFirstGT P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf b n)

theorem isR1CS_squareModBalFirstGT (P : BigIntParams circomPrime m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htw : 1 ≤ tw ∧ (2 : ℕ) ^ tw < circomPrime)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalFirstGT.NfOkF (m := m) P.B tb tw V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (SquareModLazy.Inputs m) (F circomPrime))
    (ha : AffineW input.a) (hn : AffineW input.modulus) :
    IsR1CSCirc (SquareModBalFirstGT.main P tb tw htb htw htbB htwB gf posOf G V VR hgv input) := by
  unfold SquareModBalFirstGT.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalizeTight P tb htb (Nat.le_of_succ_le htbB) _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalizeTight P tw htw htwB _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha ha) fun nPc => ?_
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nlow => ?_
  refine IsR1CSCirc.bind (isR1CS_interpolatedMulAssert _ _ _
    (affineW_provableWitness_bigInt _ nq) hn
    (affineW_sqnVecD P.B _ _ _ (affineW_mapRange_var _)
      (affineW_provableWitness_bigInt _ nlow)
      (affineW_provableWitness_bigInt _ nr))) fun _ => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_groupedEqDD P.B gf posOf G V VR hgv P.hB1 _ ?_ ?_) fun _ => ?_
  · exact affineW_mapRange_var _
  · exact affineW_rhsSVecD P.B _ _ (affineW_provableWitness_bigInt _ nlow)
      (affineW_provableWitness_bigInt _ nr)
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_squareModBalFirstGT (P : BigIntParams circomPrime m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htw : 1 ≤ tw ∧ (2 : ℕ) ^ tw < circomPrime)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalFirstGT.NfOkF (m := m) P.B tb tw V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (SquareModLazy.Inputs m) (F circomPrime))
    (ha : AffineW b.a) (hn : AffineW b.modulus) :
    IsR1CSCirc (subcircuitWithAssertion
      (SquareModBalFirstGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf) b) :=
  IsR1CSCirc.subcircuitWithAssertion
    (fun n => isR1CS_squareModBalFirstGT P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf b ha hn n)

theorem affineW_sub_squareModBalFirstGT (P : BigIntParams circomPrime m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htw : 1 ≤ tw ∧ (2 : ℕ) ^ tw < circomPrime)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalFirstGT.NfOkF (m := m) P.B tb tw V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (SquareModLazy.Inputs m) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuitWithAssertion
      (SquareModBalFirstGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf) b).output n) := by
  have h : (subcircuitWithAssertion
        (SquareModBalFirstGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf) b).output n
      = varFromOffset (BigInt m) (n + m) := by
    simp only [circuit_norm, subcircuitWithAssertion, SquareModBalFirstGT.generalCircuit,
      SquareModBalFirstGT.elaborated]
  rw [h]
  exact affineW_varFromOffset _ _

/-! ## Balanced squaring chain (`ModExpSqGT`) cost -/

def modExpSqBalCountC (k B tb tw G : ℕ) (Wf : ℕ → ℕ) : Count :=
  ⟨k * (squareModBalGTCount (m := m) B tb tw G Wf).allocations,
   k * (squareModBalGTCount (m := m) B tb tw G Wf).constraints⟩

theorem costIs_squareChainBal (P : BigIntParams circomPrime m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htw : 1 ≤ tw ∧ (2 : ℕ) ^ tw < circomPrime)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (n : Var (BigInt m) (F circomPrime)) :
    ∀ (k : ℕ) (acc : Var (BigInt m) (F circomPrime)),
      CostIs (ModExpSqGT.squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k acc)
        (modExpSqBalCountC (m := m) k P.B tb tw G V.Wf) := by
  intro k
  induction k with
  | zero =>
    intro acc
    simp only [ModExpSqGT.squareChain, modExpSqBalCountC, Nat.zero_mul]
    exact CostIs.pure _
  | succ k ih =>
    intro acc
    set S := squareModBalGTCount (m := m) P.B tb tw G V.Wf with hS
    rw [show ModExpSqGT.squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n (k + 1) acc
        = (do
            let sq ← subcircuitWithAssertion
              (SquareModBalGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf)
              { a := acc, modulus := n }
            ModExpSqGT.squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k sq) from rfl]
    have hcount : (modExpSqBalCountC (m := m) (k + 1) P.B tb tw G V.Wf)
        = (S + modExpSqBalCountC (m := m) k P.B tb tw G V.Wf : Count) := by
      subst S
      unfold modExpSqBalCountC
      congr 1 <;> simp only [Count.add_allocations, Count.add_constraints] <;> ring
    rw [hcount]
    refine CostIs.bind
      (costIs_sub_squareModBalGT P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf _) fun sq => ?_
    exact ih sq

theorem costIs_modExpSqGT (P : BigIntParams circomPrime m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htw : 1 ≤ tw ∧ (2 : ℕ) ^ tw < circomPrime)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (k : ℕ) (input : Var (ModExpG.Inputs m) (F circomPrime)) :
    CostIs (ModExpSqGT.main P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf k input)
      (modExpSqBalCountC (m := m) k P.B tb tw G V.Wf) := by
  unfold ModExpSqGT.main
  exact costIs_squareChainBal P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf input.modulus k input.base

theorem costIs_sub_modExpSqGT (P : BigIntParams circomPrime m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htw : 1 ≤ tw ∧ (2 : ℕ) ^ tw < circomPrime)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (k : ℕ) (b : Var (ModExpG.Inputs m) (F circomPrime)) :
    CostIs (subcircuitWithAssertion (ModExpSqGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf k) b)
      (modExpSqBalCountC (m := m) k P.B tb tw G V.Wf) :=
  CostIs.subcircuitWithAssertion
    (fun n => costIs_modExpSqGT P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf k b n)

theorem isR1CS_squareChainBal (P : BigIntParams circomPrime m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htw : 1 ≤ tw ∧ (2 : ℕ) ^ tw < circomPrime)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (n : Var (BigInt m) (F circomPrime)) (hn : AffineW n) :
    ∀ (k : ℕ) (acc : Var (BigInt m) (F circomPrime)), AffineW acc →
      IsR1CSCirc (ModExpSqGT.squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k acc) := by
  intro k
  induction k with
  | zero => intro acc hacc; simp only [ModExpSqGT.squareChain]; exact IsR1CSCirc.pure _
  | succ k ih =>
    intro acc hacc
    rw [show ModExpSqGT.squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n (k + 1) acc
        = (do
            let sq ← subcircuitWithAssertion
              (SquareModBalGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf)
              { a := acc, modulus := n }
            ModExpSqGT.squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k sq) from rfl]
    refine IsR1CSCirc.bind_out
      (isR1CS_sub_squareModBalGT P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf _ hacc hn) fun nsq => ?_
    exact ih _ (affineW_sub_squareModBalGT P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf _ nsq)

theorem isR1CS_modExpSqGT (P : BigIntParams circomPrime m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htw : 1 ≤ tw ∧ (2 : ℕ) ^ tw < circomPrime)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (k : ℕ) (input : Var (ModExpG.Inputs m) (F circomPrime))
    (hbase : AffineW input.base) (hn : AffineW input.modulus) :
    IsR1CSCirc (ModExpSqGT.main P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf k input) := by
  unfold ModExpSqGT.main
  exact isR1CS_squareChainBal P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf input.modulus hn k input.base hbase

theorem isR1CS_sub_modExpSqGT (P : BigIntParams circomPrime m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htw : 1 ≤ tw ∧ (2 : ℕ) ^ tw < circomPrime)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (k : ℕ) (b : Var (ModExpG.Inputs m) (F circomPrime))
    (hbase : AffineW b.base) (hn : AffineW b.modulus) :
    IsR1CSCirc (subcircuitWithAssertion
      (ModExpSqGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf k) b) :=
  IsR1CSCirc.subcircuitWithAssertion
    (fun n => isR1CS_modExpSqGT P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf k b hbase hn n)

theorem affineW_squareChainBal_output (P : BigIntParams circomPrime m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htw : 1 ≤ tw ∧ (2 : ℕ) ^ tw < circomPrime)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (n : Var (BigInt m) (F circomPrime)) :
    ∀ (k : ℕ) (acc : Var (BigInt m) (F circomPrime)) (offset : ℕ), AffineW acc →
      AffineW ((ModExpSqGT.squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k acc).output offset) := by
  intro k
  induction k with
  | zero =>
    intro acc offset hacc
    simpa only [ModExpSqGT.squareChain, Circuit.pure_output_eq] using hacc
  | succ k ih =>
    intro acc offset hacc
    rw [show ModExpSqGT.squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n (k + 1) acc
        = (do
            let sq ← subcircuitWithAssertion
              (SquareModBalGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf)
              { a := acc, modulus := n }
            ModExpSqGT.squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k sq) from rfl]
    rw [Circuit.bind_output_eq]
    exact ih _ _ (affineW_sub_squareModBalGT P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf _ _)

theorem affineW_sub_modExpSqGT (P : BigIntParams circomPrime m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htw : 1 ≤ tw ∧ (2 : ℕ) ^ tw < circomPrime)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (k : ℕ) (b : Var (ModExpG.Inputs m) (F circomPrime)) (off : ℕ)
    (hbase : AffineW b.base) :
    AffineW ((subcircuitWithAssertion
      (ModExpSqGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf k) b).output off) := by
  have h : (subcircuitWithAssertion
        (ModExpSqGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf k) b).output off
      = (ModExpSqGT.main P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf k b).output off := by
    simp only [circuit_norm, subcircuitWithAssertion, ModExpSqGT.generalCircuit]
  rw [h]
  unfold ModExpSqGT.main
  exact affineW_squareChainBal_output P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf b.modulus k b.base off hbase

end GadgetCost
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
