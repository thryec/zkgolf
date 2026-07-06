import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Cost
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.GroupedEqXVCost
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.SquareModLazyGT
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.ModExpSqGT
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.ModExpGTheorems
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulModToG
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Bytes32

/-!
# Cost / R1CS certificates for the grouped-equality gadget chain

Mirrors the `Cost.lean` certificates for the `G`-variants (`GroupedEq`,
`MulModLazyG`, `SquareModLazyG`, `ModExpG`, `MulModToG`) and adds the affineness
lemma for the witness-free 4-bytes-per-limb packing `Bytes32.packLimbs4`.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace GadgetCost

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Challenge.CostR1CS
open Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostInfra
open Specs.RSA

variable {m : ℕ}

/-! ## `GroupedEq` -/

/-- Cost of `GroupedEq.main P g input`: range-check the `G−1` affine carries and
assert only the final group equation. -/
theorem costIs_groupedEq (P : BigIntParams circomPrime m) (g : ℕ)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (EqViaCarries.Inputs m) (F circomPrime)) :
    CostIs (GroupedEq.main P g input)
      ⟨(GroupedEq.numGroups m g - 1) * (P.W - 1),
       (GroupedEq.numGroups m g - 1) * P.W + 1⟩ := by
  have hWpos : 1 ≤ P.W := by
    obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
    by_contra h
    have hW0 : W = 0 := Nat.lt_one_iff.mp (Nat.lt_of_not_ge h)
    have hlt : carryOffset (m := m) B * 2 < 1 := by
      simpa [hW0] using hWB
    have hpos : 0 < carryOffset (m := m) B * 2 := by
      unfold carryOffset
      positivity
    omega
  rw [show (⟨(GroupedEq.numGroups m g - 1) * (P.W - 1),
        (GroupedEq.numGroups m g - 1) * P.W + 1⟩ : Count)
        = ⟨(GroupedEq.numGroups m g - 1) * (P.W - 1),
            (GroupedEq.numGroups m g - 1) * P.W⟩ + ⟨0, 1⟩ from by
      congr 1 <;> simp only [Count.add_allocations, Count.add_constraints] <;> ring]
  unfold GroupedEq.main
  refine CostIs.bind (CostIs.forEach fun a n =>
    costIs_assertion_implicitRangeCheck P.W P.hW hWpos a n) fun _ => ?_
  exact CostIs.assertZero _

/-- The group-sum expression is affine when the coefficient expressions are. -/
theorem affine_groupExpr [NeZero m] (B g : ℕ)
    (x : Var (EqViaCarries.Coeffs m) (F circomPrime))
    (hx : AffineW x) (k : ℕ) :
    Affine (GroupedEq.groupExpr B g x k) := by
  unfold GroupedEq.groupExpr
  refine affine_polyEvalExpr _ _ fun i hi => ?_
  rw [Vector.getElem_ofFn]
  split
  · rename_i h
    exact hx _ h
  · exact Affine.zero

/-- The affine carry expression is affine when both grouped sides are affine. -/
theorem affine_carryExpr [NeZero m] (B g OFF : ℕ)
    (lhs rhs : Var (EqViaCarries.Coeffs m) (F circomPrime))
    (hl : AffineW lhs) (hr : AffineW rhs) :
    ∀ k, Affine (GroupedEq.carryExpr B g OFF lhs rhs k)
  | 0 => by
      unfold GroupedEq.carryExpr
      exact Affine.add
        (Affine.fconst_mul _
          (Affine.sub (affine_groupExpr B g lhs hl 0) (affine_groupExpr B g rhs hr 0)))
        (Affine.const _)
  | k + 1 => by
      unfold GroupedEq.carryExpr
      exact Affine.add
        (Affine.fconst_mul _
          (Affine.sub
            (Affine.add (affine_groupExpr B g lhs hl (k + 1))
              (Affine.sub (affine_carryExpr B g OFF lhs rhs hl hr k) (Affine.const _)))
            (affine_groupExpr B g rhs hr (k + 1))))
        (Affine.const _)

/-- Signed carry-in expression is affine. -/
theorem affine_carryInExpr [NeZero m] (B g OFF : ℕ)
    (lhs rhs : Var (EqViaCarries.Coeffs m) (F circomPrime))
    (hl : AffineW lhs) (hr : AffineW rhs) (k : ℕ) :
    Affine (GroupedEq.carryInExpr B g OFF lhs rhs k) := by
  unfold GroupedEq.carryInExpr
  split
  · exact Affine.zero
  · exact Affine.sub (affine_carryExpr B g OFF lhs rhs hl hr (k - 1)) (Affine.const _)

theorem isR1CS_groupedEq (P : BigIntParams circomPrime m) (g : ℕ)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (EqViaCarries.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (GroupedEq.main P g input) := by
  have hWpos : 1 ≤ P.W := by
    obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
    by_contra h
    have hW0 : W = 0 := Nat.lt_one_iff.mp (Nat.lt_of_not_ge h)
    have hlt : carryOffset (m := m) B * 2 < 1 := by
      simpa [hW0] using hWB
    have hpos : 0 < carryOffset (m := m) B * 2 := by
      unfold carryOffset
      positivity
    omega
  unfold GroupedEq.main
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    rw [Vector.getElem_mapFinRange]
    exact isR1CS_assertion_implicitRangeCheck P.W P.hW hWpos _
      (affine_carryExpr P.B g (carryOffset (m := m) P.B) input.lhs input.rhs hl hr i.val) k
  refine IsR1CSCirc.assertZero ?_
  refine isR1CSRow_of_affine ?_
  exact Affine.sub
    (Affine.add (affine_groupExpr P.B g input.lhs hl (GroupedEq.numGroups m g - 1))
      (affine_carryInExpr P.B g (carryOffset (m := m) P.B) input.lhs input.rhs hl hr
        (GroupedEq.numGroups m g - 1)))
    (affine_groupExpr P.B g input.rhs hr (GroupedEq.numGroups m g - 1))

theorem costIs_assertion_groupedEq (P : BigIntParams circomPrime m) (g : ℕ)
    (hgp : GroupedEq.GHyps circomPrime m P.B P.W g) [Fact (circomPrime > 2)]
    [NeZero m] (input : Var (EqViaCarries.Inputs m) (F circomPrime)) :
    CostIs (assertion (GroupedEq.circuit P g hgp) input)
      ⟨(GroupedEq.numGroups m g - 1) * (P.W - 1),
       (GroupedEq.numGroups m g - 1) * P.W + 1⟩ :=
  CostIs.assertion (fun n => costIs_groupedEq P g input n)

theorem isR1CS_assertion_groupedEq (P : BigIntParams circomPrime m) (g : ℕ)
    (hgp : GroupedEq.GHyps circomPrime m P.B P.W g) [Fact (circomPrime > 2)]
    [NeZero m] (input : Var (EqViaCarries.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (GroupedEq.circuit P g hgp) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_groupedEq P g input hl hr n)

/-! ## `MulModLazyG` cost -/

/-- Per-gadget `Count` of one `MulModLazyG` subcircuit: like `mulModLazyCount`
but with the grouped equality (`G−1` affine carry range checks + one final row). -/
def mulModLazyGCount (B W tb g : ℕ) : Count :=
  ⟨m, 0⟩ + (⟨m, 0⟩ + (⟨m * (B - 1), m * B⟩ +
    ((⟨(m - 1) * (B - 1), (m - 1) * B⟩ + ⟨tb - 1, tb⟩) +
    (⟨2 * m - 1, 2 * m - 1⟩ + (⟨2 * m - 1, 2 * m - 1⟩ +
    (⟨(GroupedEq.numGroups m g - 1) * (W - 1),
      (GroupedEq.numGroups m g - 1) * W + 1⟩ + Count.zero))))))

theorem costIs_mulModLazyG (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.B P.W g)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (MulMod.Inputs m) (F circomPrime)) :
    CostIs (MulModLazyG.main P tb htb htbB g hgp input)
      (mulModLazyGCount (m := m) P.B P.W tb g) := by
  unfold MulModLazyG.main mulModLazyGCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalizeTight P tb htb htbB _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pc => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Sqn => ?_
  refine CostIs.bind (costIs_assertion_groupedEq P g hgp _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_mulModLazyG (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.B P.W g)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulMod.Inputs m) (F circomPrime)) :
    CostIs (subcircuit (MulModLazyG.circuit P tb htb htbB g hgp) b)
      (mulModLazyGCount (m := m) P.B P.W tb g) :=
  CostIs.subcircuit (fun n => costIs_mulModLazyG P tb htb htbB g hgp b n)

/-! ## `SquareModLazyG` cost -/

/-! ## `GroupedEqV` (graduated carry widths) -/

/-- Cost of the graduated carry loop: `Σ (Wf k − 1)` witnesses and `Σ Wf k` rows
over the checked boundaries. -/
theorem costIs_carryLoopV (B g : ℕ) (OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < circomPrime)
    [Fact (circomPrime > 2)] [NeZero m]
    (lhs rhs : Var (EqViaCarries.Coeffs m) (F circomPrime)) :
    ∀ (c k₀ : ℕ),
      CostIs (GroupedEqV.carryLoop B g OFFf Wf hWok lhs rhs c k₀)
        ⟨GroupedEqV.widthAllocFrom Wf c k₀, GroupedEqV.widthConsFrom Wf c k₀⟩ := by
  intro c
  induction c with
  | zero =>
    intro k₀
    exact CostIs.pure _
  | succ n ih =>
    intro k₀
    rw [show (⟨GroupedEqV.widthAllocFrom Wf (n + 1) k₀,
          GroupedEqV.widthConsFrom Wf (n + 1) k₀⟩ : Count)
        = (⟨Wf k₀ - 1, Wf k₀⟩
            + ⟨GroupedEqV.widthAllocFrom Wf n (k₀ + 1),
               GroupedEqV.widthConsFrom Wf n (k₀ + 1)⟩ : Count) from by
      congr 1 <;>
        simp only [Count.add_allocations, Count.add_constraints,
          GroupedEqV.widthAllocFrom, GroupedEqV.widthConsFrom]]
    exact CostIs.bind
      (costIs_assertion_implicitRangeCheck (Wf k₀) (hWok k₀).2 (hWok k₀).1 _)
      fun _ => ih (k₀ + 1)

/-- Cost of `GroupedEqV.main`: the graduated carry checks plus one final row. -/
theorem costIs_groupedEqV (B g : ℕ) (V : GroupedEqV.VParams)
    (hgv : GroupedEqV.GVHyps circomPrime m B g V) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (EqViaCarries.Inputs m) (F circomPrime)) :
    CostIs (GroupedEqV.main B g V hgv input)
      ⟨GroupedEqV.widthAllocFrom V.Wf (GroupedEq.numGroups m g - 1) 0,
       GroupedEqV.widthConsFrom V.Wf (GroupedEq.numGroups m g - 1) 0 + 1⟩ := by
  rw [show (⟨GroupedEqV.widthAllocFrom V.Wf (GroupedEq.numGroups m g - 1) 0,
        GroupedEqV.widthConsFrom V.Wf (GroupedEq.numGroups m g - 1) 0 + 1⟩ : Count)
      = (⟨GroupedEqV.widthAllocFrom V.Wf (GroupedEq.numGroups m g - 1) 0,
          GroupedEqV.widthConsFrom V.Wf (GroupedEq.numGroups m g - 1) 0⟩ + ⟨0, 1⟩ : Count) from by
    congr 1 <;> simp only [Count.add_allocations, Count.add_constraints]]
  unfold GroupedEqV.main
  refine CostIs.bind (costIs_carryLoopV B g V.OFFf V.Wf hgv.2.2.2.1 _ _ _ _) fun _ => ?_
  exact CostIs.assertZero _

theorem costIs_assertion_groupedEqV (B g : ℕ) (V : GroupedEqV.VParams)
    (hgv : GroupedEqV.GVHyps circomPrime m B g V) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (EqViaCarries.Inputs m) (F circomPrime)) :
    CostIs (assertion (GroupedEqV.circuit B g V hgv hB1) input)
      ⟨GroupedEqV.widthAllocFrom V.Wf (GroupedEq.numGroups m g - 1) 0,
       GroupedEqV.widthConsFrom V.Wf (GroupedEq.numGroups m g - 1) 0 + 1⟩ :=
  CostIs.assertion (fun n => costIs_groupedEqV B g V hgv hB1 input n)

/-- The graduated carry expression is affine when both grouped sides are affine. -/
theorem affine_carryExprV [NeZero m] (B g : ℕ) (OFFf : ℕ → ℕ)
    (lhs rhs : Var (EqViaCarries.Coeffs m) (F circomPrime))
    (hl : AffineW lhs) (hr : AffineW rhs) :
    ∀ k, Affine (GroupedEqV.carryExpr B g OFFf lhs rhs k)
  | 0 => by
      unfold GroupedEqV.carryExpr
      exact Affine.add
        (Affine.fconst_mul _
          (Affine.sub (affine_groupExpr B g lhs hl 0) (affine_groupExpr B g rhs hr 0)))
        (Affine.const _)
  | k + 1 => by
      unfold GroupedEqV.carryExpr
      exact Affine.add
        (Affine.fconst_mul _
          (Affine.sub
            (Affine.add (affine_groupExpr B g lhs hl (k + 1))
              (Affine.sub (affine_carryExprV B g OFFf lhs rhs hl hr k) (Affine.const _)))
            (affine_groupExpr B g rhs hr (k + 1))))
        (Affine.const _)

/-- Graduated signed carry-in expression is affine. -/
theorem affine_carryInExprV [NeZero m] (B g : ℕ) (OFFf : ℕ → ℕ)
    (lhs rhs : Var (EqViaCarries.Coeffs m) (F circomPrime))
    (hl : AffineW lhs) (hr : AffineW rhs) (k : ℕ) :
    Affine (GroupedEqV.carryInExpr B g OFFf lhs rhs k) := by
  unfold GroupedEqV.carryInExpr
  split
  · exact Affine.zero
  · exact Affine.sub (affine_carryExprV B g OFFf lhs rhs hl hr (k - 1)) (Affine.const _)

theorem isR1CS_carryLoopV (B g : ℕ) (OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < circomPrime)
    [Fact (circomPrime > 2)] [NeZero m]
    (lhs rhs : Var (EqViaCarries.Coeffs m) (F circomPrime))
    (hl : AffineW lhs) (hr : AffineW rhs) :
    ∀ (c k₀ : ℕ),
      IsR1CSCirc (GroupedEqV.carryLoop B g OFFf Wf hWok lhs rhs c k₀) := by
  intro c
  induction c with
  | zero =>
    intro k₀
    exact IsR1CSCirc.pure _
  | succ n ih =>
    intro k₀
    refine IsR1CSCirc.bind
      (isR1CS_assertion_implicitRangeCheck (Wf k₀) (hWok k₀).2 (hWok k₀).1 _
        (affine_carryExprV B g OFFf lhs rhs hl hr k₀))
      fun _ => ih (k₀ + 1)

theorem isR1CS_groupedEqV (B g : ℕ) (V : GroupedEqV.VParams)
    (hgv : GroupedEqV.GVHyps circomPrime m B g V) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (EqViaCarries.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (GroupedEqV.main B g V hgv input) := by
  unfold GroupedEqV.main
  refine IsR1CSCirc.bind (isR1CS_carryLoopV B g V.OFFf V.Wf hgv.2.2.2.1 _ _ hl hr _ _) fun _ => ?_
  refine IsR1CSCirc.assertZero ?_
  refine isR1CSRow_of_affine ?_
  exact Affine.sub
    (Affine.add (affine_groupExpr B g input.lhs hl (GroupedEq.numGroups m g - 1))
      (affine_carryInExprV B g V.OFFf input.lhs input.rhs hl hr (GroupedEq.numGroups m g - 1)))
    (affine_groupExpr B g input.rhs hr (GroupedEq.numGroups m g - 1))

theorem isR1CS_assertion_groupedEqV (B g : ℕ) (V : GroupedEqV.VParams)
    (hgv : GroupedEqV.GVHyps circomPrime m B g V) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (EqViaCarries.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (GroupedEqV.circuit B g V hgv hB1) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_groupedEqV B g V hgv hB1 input hl hr n)

/-- Per-gadget `Count` of one `SquareModLazyG` subcircuit. -/
def squareModLazyGCount (B W tb g : ℕ) (Wf : ℕ → ℕ) : Count :=
  ⟨m, 0⟩ + (⟨m, 0⟩ + ((⟨(m - 1) * (B - 1), (m - 1) * B⟩ + ⟨tb + 1 - 1, tb + 1⟩) +
    ((⟨(m - 1) * (B - 1), (m - 1) * B⟩ + ⟨tb - 1, tb⟩) +
    (⟨2 * m - 1, 2 * m - 1⟩ + (⟨2 * m - 1, 2 * m - 1⟩ +
    (⟨GroupedEqV.widthAllocFrom Wf (GroupedEq.numGroups m g - 1) 0,
      GroupedEqV.widthConsFrom Wf (GroupedEq.numGroups m g - 1) 0 + 1⟩ + Count.zero))))))

theorem costIs_squareModLazyG (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.B P.W g)
    (V : GroupedEqV.VParams) (hgv : GroupedEqV.GVHyps circomPrime m P.B g V)
    (hNf : SquareModLazyG.NfOk (m := m) P.B tb V)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (SquareModLazy.Inputs m) (F circomPrime)) :
    CostIs (SquareModLazyG.main P tb htb htbB g V hgv input)
      (squareModLazyGCount (m := m) P.B P.W tb g V.Wf) := by
  unfold SquareModLazyG.main squareModLazyGCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_normalizeTight P (tb + 1) _ htbB _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalizeTight P tb htb
    (Nat.le_of_succ_le htbB) _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pc => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Sqn => ?_
  refine CostIs.bind (costIs_assertion_groupedEqV P.B g V hgv P.hB1 _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_squareModLazyG (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.B P.W g)
    (V : GroupedEqV.VParams) (hgv : GroupedEqV.GVHyps circomPrime m P.B g V)
    (hNf : SquareModLazyG.NfOk (m := m) P.B tb V)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (SquareModLazy.Inputs m) (F circomPrime)) :
    CostIs (subcircuit (SquareModLazyG.circuit P tb htb htbB g V hgv hNf) b)
      (squareModLazyGCount (m := m) P.B P.W tb g V.Wf) :=
  CostIs.subcircuit (fun n => costIs_squareModLazyG P tb htb htbB g hgp V hgv hNf b n)

theorem squareModLazyGCount_allocations (B W tb g : ℕ) (Wf : ℕ → ℕ) :
    (squareModLazyGCount (m := m) B W tb g Wf).allocations
      = ModExpG.squareModLen (m := m) B W tb g Wf := by
  unfold squareModLazyGCount ModExpG.squareModLen
  simp only [Count.add_allocations, Count.zero]
  ring

theorem mulModLazyGCount_allocations (B W tb g : ℕ) :
    (mulModLazyGCount (m := m) B W tb g).allocations
      = ModExpG.mulModLen (m := m) B W tb g := by
  unfold mulModLazyGCount ModExpG.mulModLen
  simp only [Count.add_allocations, Count.zero]
  ring

/-! ## `ModExpG` cost -/

theorem costIs_modExpLoopG (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.B P.W g)
    (V : GroupedEqV.VParams) (hgv : GroupedEqV.GVHyps circomPrime m P.B g V)
    (hNf : SquareModLazyG.NfOk (m := m) P.B tb V)
    [Fact (circomPrime > 2)] [NeZero m]
    (base n : Var (BigInt m) (F circomPrime)) :
    ∀ (bs : List Bool) (acc : Var (BigInt m) (F circomPrime)),
      CostIs (ModExpG.modExpLoop P tb htb htbB g hgp V hgv hNf base n bs acc)
        ⟨bs.length * (squareModLazyGCount (m := m) P.B P.W tb g V.Wf).allocations
            + bs.count true * (mulModLazyGCount (m := m) P.B P.W tb g).allocations,
         bs.length * (squareModLazyGCount (m := m) P.B P.W tb g V.Wf).constraints
            + bs.count true * (mulModLazyGCount (m := m) P.B P.W tb g).constraints⟩ := by
  intro bs
  induction bs with
  | nil =>
    intro acc
    simp only [ModExpG.modExpLoop, List.length_nil, List.count_nil, Nat.zero_mul, Nat.add_zero]
    exact CostIs.pure _
  | cons bit rest ih =>
    intro acc
    set S := squareModLazyGCount (m := m) P.B P.W tb g V.Wf with hS
    set K := mulModLazyGCount (m := m) P.B P.W tb g with hK
    rw [show ModExpG.modExpLoop P tb htb htbB g hgp V hgv hNf base n (bit :: rest) acc
        = (do
            let sq ← subcircuit (SquareModLazyG.circuit P tb htb htbB g V hgv hNf) { a := acc, modulus := n }
            let acc' ← if bit then subcircuit (MulModLazyG.circuit P tb htb (Nat.le_of_succ_le htbB) g hgp) { a := sq, b := base, modulus := n }
                       else pure sq
            ModExpG.modExpLoop P tb htb htbB g hgp V hgv hNf base n rest acc') from rfl]
    cases bit
    · have hcount : (Count.mk ((rest.length + 1) * S.allocations + rest.count true * K.allocations)
            ((rest.length + 1) * S.constraints + rest.count true * K.constraints))
          = (S + (Count.zero +
              Count.mk (rest.length * S.allocations + rest.count true * K.allocations)
               (rest.length * S.constraints + rest.count true * K.constraints)) : Count) := by
        congr 1 <;> simp only [Count.add_allocations, Count.add_constraints, Count.zero] <;> ring
      simp only [List.length_cons, List.count_cons, Bool.false_eq_true, if_false, Nat.add_zero,
        beq_iff_eq, hcount]
      refine CostIs.bind (costIs_sub_squareModLazyG P tb htb htbB g hgp V hgv hNf _) fun sq => ?_
      exact CostIs.bind (CostIs.pure sq) fun acc' => ih acc'
    · have hcount : (Count.mk ((rest.length + 1) * S.allocations + (rest.count true + 1) * K.allocations)
            ((rest.length + 1) * S.constraints + (rest.count true + 1) * K.constraints))
          = (S + (K +
              Count.mk (rest.length * S.allocations + rest.count true * K.allocations)
               (rest.length * S.constraints + rest.count true * K.constraints)) : Count) := by
        congr 1 <;> simp only [Count.add_allocations, Count.add_constraints] <;> ring
      simp only [List.length_cons, List.count_cons, beq_self_eq_true, if_true, hcount]
      refine CostIs.bind (costIs_sub_squareModLazyG P tb htb htbB g hgp V hgv hNf _) fun sq => ?_
      exact CostIs.bind (costIs_sub_mulModLazyG P tb htb
        (Nat.le_of_succ_le htbB) g hgp _) fun acc' => ih acc'

/-- Total `Count` of `ModExpG.main`. -/
def modExpGCountC (e B W tb g : ℕ) (Wf : ℕ → ℕ) : Count :=
  match ModExpG.eBits e with
  | [] => Count.zero
  | _ :: tail =>
    ⟨tail.length * (squareModLazyGCount (m := m) B W tb g Wf).allocations
        + tail.count true * (mulModLazyGCount (m := m) B W tb g).allocations,
     tail.length * (squareModLazyGCount (m := m) B W tb g Wf).constraints
        + tail.count true * (mulModLazyGCount (m := m) B W tb g).constraints⟩

theorem costIs_modExpG (P : RSAParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.bigIntParams.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.bigIntParams.B P.bigIntParams.W g)
    (V : GroupedEqV.VParams) (hgv : GroupedEqV.GVHyps circomPrime m P.bigIntParams.B g V)
    (hNf : SquareModLazyG.NfOk (m := m) P.bigIntParams.B tb V)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (ModExpG.Inputs m) (F circomPrime)) :
    CostIs (ModExpG.main P tb htb htbB g hgp V hgv hNf input)
      (modExpGCountC (m := m) P.e P.bigIntParams.B P.bigIntParams.W tb g V.Wf) := by
  unfold ModExpG.main modExpGCountC
  cases h : ModExpG.eBits P.e with
  | nil =>
    exact CostIs.pure _
  | cons headBit tail =>
    exact costIs_modExpLoopG P.bigIntParams tb htb htbB g hgp V hgv hNf _ _ tail _

theorem costIs_sub_modExpG (P : RSAParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.bigIntParams.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.bigIntParams.B P.bigIntParams.W g)
    (V : GroupedEqV.VParams) (hgv : GroupedEqV.GVHyps circomPrime m P.bigIntParams.B g V)
    (hNf : SquareModLazyG.NfOk (m := m) P.bigIntParams.B tb V)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (ModExpG.Inputs m) (F circomPrime)) :
    CostIs (subcircuit (ModExpG.circuit P tb htb htbB g hgp V hgv hNf) b)
      (modExpGCountC (m := m) P.e P.bigIntParams.B P.bigIntParams.W tb g V.Wf) :=
  CostIs.subcircuit (fun n => costIs_modExpG P tb htb htbB g hgp V hgv hNf b n)

/-! ## `MulModToG` cost -/

/-- Per-gadget `Count` of the `MulModToG` assertion. -/
def mulModToGCount (B W tq g : ℕ) : Count :=
  ⟨m, 0⟩ + ((⟨(m - 1) * (B - 1), (m - 1) * B⟩ + ⟨tq - 1, tq⟩) +
    (⟨2 * m - 1, 2 * m - 1⟩ + (⟨2 * m - 1, 2 * m - 1⟩ +
    ⟨(GroupedEq.numGroups m g - 1) * (W - 1),
      (GroupedEq.numGroups m g - 1) * W + 1⟩)))

theorem costIs_mulModToG (P : BigIntParams circomPrime m) (tq : ℕ)
    (htq : 1 ≤ tq ∧ (2 : ℕ) ^ tq < circomPrime) (htqB : tq ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.B P.W g)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (MulModTo.InputsTo m) (F circomPrime)) :
    CostIs (MulModToG.main P tq htq htqB g hgp input) (mulModToGCount (m := m) P.B P.W tq g) := by
  unfold MulModToG.main mulModToGCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (costIs_assertion_normalizeTight P tq htq htqB _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pc => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Sqn => ?_
  exact costIs_assertion_groupedEq P g hgp _

theorem costIs_assertion_mulModToG (P : BigIntParams circomPrime m) (tb tq : ℕ)
    (htq : 1 ≤ tq ∧ (2 : ℕ) ^ tq < circomPrime) (htqB : tq ≤ P.B)
    (htb1 : 1 ≤ tb) (htbq : tb ≤ tq)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.B P.W g)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulModTo.InputsTo m) (F circomPrime)) :
    CostIs (assertion (MulModToG.circuit P tb tq htq htqB htb1 htbq g hgp) b)
      (mulModToGCount (m := m) P.B P.W tq g) :=
  CostIs.assertion (fun n => costIs_mulModToG P tq htq htqB g hgp b n)

/-! ## R1CS certificates for the G-chain -/

theorem isR1CS_mulModLazyG (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.B P.W g)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (MulMod.Inputs m) (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hn : AffineW input.modulus) :
    IsR1CSCirc (MulModLazyG.main P tb htb htbB g hgp input) := by
  unfold MulModLazyG.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalizeTight P tb htb htbB _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha hb) fun nPc => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_interpolatedMul _ _ (affineW_provableWitness_bigInt _ nq) hn) fun nSqn => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_groupedEq P g hgp _ ?_ ?_) fun _ => ?_
  · exact affineW_mapRange_var _
  · intro i hi
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add (affineW_interpolatedMul_output _ _ _ i hi)
        (affineW_provableWitness_bigInt _ nr i (by assumption))
    · exact affineW_interpolatedMul_output _ _ _ i hi
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_mulModLazyG (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.B P.W g)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulMod.Inputs m) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus) :
    IsR1CSCirc (subcircuit (MulModLazyG.circuit P tb htb htbB g hgp) b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_mulModLazyG P tb htb htbB g hgp b ha hb hn n)

theorem affineW_sub_mulModLazyG (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.B P.W g)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulMod.Inputs m) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit (MulModLazyG.circuit P tb htb htbB g hgp) b).output n) := by
  have h : (subcircuit (MulModLazyG.circuit P tb htb htbB g hgp) b).output n
      = varFromOffset (BigInt m) (n + m) := by
    simp only [circuit_norm, subcircuit, MulModLazyG.circuit, MulModLazyG.elaborated]
  rw [h]
  exact affineW_varFromOffset _ _

theorem isR1CS_squareModLazyG (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.B P.W g)
    (V : GroupedEqV.VParams) (hgv : GroupedEqV.GVHyps circomPrime m P.B g V)
    (hNf : SquareModLazyG.NfOk (m := m) P.B tb V)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (SquareModLazy.Inputs m) (F circomPrime))
    (ha : AffineW input.a) (hn : AffineW input.modulus) :
    IsR1CSCirc (SquareModLazyG.main P tb htb htbB g V hgv input) := by
  unfold SquareModLazyG.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalizeTight P (tb + 1) _ htbB _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalizeTight P tb htb (Nat.le_of_succ_le htbB) _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha ha) fun nPc => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_interpolatedMul _ _ (affineW_provableWitness_bigInt _ nq) hn) fun nSqn => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_groupedEqV P.B g V hgv P.hB1 _ ?_ ?_) fun _ => ?_
  · exact affineW_mapRange_var _
  · intro i hi
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add (affineW_interpolatedMul_output _ _ _ i hi)
        (affineW_provableWitness_bigInt _ nr i (by assumption))
    · exact affineW_interpolatedMul_output _ _ _ i hi
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_squareModLazyG (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.B P.W g)
    (V : GroupedEqV.VParams) (hgv : GroupedEqV.GVHyps circomPrime m P.B g V)
    (hNf : SquareModLazyG.NfOk (m := m) P.B tb V)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (SquareModLazy.Inputs m) (F circomPrime))
    (ha : AffineW b.a) (hn : AffineW b.modulus) :
    IsR1CSCirc (subcircuit (SquareModLazyG.circuit P tb htb htbB g V hgv hNf) b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_squareModLazyG P tb htb htbB g hgp V hgv hNf b ha hn n)

theorem affineW_sub_squareModLazyG (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.B P.W g)
    (V : GroupedEqV.VParams) (hgv : GroupedEqV.GVHyps circomPrime m P.B g V)
    (hNf : SquareModLazyG.NfOk (m := m) P.B tb V)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (SquareModLazy.Inputs m) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit (SquareModLazyG.circuit P tb htb htbB g V hgv hNf) b).output n) := by
  have h : (subcircuit (SquareModLazyG.circuit P tb htb htbB g V hgv hNf) b).output n
      = varFromOffset (BigInt m) (n + m) := by
    simp only [circuit_norm, subcircuit, SquareModLazyG.circuit, SquareModLazyG.elaborated]
  rw [h]
  exact affineW_varFromOffset _ _

/-! ## `SquareModLazyGT` cost (tight first squaring: quotient top limb `tb`) -/

/-- Per-gadget `Count` of one `SquareModLazyGT` subcircuit: one allocation and
one constraint fewer than `squareModLazyGCount` (the quotient's top limb is
`tb` bits, not `tb+1`). -/
def squareModLazyGTCount (B W tb G : ℕ) (Wf : ℕ → ℕ) : Count :=
  ⟨m, 0⟩ + (⟨m, 0⟩ + ((⟨(m - 1) * (B - 1), (m - 1) * B⟩ + ⟨tb - 1, tb⟩) +
    ((⟨(m - 1) * (B - 1), (m - 1) * B⟩ + ⟨tb - 1, tb⟩) +
    (⟨2 * m - 1, 2 * m - 1⟩ + (⟨2 * m - 1, 2 * m - 1⟩ +
    (⟨GroupedEqXV.widthAllocFrom Wf (G - 2) 0,
      GroupedEqXV.widthConsFrom Wf (G - 2) 0 + 1⟩ + Count.zero))))))

theorem costIs_squareModLazyGT (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.B)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgvx : GroupedEqXV.GVXHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModLazyGT.NfOk2 (m := m) P.B tb V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (SquareModLazy.Inputs m) (F circomPrime)) :
    CostIs (SquareModLazyGT.main P tb htb htbB gf posOf G V VR hgvx input)
      (squareModLazyGTCount (m := m) P.B P.W tb G V.Wf) := by
  unfold SquareModLazyGT.main squareModLazyGTCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_normalizeTight P tb htb
    (Nat.le_of_succ_le htbB) _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalizeTight P tb htb
    (Nat.le_of_succ_le htbB) _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pc => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Sqn => ?_
  refine CostIs.bind (costIs_assertion_groupedEqXV P.B gf posOf G V VR hgvx P.hB1 _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_squareModLazyGT (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.B)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgvx : GroupedEqXV.GVXHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModLazyGT.NfOk2 (m := m) P.B tb V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (SquareModLazy.Inputs m) (F circomPrime)) :
    CostIs (subcircuit (SquareModLazyGT.circuit P tb htb htbB gf posOf G V VR hgvx hNf) b)
      (squareModLazyGTCount (m := m) P.B P.W tb G V.Wf) :=
  CostIs.subcircuit (fun n => costIs_squareModLazyGT P tb htb htbB gf posOf G V VR hgvx hNf b n)

theorem isR1CS_squareModLazyGT (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.B)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgvx : GroupedEqXV.GVXHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModLazyGT.NfOk2 (m := m) P.B tb V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (SquareModLazy.Inputs m) (F circomPrime))
    (ha : AffineW input.a) (hn : AffineW input.modulus) :
    IsR1CSCirc (SquareModLazyGT.main P tb htb htbB gf posOf G V VR hgvx input) := by
  unfold SquareModLazyGT.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalizeTight P tb htb (Nat.le_of_succ_le htbB) _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalizeTight P tb htb (Nat.le_of_succ_le htbB) _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha ha) fun nPc => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_interpolatedMul _ _ (affineW_provableWitness_bigInt _ nq) hn) fun nSqn => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_groupedEqXV P.B gf posOf G V VR hgvx P.hB1 _ ?_ ?_) fun _ => ?_
  · exact affineW_mapRange_var _
  · intro i hi
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add (affineW_interpolatedMul_output _ _ _ i hi)
        (affineW_provableWitness_bigInt _ nr i (by assumption))
    · exact affineW_interpolatedMul_output _ _ _ i hi
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_squareModLazyGT (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.B)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgvx : GroupedEqXV.GVXHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModLazyGT.NfOk2 (m := m) P.B tb V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (SquareModLazy.Inputs m) (F circomPrime))
    (ha : AffineW b.a) (hn : AffineW b.modulus) :
    IsR1CSCirc (subcircuit (SquareModLazyGT.circuit P tb htb htbB gf posOf G V VR hgvx hNf) b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_squareModLazyGT P tb htb htbB gf posOf G V VR hgvx hNf b ha hn n)

theorem affineW_sub_squareModLazyGT (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.B)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgvx : GroupedEqXV.GVXHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModLazyGT.NfOk2 (m := m) P.B tb V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (SquareModLazy.Inputs m) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit (SquareModLazyGT.circuit P tb htb htbB gf posOf G V VR hgvx hNf) b).output n) := by
  have h : (subcircuit (SquareModLazyGT.circuit P tb htb htbB gf posOf G V VR hgvx hNf) b).output n
      = varFromOffset (BigInt m) (n + m) := by
    simp only [circuit_norm, subcircuit, SquareModLazyGT.circuit, SquareModLazyGT.elaborated]
  rw [h]
  exact affineW_varFromOffset _ _

/-! ## `ModExpSqGT` cost / R1CS (square-only tight chain) -/

theorem costIs_sub_squareModLazyGT_general (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.B)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgvx : GroupedEqXV.GVXHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModLazyGT.NfOk2 (m := m) P.B tb V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (SquareModLazy.Inputs m) (F circomPrime)) :
    CostIs (subcircuitWithAssertion
      (SquareModLazyGT.generalCircuit P tb htb htbB gf posOf G V VR hgvx hNf) b)
      (squareModLazyGTCount (m := m) P.B P.W tb G V.Wf) :=
  CostIs.subcircuitWithAssertion
    (fun n => costIs_squareModLazyGT P tb htb htbB gf posOf G V VR hgvx hNf b n)

theorem isR1CS_sub_squareModLazyGT_general (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.B)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgvx : GroupedEqXV.GVXHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModLazyGT.NfOk2 (m := m) P.B tb V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (SquareModLazy.Inputs m) (F circomPrime))
    (ha : AffineW b.a) (hn : AffineW b.modulus) :
    IsR1CSCirc (subcircuitWithAssertion
      (SquareModLazyGT.generalCircuit P tb htb htbB gf posOf G V VR hgvx hNf) b) :=
  IsR1CSCirc.subcircuitWithAssertion
    (fun n => isR1CS_squareModLazyGT P tb htb htbB gf posOf G V VR hgvx hNf b ha hn n)

theorem affineW_sub_squareModLazyGT_general (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.B)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgvx : GroupedEqXV.GVXHyps circomPrime (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModLazyGT.NfOk2 (m := m) P.B tb V VR)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (SquareModLazy.Inputs m) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuitWithAssertion
      (SquareModLazyGT.generalCircuit P tb htb htbB gf posOf G V VR hgvx hNf) b).output n) := by
  have h : (subcircuitWithAssertion
        (SquareModLazyGT.generalCircuit P tb htb htbB gf posOf G V VR hgvx hNf) b).output n
      = varFromOffset (BigInt m) (n + m) := by
    simp only [circuit_norm, subcircuitWithAssertion, SquareModLazyGT.generalCircuit,
      SquareModLazyGT.elaborated]
  rw [h]
  exact affineW_varFromOffset _ _

theorem isR1CS_modExpLoopG (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.B P.W g)
    (V : GroupedEqV.VParams) (hgv : GroupedEqV.GVHyps circomPrime m P.B g V)
    (hNf : SquareModLazyG.NfOk (m := m) P.B tb V)
    [Fact (circomPrime > 2)] [NeZero m]
    (base n : Var (BigInt m) (F circomPrime)) (hbase : AffineW base) (hn : AffineW n) :
    ∀ (bs : List Bool) (acc : Var (BigInt m) (F circomPrime)), AffineW acc →
      IsR1CSCirc (ModExpG.modExpLoop P tb htb htbB g hgp V hgv hNf base n bs acc) := by
  intro bs
  induction bs with
  | nil => intro acc hacc; simp only [ModExpG.modExpLoop]; exact IsR1CSCirc.pure _
  | cons bit rest ih =>
    intro acc hacc
    rw [show ModExpG.modExpLoop P tb htb htbB g hgp V hgv hNf base n (bit :: rest) acc
        = (do
            let sq ← subcircuit (SquareModLazyG.circuit P tb htb htbB g V hgv hNf) { a := acc, modulus := n }
            let acc' ← if bit then subcircuit (MulModLazyG.circuit P tb htb (Nat.le_of_succ_le htbB) g hgp) { a := sq, b := base, modulus := n }
                       else pure sq
            ModExpG.modExpLoop P tb htb htbB g hgp V hgv hNf base n rest acc') from rfl]
    refine IsR1CSCirc.bind_out (isR1CS_sub_squareModLazyG P tb htb htbB g hgp V hgv hNf _ hacc hn) fun nsq => ?_
    have hsq : AffineW ((subcircuit (SquareModLazyG.circuit P tb htb htbB g V hgv hNf) { a := acc, modulus := n }).output nsq) :=
      affineW_sub_squareModLazyG P tb htb htbB g hgp V hgv hNf _ nsq
    cases bit
    · simp only [Bool.false_eq_true, if_false]
      refine IsR1CSCirc.bind_out (IsR1CSCirc.pure _) fun nacc' => ?_
      exact ih _ hsq
    · simp only [if_true]
      refine IsR1CSCirc.bind_out (isR1CS_sub_mulModLazyG P tb htb (Nat.le_of_succ_le htbB) g hgp _ hsq hbase hn) fun nmul => ?_
      exact ih _ (affineW_sub_mulModLazyG P tb htb (Nat.le_of_succ_le htbB) g hgp _ nmul)

theorem isR1CS_modExpG (P : RSAParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.bigIntParams.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.bigIntParams.B P.bigIntParams.W g)
    (V : GroupedEqV.VParams) (hgv : GroupedEqV.GVHyps circomPrime m P.bigIntParams.B g V)
    (hNf : SquareModLazyG.NfOk (m := m) P.bigIntParams.B tb V)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (ModExpG.Inputs m) (F circomPrime))
    (hbase : AffineW input.base) (hn : AffineW input.modulus) :
    IsR1CSCirc (ModExpG.main P tb htb htbB g hgp V hgv hNf input) := by
  unfold ModExpG.main
  cases h : ModExpG.eBits P.e with
  | nil =>
    simp only []
    intro k
    rw [show (Vector.ofFn fun k : Fin m => if k.val = 0 then (1 : Expression (F circomPrime)) else 0)
          = (Vector.ofFn fun k : Fin m => if k.val = 0 then (1 : Expression (F circomPrime)) else 0) from rfl]
    exact (IsR1CSCirc.pure _ : IsR1CSCirc (pure _)) k
  | cons headBit tail =>
    simp only []
    exact isR1CS_modExpLoopG P.bigIntParams tb htb htbB g hgp V hgv hNf _ _ hbase hn tail _ hbase

theorem isR1CS_sub_modExpG (P : RSAParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.bigIntParams.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.bigIntParams.B P.bigIntParams.W g)
    (V : GroupedEqV.VParams) (hgv : GroupedEqV.GVHyps circomPrime m P.bigIntParams.B g V)
    (hNf : SquareModLazyG.NfOk (m := m) P.bigIntParams.B tb V)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (ModExpG.Inputs m) (F circomPrime))
    (hbase : AffineW b.base) (hn : AffineW b.modulus) :
    IsR1CSCirc (subcircuit (ModExpG.circuit P tb htb htbB g hgp V hgv hNf) b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_modExpG P tb htb htbB g hgp V hgv hNf b hbase hn n)

theorem affineW_modExpLoopG_output (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.B P.W g)
    (V : GroupedEqV.VParams) (hgv : GroupedEqV.GVHyps circomPrime m P.B g V)
    (hNf : SquareModLazyG.NfOk (m := m) P.B tb V)
    [Fact (circomPrime > 2)] [NeZero m]
    (base n : Var (BigInt m) (F circomPrime)) (_hbase : AffineW base) (_hn : AffineW n) :
    ∀ (bs : List Bool) (acc : Var (BigInt m) (F circomPrime)) (offset : ℕ), AffineW acc →
      AffineW ((ModExpG.modExpLoop P tb htb htbB g hgp V hgv hNf base n bs acc).output offset) := by
  intro bs
  induction bs with
  | nil => intro acc offset hacc; simpa only [ModExpG.modExpLoop, Circuit.pure_output_eq] using hacc
  | cons bit rest ih =>
    intro acc offset hacc
    rw [show ModExpG.modExpLoop P tb htb htbB g hgp V hgv hNf base n (bit :: rest) acc
        = (do
            let sq ← subcircuit (SquareModLazyG.circuit P tb htb htbB g V hgv hNf) { a := acc, modulus := n }
            let acc' ← if bit then subcircuit (MulModLazyG.circuit P tb htb (Nat.le_of_succ_le htbB) g hgp) { a := sq, b := base, modulus := n }
                       else pure sq
            ModExpG.modExpLoop P tb htb htbB g hgp V hgv hNf base n rest acc') from rfl]
    rw [Circuit.bind_output_eq]
    cases bit
    · simp only [Bool.false_eq_true, if_false, Circuit.bind_output_eq, Circuit.pure_output_eq]
      exact ih _ _ (affineW_sub_squareModLazyG P tb htb htbB g hgp V hgv hNf _ _)
    · simp only [if_true, Circuit.bind_output_eq]
      exact ih _ _ (affineW_sub_mulModLazyG P tb htb (Nat.le_of_succ_le htbB) g hgp _ _)

theorem affineW_sub_modExpG (P : RSAParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 1 ≤ P.bigIntParams.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.bigIntParams.B P.bigIntParams.W g)
    (V : GroupedEqV.VParams) (hgv : GroupedEqV.GVHyps circomPrime m P.bigIntParams.B g V)
    (hNf : SquareModLazyG.NfOk (m := m) P.bigIntParams.B tb V)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (ModExpG.Inputs m) (F circomPrime)) (off : ℕ)
    (hbase : AffineW b.base) (hn : AffineW b.modulus) :
    AffineW ((subcircuit (ModExpG.circuit P tb htb htbB g hgp V hgv hNf) b).output off) := by
  have h : (subcircuit (ModExpG.circuit P tb htb htbB g hgp V hgv hNf) b).output off
      = (ModExpG.main P tb htb htbB g hgp V hgv hNf b).output off := by
    simp only [circuit_norm, subcircuit, ModExpG.circuit]
  rw [h]
  unfold ModExpG.main
  cases hb : ModExpG.eBits P.e with
  | nil =>
    simp only [Circuit.pure_output_eq]
    intro i hi
    rw [Vector.getElem_ofFn]
    split
    · exact Affine.const 1
    · exact Affine.zero
  | cons headBit tail =>
    exact affineW_modExpLoopG_output P.bigIntParams tb htb htbB g hgp V hgv hNf _ _ hbase hn tail _ _ hbase

theorem isR1CS_mulModToG (P : BigIntParams circomPrime m) (tq : ℕ)
    (htq : 1 ≤ tq ∧ (2 : ℕ) ^ tq < circomPrime) (htqB : tq ≤ P.B)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.B P.W g)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (MulModTo.InputsTo m) (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hn : AffineW input.modulus)
    (hem : AffineW input.em) :
    IsR1CSCirc (MulModToG.main P tq htq htqB g hgp input) := by
  unfold MulModToG.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalizeTight P tq htq htqB _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha hb) fun nPc => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_interpolatedMul _ _ (affineW_provableWitness_bigInt _ nq) hn) fun nSqn => ?_
  refine isR1CS_assertion_groupedEq P g hgp _ ?_ ?_
  · exact affineW_mapRange_var _
  · intro i hi
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add (affineW_interpolatedMul_output _ _ _ i hi) (hem i (by assumption))
    · exact affineW_interpolatedMul_output _ _ _ i hi

theorem isR1CS_assertion_mulModToG (P : BigIntParams circomPrime m) (tb tq : ℕ)
    (htq : 1 ≤ tq ∧ (2 : ℕ) ^ tq < circomPrime) (htqB : tq ≤ P.B)
    (htb1 : 1 ≤ tb) (htbq : tb ≤ tq)
    (g : ℕ) (hgp : GroupedEq.GHyps circomPrime m P.B P.W g)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulModTo.InputsTo m) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus) (hem : AffineW b.em) :
    IsR1CSCirc (assertion (MulModToG.circuit P tb tq htq htqB htb1 htbq g hgp) b) :=
  IsR1CSCirc.assertion (fun n => isR1CS_mulModToG P tq htq htqB g hgp b ha hb hn hem n)

/-! ## `Bytes32.packLimbs4` affineness (the packing is witness-free) -/

/-- Every limb of the 4-bytes-per-limb packing is affine when the byte
expressions are. -/
theorem affineW_packLimbs4 (bytes : Vector (Expression (F circomPrime)) 512)
    (hbytes : ∀ j (hj : j < 512), Affine bytes[j]) :
    AffineW (Bytes32.packLimbs4 bytes) := by
  intro k hk
  rw [Bytes32.packLimbs4, Vector.getElem_ofFn]
  split
  · refine Affine.add (Affine.add (Affine.add (hbytes _ (by omega)) ?_) ?_) ?_
    · exact Affine.mul_fconst _ (hbytes _ (by omega))
    · exact Affine.mul_fconst _ (hbytes _ (by omega))
    · exact Affine.mul_fconst _ (hbytes _ (by omega))
  · exact Affine.zero

end GadgetCost
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
