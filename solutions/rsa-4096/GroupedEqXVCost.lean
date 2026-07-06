import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Cost
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.GroupedEqXV
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.WindowCaps

/-!
# Cost / R1CS certificates for the graduated fused equality `GroupedEqXV`

Mirrors the `GroupedEqV` cost certificates in `CostG.lean` for the length-generic
`GroupedEqXV` gadget: the graduated carry loop costs `Σ(Wf−1)` witnesses and
`ΣWf` rows, plus one final asserted equation row; single-row R1CS via the affine
carry expressions.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace GadgetCost

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Challenge.CostR1CS
open Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostInfra

variable {L : ℕ}


/-- Cost of the graduated carry loop: `Σ (Wf k − 1)` witnesses and `Σ Wf k` rows
over the checked boundaries. -/
theorem costIs_carryLoopXV (B : ℕ) (gf posOf OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < circomPrime)
    [Fact (circomPrime > 2)] [NeZero L]
    (lhs rhs : Var (GroupedEqX.CoeffsX L) (F circomPrime)) :
    ∀ (c k₀ : ℕ),
      CostIs (GroupedEqXV.carryLoop B gf posOf OFFf Wf hWok lhs rhs c k₀)
        ⟨GroupedEqXV.widthAllocFrom Wf c k₀, GroupedEqXV.widthConsFrom Wf c k₀⟩ := by
  intro c
  induction c with
  | zero =>
    intro k₀
    exact CostIs.pure _
  | succ n ih =>
    intro k₀
    rw [show (⟨GroupedEqXV.widthAllocFrom Wf (n + 1) k₀,
          GroupedEqXV.widthConsFrom Wf (n + 1) k₀⟩ : Count)
        = (⟨Wf k₀ - 1, Wf k₀⟩
            + ⟨GroupedEqXV.widthAllocFrom Wf n (k₀ + 1),
               GroupedEqXV.widthConsFrom Wf n (k₀ + 1)⟩ : Count) from by
      congr 1 <;>
        simp only [Count.add_allocations, Count.add_constraints,
          GroupedEqXV.widthAllocFrom, GroupedEqXV.widthConsFrom]]
    exact CostIs.bind
      (costIs_assertion_implicitRangeCheck (Wf k₀) (hWok k₀).2 (hWok k₀).1 _)
      fun _ => ih (k₀ + 1)

/-- Cost of `GroupedEqXV.main`: the graduated carry checks plus one final row. -/
theorem costIs_groupedEqXV (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime)) :
    CostIs (GroupedEqXV.main B gf posOf G V VR hgv input)
      ⟨GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0,
       GroupedEqXV.widthConsFrom V.Wf (G - 2) 0 + 1⟩ := by
  rw [show (⟨GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0,
        GroupedEqXV.widthConsFrom V.Wf (G - 2) 0 + 1⟩ : Count)
      = (⟨GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0,
          GroupedEqXV.widthConsFrom V.Wf (G - 2) 0⟩ + ⟨0, 1⟩ : Count) from by
    congr 1 <;> simp only [Count.add_allocations, Count.add_constraints]]
  unfold GroupedEqXV.main
  refine CostIs.bind (costIs_carryLoopXV B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _ _ _) fun _ => ?_
  exact CostIs.assertZero _

theorem costIs_assertion_groupedEqXV (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime)) :
    CostIs (assertion (GroupedEqXV.circuit B gf posOf G V VR hgv hB1) input)
      ⟨GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0,
       GroupedEqXV.widthConsFrom V.Wf (G - 2) 0 + 1⟩ :=
  CostIs.assertion (fun n => costIs_groupedEqXV B gf posOf G V VR hgv hB1 input n)

/-- The graduated carry expression is affine when both grouped sides are affine. -/
theorem affine_carryExprXV [NeZero L] (B : ℕ) (gf posOf OFFf : ℕ → ℕ)
    (lhs rhs : Var (GroupedEqX.CoeffsX L) (F circomPrime))
    (hl : AffineW lhs) (hr : AffineW rhs) :
    ∀ k, Affine (GroupedEqXV.carryExpr B gf posOf OFFf lhs rhs k)
  | 0 => by
      unfold GroupedEqXV.carryExpr
      exact Affine.add
        (Affine.fconst_mul _
          (Affine.sub (affine_groupExprW B L gf posOf lhs hl 0) (affine_groupExprW B L gf posOf rhs hr 0)))
        (Affine.const _)
  | k + 1 => by
      unfold GroupedEqXV.carryExpr
      exact Affine.add
        (Affine.fconst_mul _
          (Affine.sub
            (Affine.add (affine_groupExprW B L gf posOf lhs hl (k + 1))
              (Affine.sub (affine_carryExprXV B gf posOf OFFf lhs rhs hl hr k) (Affine.const _)))
            (affine_groupExprW B L gf posOf rhs hr (k + 1))))
        (Affine.const _)

/-- Graduated signed carry-in expression is affine. -/
theorem affine_carryInExprXV [NeZero L] (B : ℕ) (gf posOf OFFf : ℕ → ℕ)
    (lhs rhs : Var (GroupedEqX.CoeffsX L) (F circomPrime))
    (hl : AffineW lhs) (hr : AffineW rhs) (k : ℕ) :
    Affine (GroupedEqXV.carryInExpr B gf posOf OFFf lhs rhs k) := by
  unfold GroupedEqXV.carryInExpr
  split
  · exact Affine.zero
  · exact Affine.sub (affine_carryExprXV B gf posOf OFFf lhs rhs hl hr (k - 1)) (Affine.const _)

theorem isR1CS_carryLoopXV (B : ℕ) (gf posOf OFFf Wf : ℕ → ℕ)
    (hWok : ∀ k, 1 ≤ Wf k ∧ 2 ^ Wf k < circomPrime)
    [Fact (circomPrime > 2)] [NeZero L]
    (lhs rhs : Var (GroupedEqX.CoeffsX L) (F circomPrime))
    (hl : AffineW lhs) (hr : AffineW rhs) :
    ∀ (c k₀ : ℕ),
      IsR1CSCirc (GroupedEqXV.carryLoop B gf posOf OFFf Wf hWok lhs rhs c k₀) := by
  intro c
  induction c with
  | zero =>
    intro k₀
    exact IsR1CSCirc.pure _
  | succ n ih =>
    intro k₀
    refine IsR1CSCirc.bind
      (isR1CS_assertion_implicitRangeCheck (Wf k₀) (hWok k₀).2 (hWok k₀).1 _
        (affine_carryExprXV B gf posOf OFFf lhs rhs hl hr k₀))
      fun _ => ih (k₀ + 1)

theorem isR1CS_groupedEqXV (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (GroupedEqXV.main B gf posOf G V VR hgv input) := by
  unfold GroupedEqXV.main
  refine IsR1CSCirc.bind (isR1CS_carryLoopXV B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _ hl hr _ _) fun _ => ?_
  refine IsR1CSCirc.assertZero ?_
  refine isR1CSRow_of_affine ?_
  refine affine_polyEvalExpr _ _ fun i hi => ?_
  rw [Vector.getElem_ofFn]
  exact Affine.sub (hl i hi) (hr i hi)

theorem isR1CS_assertion_groupedEqXV (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (GroupedEqXV.circuit B gf posOf G V VR hgv hB1) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_groupedEqXV B gf posOf G V VR hgv hB1 input hl hr n)


/-! ## Definitional-top variant certificates -/

/-- Cost of `GroupedEqXV.mainD`: the graduated carry checks only — no final row. -/
theorem costIs_groupedEqXVD (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime)) :
    CostIs (GroupedEqXV.mainD B gf posOf G V VR hgv input)
      ⟨GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0,
       GroupedEqXV.widthConsFrom V.Wf (G - 2) 0⟩ := by
  unfold GroupedEqXV.mainD
  exact costIs_carryLoopXV B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _ _ _

theorem costIs_assertion_groupedEqXVD (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime)) :
    CostIs (assertion (GroupedEqXV.circuitD B gf posOf G V VR hgv hB1) input)
      ⟨GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0,
       GroupedEqXV.widthConsFrom V.Wf (G - 2) 0⟩ :=
  CostIs.assertion (fun n => costIs_groupedEqXVD B gf posOf G V VR hgv hB1 input n)

/-- The reconstructed top coefficient is affine. -/
theorem affine_topExprD [NeZero L] (B : ℕ)
    (lhs rhs : Var (GroupedEqX.CoeffsX L) (F circomPrime))
    (hl : AffineW lhs) (hr : AffineW rhs) :
    Affine (GroupedEqXV.topExprD B lhs rhs) := by
  unfold GroupedEqXV.topExprD
  exact Affine.fconst_mul _
    (Affine.sub (affine_polyEvalExpr _ _ fun i hi => hl i hi)
      (affine_polyEvalExpr _ _ fun i hi => by
        have hgl : (GroupedEqXV.lowVec rhs)[i]'hi = rhs[i]'(by omega) := by
          unfold GroupedEqXV.lowVec
          rw [Vector.getElem_mapFinRange]
        rw [hgl]
        exact hr i (by omega)))

/-- The reconstructed rhs vector is affine coordinatewise. -/
theorem affineW_rhsD [NeZero L] (B : ℕ)
    (lhs rhs : Var (GroupedEqX.CoeffsX L) (F circomPrime))
    (hl : AffineW lhs) (hr : AffineW rhs) :
    AffineW (GroupedEqXV.rhsD B lhs rhs) := by
  intro i hi
  by_cases h : i < L - 1
  · rw [GroupedEqXV.rhsD_getElem_low B lhs rhs i h]
    exact hr i (by omega)
  · have hieq : i = L - 1 := by omega
    subst hieq
    rw [GroupedEqXV.rhsD_getElem_top B lhs rhs]
    exact affine_topExprD B lhs rhs hl hr

theorem isR1CS_groupedEqXVD (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (GroupedEqXV.mainD B gf posOf G V VR hgv input) := by
  unfold GroupedEqXV.mainD
  exact isR1CS_carryLoopXV B gf posOf VR.OFFf V.Wf hgv.2.2.2.1 _ _
    hl (affineW_rhsD B input.lhs input.rhs hl hr) _ _

theorem isR1CS_assertion_groupedEqXVD (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqXV.GVXHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (GroupedEqXV.circuitD B gf posOf G V VR hgv hB1) input) :=
  IsR1CSCirc.assertion
    (fun n => isR1CS_groupedEqXVD B gf posOf G V VR hgv hB1 input hl hr n)

end GadgetCost
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
