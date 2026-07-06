import Solution.RSASSAPKCS1v15_SHA256_4096_65537.GroupedEqXVCost
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.GroupedEqD

/-!
# Cost / R1CS certificates for the two-sided-window grouped equality `GroupedEqD`

`GroupedEqD.main` is circuit-identical to `GroupedEqXV.main` (the same graduated
carry loop plus one final mod-`p` row), so the certificates delegate to the
`GroupedEqXV` loop lemmas: `Σ(Wf−1)` witnesses and `ΣWf + 1` rows, single-row
R1CS via the affine carry expressions.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace GadgetCost

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Challenge.CostR1CS
open Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostInfra

variable {L : ℕ}

/-- Cost of `GroupedEqD.main`: the graduated carry checks plus one final row. -/
theorem costIs_groupedEqD (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime)) :
    CostIs (GroupedEqD.main B gf posOf G V VR hgv input)
      ⟨GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0,
       GroupedEqXV.widthConsFrom V.Wf (G - 2) 0 + 1⟩ := by
  rw [show (⟨GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0,
        GroupedEqXV.widthConsFrom V.Wf (G - 2) 0 + 1⟩ : Count)
      = (⟨GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0,
          GroupedEqXV.widthConsFrom V.Wf (G - 2) 0⟩ + ⟨0, 1⟩ : Count) from by
    congr 1 <;> simp only [Count.add_allocations, Count.add_constraints]]
  unfold GroupedEqD.main
  refine CostIs.bind (costIs_carryLoopXV B gf posOf VR.OFFf V.Wf hgv.1.2.2.2.1 _ _ _ _) fun _ => ?_
  exact CostIs.assertZero _

theorem costIs_assertion_groupedEqD (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime)) :
    CostIs (assertion (GroupedEqD.circuit B gf posOf G V VR hgv hB1) input)
      ⟨GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0,
       GroupedEqXV.widthConsFrom V.Wf (G - 2) 0 + 1⟩ :=
  CostIs.assertion (fun n => costIs_groupedEqD B gf posOf G V VR hgv hB1 input n)

theorem isR1CS_groupedEqD (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (GroupedEqD.main B gf posOf G V VR hgv input) := by
  unfold GroupedEqD.main
  refine IsR1CSCirc.bind
    (isR1CS_carryLoopXV B gf posOf VR.OFFf V.Wf hgv.1.2.2.2.1 _ _ hl hr _ _) fun _ => ?_
  refine IsR1CSCirc.assertZero ?_
  refine isR1CSRow_of_affine ?_
  refine affine_polyEvalExpr _ _ fun i hi => ?_
  rw [Vector.getElem_ofFn]
  exact Affine.sub (hl i hi) (hr i hi)

theorem isR1CS_assertion_groupedEqD (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (GroupedEqD.circuit B gf posOf G V VR hgv hB1) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_groupedEqD B gf posOf G V VR hgv hB1 input hl hr n)

/-! ## Definitional-top variant certificates -/

/-- Cost of `GroupedEqD.mainD`: the graduated carry checks only — no final row. -/
theorem costIs_groupedEqDD (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime)) :
    CostIs (GroupedEqD.mainD B gf posOf G V VR hgv input)
      ⟨GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0,
       GroupedEqXV.widthConsFrom V.Wf (G - 2) 0⟩ := by
  unfold GroupedEqD.mainD
  exact costIs_carryLoopXV B gf posOf VR.OFFf V.Wf hgv.1.2.2.2.1 _ _ _ _

theorem costIs_assertion_groupedEqDD (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime)) :
    CostIs (assertion (GroupedEqD.circuitD B gf posOf G V VR hgv hB1) input)
      ⟨GroupedEqXV.widthAllocFrom V.Wf (G - 2) 0,
       GroupedEqXV.widthConsFrom V.Wf (G - 2) 0⟩ :=
  CostIs.assertion (fun n => costIs_groupedEqDD B gf posOf G V VR hgv hB1 input n)

theorem isR1CS_groupedEqDD (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (GroupedEqD.mainD B gf posOf G V VR hgv input) := by
  unfold GroupedEqD.mainD
  exact isR1CS_carryLoopXV B gf posOf VR.OFFf V.Wf hgv.1.2.2.2.1 _ _
    hl (affineW_rhsD B input.lhs input.rhs hl hr) _ _

theorem isR1CS_assertion_groupedEqDD (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps circomPrime L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (circomPrime > 2)] [NeZero L]
    (input : Var (GroupedEqX.InputsX L) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (GroupedEqD.circuitD B gf posOf G V VR hgv hB1) input) :=
  IsR1CSCirc.assertion
    (fun n => isR1CS_groupedEqDD B gf posOf G V VR hgv hB1 input hl hr n)

end GadgetCost
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
