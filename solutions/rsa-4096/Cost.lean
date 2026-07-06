import Solution.RSASSAPKCS1v15_SHA256_4096_65537.ModExp
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulModCanon
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.EqMod
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulModTo
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.LessThan
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.LessThanTight
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.LessThanSel
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.EqViaCarries
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.BytesToBigInt
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.PadDigest
import Challenge.Utils.CostR1CS
import Clean.Circuit.Loops

/-!
# Compositional cost (`CostIs`) and R1CS (`IsR1CSCirc`) facts for the RSA gadgets

Bottom-up `operationCount` / `operationsIsR1CS` certificates for the building-block
gadgets used by `main` (`rangeCheck`, `Normalize`, `Equal`, `LessThan`,
`EqViaCarries`, `MulMod`, `ModExp`, and the byte-glue `ByteBlock`/`BytesToBigInt`/
`PadDigest`), proved with the compositional lemmas in `Challenge.CostR1CS` (no
`native_decide`).

These leaves are all generic over the parameter bundle `P`; the top-level
`main`-specific R1CS assembly lives in `Main.lean`, which consumes these.

This file also folds in the `CostInfra` row-affineness helper for a
`ProvableVector (fields 32) n` symbolic witness vector (the byte/digest glue),
which the trusted module does not provide.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostInfra

open Challenge.CostR1CS

variable {Fld : Type} [Field Fld]

/-- Each `fields 32` row of a `varFromOffset` over a `ProvableVector (fields 32) n`
is itself a `varFromOffset`, hence affine. -/
theorem affineW_varFromOffset_pvec {n : ℕ} (off j : ℕ) (hj : j < n) :
    AffineW ((varFromOffset (ProvableVector (fields 32) n) off :
      Var (ProvableVector (fields 32) n) Fld)[j]'hj) := by
  rw [varFromOffset_vector, Vector.getElem_mapRange]
  exact affineW_varFromOffset _ _

end Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostInfra

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace GadgetCost

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Challenge.CostR1CS
open Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostInfra

/-- A `ProvableType.witness` over `α` allocates exactly `size α` cells and no
constraints. Its operation list is `[.witness (size α) ..]`, same shape as
`witnessVector`. -/
theorem CostIs.provableWitness {α : TypeMap} [ProvableType α]
    (compute : ProverEnvironment (F circomPrime) → α (F circomPrime)) :
    CostIs (ProvableType.witness (α := α) compute) ⟨size α, 0⟩ := by
  intro n; rfl

theorem IsR1CSCirc.provableWitness {α : TypeMap} [ProvableType α]
    (compute : ProverEnvironment (F circomPrime) → α (F circomPrime)) :
    IsR1CSCirc (ProvableType.witness (α := α) compute) := by
  intro n; trivial

/-- Invoking a `GeneralFormalCircuit` as a subcircuit costs exactly its `main`'s
count (same operation shape as `CostIs.subcircuit`). -/
theorem CostIs.subcircuitWithAssertion {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    {circuit : GeneralFormalCircuit (F circomPrime) Input Output}
    {b : Var Input (F circomPrime)} {K : Count}
    (h : ∀ n, operationCount ((circuit.main b).operations n) = K) :
    CostIs (subcircuitWithAssertion circuit b) K := by
  intro n
  show operationCount [Operation.subcircuit (circuit.toSubcircuit n b)] = K
  have hz : operationCount [Operation.subcircuit (circuit.toSubcircuit n b)]
      = nestedCount (circuit.toSubcircuit n b).ops := by
    show nestedCount _ + operationCount ([] : Operations (F circomPrime)) = nestedCount _
    rw [show operationCount ([] : Operations (F circomPrime)) = Count.zero from rfl, Count.add_zero]
  rw [hz]
  show nestedCount (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩) = K
  rw [show nestedCount (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩)
        = nestedListCount ((circuit.main b).operations n).toNested from rfl,
      Lemmas.operationCount_toNested]
  exact h n

theorem IsR1CSCirc.subcircuitWithAssertion {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    {circuit : GeneralFormalCircuit (F circomPrime) Input Output}
    {b : Var Input (F circomPrime)}
    (h : ∀ n, operationsIsR1CS ((circuit.main b).operations n)) :
    IsR1CSCirc (subcircuitWithAssertion circuit b) := by
  intro n
  show operationsIsR1CS [Operation.subcircuit (circuit.toSubcircuit n b)]
  refine ⟨?_, trivial⟩
  show flatOperationsIsR1CS (circuit.toSubcircuit n b).ops.toFlat
  have hofl : (circuit.toSubcircuit n b).ops.toFlat = ((circuit.main b).operations n).toFlat := by
    show (NestedOperations.nested ⟨circuit.name, ((circuit.main b).operations n).toNested⟩).toFlat = _
    rw [Operations.toNested_toFlat]
  rw [hofl]
  exact (Lemmas.operationsIsR1CS_iff_toFlat _).mp (h n)

/-! ## `toBits` / `rangeCheck` (per-limb `B`-bit range check) -/

/-- `toBits.main n x` witnesses `n` bits, boolean-constrains each, and asserts the
recomposition equals `x`: `⟨n, n+1⟩`. -/
theorem costIs_toBits (n : ℕ) (x : Expression (F circomPrime)) :
    CostIs (Gadgets.ToBits.main n x) ⟨n, n + 1⟩ := by
  unfold Gadgets.ToBits.main
  have hcount : (⟨n, 0⟩ + (⟨n * 0, n * 1⟩ + (⟨0, 1⟩ + Count.zero)) : Count) = ⟨n, n + 1⟩ := by
    show (⟨_, _⟩ : Count) = _; congr 1; simp [Count.zero]
  rw [← hcount]
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) n _) fun bits => ?_
  refine CostIs.bind
    (show CostIs (Circuit.forEach bits (fun input => assertion assertBool input) _) ⟨n * 0, n * 1⟩ from
      CostIs.forEach fun a m =>
        (CostIs.assertion (circuit := assertBool) (b := a) (K := ⟨0, 1⟩) (fun k => rfl)) m) fun _ => ?_
  refine CostIs.bind
    (show CostIs (x === Utils.Bits.fieldFromBitsExpr bits) ⟨0, 1⟩ from ?_) fun _ => CostIs.pure _
  show CostIs (Expression.assertEquals x (Utils.Bits.fieldFromBitsExpr bits)) ⟨0, 1⟩
  unfold Expression.assertEquals
  refine CostIs.assertion (K := ⟨0, 1⟩) fun m => ?_
  show operationCount ((Gadgets.Equality.main (M := id) (x, Utils.Bits.fieldFromBitsExpr bits)).operations m) = _
  unfold Gadgets.Equality.main
  simpa using (CostIs.forEach (m := 1) (fun a k => CostIs.assertZero _ k) m)

/-- A `forEach` is single-row R1CS when each *indexed* body is, so the certificate
can use that `xs[i]` is affine (the generic `IsR1CSCirc.forEach` quantifies over
all element values, too weak for booleanity rows). -/
theorem IsR1CSCirc.forEach_mem {α : Type} {m : ℕ} [Inhabited α] {xs : Vector α m}
    {body : α → Circuit (F circomPrime) Unit}
    {constant : Circuit.ConstantLength body}
    (h : ∀ (i : Fin m) n, operationsIsR1CS ((body xs[i.val]).operations n)) :
    IsR1CSCirc (Circuit.forEach xs body constant) := by
  intro n
  rw [Circuit.forEach.operations_eq]
  exact operationsIsR1CS_flatten_ofFn _ (fun i => h i _)

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

/-- `fieldFromBitsExpr` over an affine bit-vector is affine. -/
theorem affine_fieldFromBitsExpr {n : ℕ} (bits : Var (fields n) (F circomPrime))
    (h : AffineW bits) : Affine (Utils.Bits.fieldFromBitsExpr bits) := by
  unfold Utils.Bits.fieldFromBitsExpr
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    exact Affine.add hacc (Affine.mul_fconst _ (h i.val i.isLt))

/-- `toBits.main n x` is single-row R1CS when `x` is affine: each booleanity row
`bit·(bit-1)` and the recomposition row `x - fieldFromBitsExpr bits` are R1CS. -/
theorem isR1CS_toBits (n : ℕ) (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (Gadgets.ToBits.main n x) := by
  unfold Gadgets.ToBits.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector n _) fun w => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine (IsR1CSCirc.assertion (circuit := assertBool) fun j => ?_) k
    refine IsR1CSCirc.assertZero ?_ j
    show isR1CSRow (_ * (_ - 1))
    exact isR1CSRow_mul (affineW_witnessVector_output n _ w i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output n _ w i.val i.isLt) (Affine.const 1))
  · show IsR1CSCirc (x === Utils.Bits.fieldFromBitsExpr _)
    show IsR1CSCirc (Expression.assertEquals x (Utils.Bits.fieldFromBitsExpr _))
    unfold Expression.assertEquals
    refine IsR1CSCirc.assertion (circuit := Gadgets.Equality.circuit id) fun k => ?_
    show operationsIsR1CS ((Gadgets.Equality.main (M := id)
      (x, Utils.Bits.fieldFromBitsExpr ((Circuit.witnessVector n _).output w))).operations k)
    unfold Gadgets.Equality.main
    refine (IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) (m := 1) fun i j => ?_) k
    refine IsR1CSCirc.assertZero ?_ j
    simp only [circuit_norm, Vector.getElem_map, Vector.getElem_zip]
    exact isR1CSRow_of_affine (Affine.sub hx
      (affine_fieldFromBitsExpr (Vector.mapRange n fun i => Expression.var { index := w + i })
        (affineW_mapRange_var _)))

/-! ### `rangeCheck` (a `FormalAssertion` wrapping `toBits`) -/

theorem costIs_toBits_sub (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime) (x : Expression (F circomPrime)) :
    CostIs (Gadgets.ToBits.toBits n hn x) ⟨n, n + 1⟩ :=
  CostIs.subcircuitWithAssertion (fun m => costIs_toBits n x m)

theorem isR1CS_toBits_sub (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (Gadgets.ToBits.toBits n hn x) :=
  IsR1CSCirc.subcircuitWithAssertion (fun m => isR1CS_toBits n x hx m)

/-- `rangeCheck.main x = do let _ ← toBits n hn x`, hence cost `⟨n, n+1⟩`. -/
theorem costIs_rangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime) (x : Expression (F circomPrime)) :
    CostIs ((Gadgets.ToBits.rangeCheck n hn).main x) ⟨n, n + 1⟩ := by
  show CostIs (Gadgets.ToBits.toBits n hn x >>= fun _ => pure ()) ⟨n, n + 1⟩
  have := CostIs.bind (costIs_toBits_sub n hn x) (fun _ => CostIs.pure ())
  simpa [Count.add_zero] using this

theorem isR1CS_rangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc ((Gadgets.ToBits.rangeCheck n hn).main x) := by
  show IsR1CSCirc (Gadgets.ToBits.toBits n hn x >>= fun _ => pure ())
  exact IsR1CSCirc.bind (isR1CS_toBits_sub n hn x hx) (fun _ => IsR1CSCirc.pure ())

/-- The `rangeCheck` assertion invoked on `x` costs `⟨n, n+1⟩`. -/
theorem costIs_assertion_rangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (x : Expression (F circomPrime)) :
    CostIs (assertion (Gadgets.ToBits.rangeCheck n hn) x) ⟨n, n + 1⟩ :=
  CostIs.assertion (fun m => costIs_rangeCheck n hn x m)

theorem isR1CS_assertion_rangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (assertion (Gadgets.ToBits.rangeCheck n hn) x) :=
  IsR1CSCirc.assertion (fun m => isR1CS_rangeCheck n hn x hx m)

/-! ### Optimized implicit-top-bit range check used by `Normalize` -/

theorem costIs_implicitRangeCheck (n : ℕ) (hpos : 1 ≤ n) (x : Expression (F circomPrime)) :
    CostIs (RangeCheck.main n x) ⟨n - 1, n⟩ := by
  unfold RangeCheck.main
  rw [show (⟨n - 1, n⟩ : Count)
        = ⟨n - 1, 0⟩ + (⟨(n - 1) * 0, (n - 1) * 1⟩ + (⟨0, 1⟩ + Count.zero)) from by
      simp only [Count.zero]; congr 1 <;> simp only [Count.add_allocations, Count.add_constraints] <;> omega]
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) (n - 1) _) fun bits => ?_
  refine CostIs.bind (CostIs.forEach fun a m => CostIs.assertZero _ m) fun _ => ?_
  exact CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem isR1CS_implicitRangeCheck (n : ℕ) (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (RangeCheck.main n x) := by
  unfold RangeCheck.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector (n - 1) _) fun w => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    exact isR1CSRow_mul (affineW_witnessVector_output _ _ _ i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output _ _ _ i.val i.isLt) (Affine.const 1))
  · refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => IsR1CSCirc.pure _
    let bits : Var (fields (n - 1)) (F circomPrime) :=
      (Circuit.witnessVector (n - 1) fun env => Utils.Bits.fieldToBits (n - 1) (x.eval env)).output w
    have hbits : Affine (Utils.Bits.fieldFromBitsExpr bits) := by
      change Affine (Utils.Bits.fieldFromBitsExpr
        (Vector.mapRange (n - 1) fun i => Expression.var { index := w + i }))
      exact affine_fieldFromBitsExpr _ (affineW_mapRange_var _)
    let c : F circomPrime := (((2 ^ (n - 1) : ℕ) : F circomPrime)⁻¹ : F circomPrime)
    have htop : Affine (c * (x - Utils.Bits.fieldFromBitsExpr bits)) := by
      exact Affine.fconst_mul c (Affine.sub hx hbits)
    exact isR1CSRow_mul htop (Affine.sub htop (Affine.const 1))

theorem costIs_assertion_implicitRangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (hpos : 1 ≤ n) [Fact (circomPrime > 2)] (x : Expression (F circomPrime)) :
    CostIs (assertion (RangeCheck.circuit n hn hpos) x) ⟨n - 1, n⟩ :=
  CostIs.assertion (fun m => costIs_implicitRangeCheck n hpos x m)

theorem isR1CS_assertion_implicitRangeCheck (n : ℕ) (hn : (2 : ℕ) ^ n < circomPrime)
    (hpos : 1 ≤ n) [Fact (circomPrime > 2)] (x : Expression (F circomPrime)) (hx : Affine x) :
    IsR1CSCirc (assertion (RangeCheck.circuit n hn hpos) x) :=
  IsR1CSCirc.assertion (fun m => isR1CS_implicitRangeCheck n x hx m)

/-! ## G1 — `Normalize` -/

variable {m : ℕ}

/-- `Normalize.main P x` range-checks each of the `m` limbs of `x`. -/
theorem costIs_normalize (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)]
    (x : Var (BigInt m) (F circomPrime)) :
    CostIs (Normalize.main P x) ⟨m * (P.B - 1), m * P.B⟩ := by
  unfold Normalize.main
  exact CostIs.forEach (fun a n => costIs_assertion_implicitRangeCheck P.B P.hB P.hB1 a n)

theorem isR1CS_normalize (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)]
    (x : Var (BigInt m) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (Normalize.main P x) := by
  unfold Normalize.main
  exact IsR1CSCirc.forEach_mem (α := Expression (F circomPrime))
    fun i n => isR1CS_assertion_implicitRangeCheck P.B P.hB P.hB1 x[i.val] (hx i.val i.isLt) n

theorem costIs_assertion_normalize (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)]
    (x : Var (BigInt m) (F circomPrime)) :
    CostIs (assertion (Normalize.circuit P) x) ⟨m * (P.B - 1), m * P.B⟩ :=
  CostIs.assertion (fun n => costIs_normalize P x n)

theorem isR1CS_assertion_normalize (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)]
    (x : Var (BigInt m) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (assertion (Normalize.circuit P) x) :=
  IsR1CSCirc.assertion (fun n => isR1CS_normalize P x hx n)

/-! ## G1' — `NormalizeTight` -/

/-- `NormalizeTight.main P tb htb x` range-checks the first `m-1` limbs to `B` bits
and the top limb to `tb` bits: `⟨(m-1)·B + tb, (m-1)·(B+1) + (tb+1)⟩`. -/
theorem costIs_normalizeTight (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) [Fact (circomPrime > 2)] [NeZero m]
    (x : Var (BigInt m) (F circomPrime)) :
    CostIs (NormalizeTight.main P tb htb x)
      (⟨(m - 1) * (P.B - 1), (m - 1) * P.B⟩ + ⟨tb - 1, tb⟩) := by
  unfold NormalizeTight.main
  refine CostIs.bind
    (CostIs.forEach (fun a n => costIs_assertion_implicitRangeCheck P.B P.hB P.hB1 a n)) fun _ => ?_
  exact costIs_assertion_implicitRangeCheck tb htb.2 htb.1 _

theorem isR1CS_normalizeTight (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) [Fact (circomPrime > 2)] [NeZero m]
    (x : Var (BigInt m) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (NormalizeTight.main P tb htb x) := by
  unfold NormalizeTight.main
  refine IsR1CSCirc.bind
    (IsR1CSCirc.forEach_mem (α := Expression (F circomPrime))
      fun i n => isR1CS_assertion_implicitRangeCheck P.B P.hB P.hB1 (x.pop)[i.val] ?_ n) fun _ => ?_
  · rw [Vector.getElem_pop]; exact hx i.val (by have := i.isLt; omega)
  · exact isR1CS_assertion_implicitRangeCheck tb htb.2 htb.1 _
      (hx (m - 1) (by have := Nat.pos_of_neZero m; omega))

theorem costIs_assertion_normalizeTight (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb ≤ P.B) [Fact (circomPrime > 2)] [NeZero m]
    (x : Var (BigInt m) (F circomPrime)) :
    CostIs (assertion (NormalizeTight.circuit P tb htb htbB) x)
      (⟨(m - 1) * (P.B - 1), (m - 1) * P.B⟩ + ⟨tb - 1, tb⟩) :=
  CostIs.assertion (fun n => costIs_normalizeTight P tb htb x n)

theorem isR1CS_assertion_normalizeTight (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb ≤ P.B) [Fact (circomPrime > 2)] [NeZero m]
    (x : Var (BigInt m) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (assertion (NormalizeTight.circuit P tb htb htbB) x) :=
  IsR1CSCirc.assertion (fun n => isR1CS_normalizeTight P tb htb x hx n)

/-! ## `Equal` -/

/-- `Equal.main input = input.lhs === input.rhs`, an `Equality` assertion over the
`m` limbs: `⟨0, m⟩`. -/
theorem costIs_equal (input : Var (Equal.Inputs m) (F circomPrime)) :
    CostIs (Equal.main input) ⟨0, m⟩ := by
  show CostIs (Gadgets.Equality.circuit (fields m) (input.lhs, input.rhs)) ⟨0, m⟩
  refine CostIs.assertion (K := ⟨0, m⟩) fun n => ?_
  show operationCount ((Gadgets.Equality.main (M := fields m)
    (input.lhs, input.rhs)).operations n) = _
  unfold Gadgets.Equality.main
  simpa using (CostIs.forEach (m := m) (fun a k => CostIs.assertZero _ k) n)

theorem isR1CS_equal (input : Var (Equal.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (Equal.main input) := by
  show IsR1CSCirc (Gadgets.Equality.circuit (fields m) (input.lhs, input.rhs))
  refine IsR1CSCirc.assertion (circuit := Gadgets.Equality.circuit (fields m)) fun n => ?_
  show operationsIsR1CS ((Gadgets.Equality.main (M := fields m)
    (input.lhs, input.rhs)).operations n)
  unfold Gadgets.Equality.main
  refine (IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_) n
  refine IsR1CSCirc.assertZero ?_ k
  have hi : i.val < m := i.isLt
  rw [Vector.getElem_map, Vector.getElem_zip]
  exact isR1CSRow_of_affine (Affine.sub (hl i.val hi) (hr i.val hi))

theorem costIs_assertion_equal (P : BigIntParams circomPrime m)
    (input : Var (Equal.Inputs m) (F circomPrime)) :
    CostIs (assertion (Equal.circuit P) input) ⟨0, m⟩ :=
  CostIs.assertion (fun n => costIs_equal input n)

theorem isR1CS_assertion_equal (P : BigIntParams circomPrime m)
    (input : Var (Equal.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (Equal.circuit P) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_equal input hl hr n)

/-- The output of a `ProvableType.witness (α := BigInt k)` is a fresh
`varFromOffset`, hence affine at every offset. -/
theorem affineW_provableWitness_bigInt {k : ℕ}
    (compute : ProverEnvironment (F circomPrime) → BigInt k (F circomPrime)) (nd : ℕ) :
    AffineW ((ProvableType.witness (α := BigInt k) compute).output nd :
      Var (BigInt k) (F circomPrime)) := by
  rw [show ((ProvableType.witness (α := BigInt k) compute).output nd : Var (BigInt k) (F circomPrime))
        = varFromOffset (BigInt k) nd from rfl]
  exact affineW_varFromOffset _ _

theorem isR1CS_provableWitness_bigInt {k : ℕ}
    (compute : ProverEnvironment (F circomPrime) → BigInt k (F circomPrime)) :
    IsR1CSCirc (ProvableType.witness (α := BigInt k) compute) :=
  IsR1CSCirc.provableWitness _

/-- `IsR1CSCirc.witnessVector` packaged so it unifies as the first argument of
`bind_out` (avoids the `compute` metavariable elaboration-order issue). -/
theorem isR1CS_witnessVec (k : ℕ) (c : ProverEnvironment (F circomPrime) → Vector (F circomPrime) k) :
    IsR1CSCirc (Circuit.witnessVector k c) := IsR1CSCirc.witnessVector k c

/-! ## G2 — `LessThan` -/

/-- Cost of `LessThan.main P input` (m ≥ 1): witness `d` (m), normalize `d`
(`m·(B-1)` / `m·B`), witness carries (m), boolean forEach (m constraints),
linear forEach (m constraints), and the forced top carry (1 constraint). -/
theorem costIs_lessThan (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThan.Inputs m) (F circomPrime)) :
    CostIs (LessThan.main P input)
      ⟨m + m * (P.B - 1) + (m - 1), m * P.B + (m - 1) + m⟩ := by
  rw [show (⟨m + m * (P.B - 1) + (m - 1), m * P.B + (m - 1) + m⟩ : Count)
        = ⟨m, 0⟩ + (⟨m * (P.B - 1), m * P.B⟩ + (⟨m - 1, 0⟩ +
            (⟨(m - 1) * 0, (m - 1) * 1⟩ + ⟨m * 0, m * 1⟩))) from by
      congr 1 <;> simp only [Count.add_allocations, Count.add_constraints] <;> ring]
  unfold LessThan.main
  refine CostIs.bind (CostIs.provableWitness _) fun d => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessVector (m - 1) _) fun carry => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  exact CostIs.forEach fun a n => CostIs.assertZero _ n

theorem isR1CS_lessThan (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThan.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (LessThan.main P input) := by
  have hne : ¬ (m = 0) := NeZero.ne m
  unfold LessThan.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nd => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nd))
    fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec (m - 1) _) fun nc => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- boolean forEach (all but the top carry): each `c * (c - 1)` is a single row
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul (affineW_witnessVector_output _ _ _ i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output _ _ _ i.val i.isLt) (Affine.const 1))
  -- linear forEach (last op): each constraint is affine (the top limb's
  -- carry-out is the constant `0`, affine as well)
  refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
  refine IsR1CSCirc.assertZero ?_ k
  rw [Vector.getElem_mapFinRange]
  refine isR1CSRow_of_affine ?_
  refine Affine.sub (Affine.sub (Affine.add (Affine.add (Affine.add
    (hl i.val i.isLt) (affineW_provableWitness_bigInt _ nd i.val i.isLt)) ?_) ?_)
    (hr i.val i.isLt))
    (Affine.mul_fconst _ ?_)
  · split
    · exact Affine.zero
    · exact affineW_witnessVector_output _ _ _ _ (by omega)
  · split
    · exact Affine.const 1
    · exact Affine.zero
  · split
    · exact Affine.zero
    · rename_i hne
      have hne' : ¬ (i.val = m - 1) := by simpa using hne
      exact affineW_witnessVector_output (m - 1) _ _ i.val (by omega)

theorem costIs_assertion_lessThan (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThan.Inputs m) (F circomPrime)) :
    CostIs (assertion (LessThan.circuit P) input)
      ⟨m + m * (P.B - 1) + (m - 1), m * P.B + (m - 1) + m⟩ :=
  CostIs.assertion (fun n => costIs_lessThan P input n)

theorem isR1CS_assertion_lessThan (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThan.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (LessThan.circuit P) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_lessThan P input hl hr n)

/-! ## G2' — `LessThanTight` -/

theorem costIs_lessThanTight (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb ≤ P.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThanTight.Inputs m) (F circomPrime)) :
    CostIs (LessThanTight.main P tb htb htbB input)
      ⟨m + ((m - 1) * (P.B - 1) + (tb - 1)) + (m - 1),
        ((m - 1) * P.B + tb) + (m - 1) + m⟩ := by
  rw [show (⟨m + ((m - 1) * (P.B - 1) + (tb - 1)) + (m - 1),
        ((m - 1) * P.B + tb) + (m - 1) + m⟩ : Count)
        = ⟨m, 0⟩
          + ((⟨(m - 1) * (P.B - 1), (m - 1) * P.B⟩ + ⟨tb - 1, tb⟩)
            + (⟨m - 1, 0⟩ + (⟨(m - 1) * 0, (m - 1) * 1⟩ + ⟨m * 0, m * 1⟩))) from by
      congr 1 <;> simp only [Count.add_allocations, Count.add_constraints] <;> ring]
  unfold LessThanTight.main
  refine CostIs.bind (CostIs.provableWitness _) fun d => ?_
  refine CostIs.bind (costIs_assertion_normalizeTight P tb htb htbB _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessVector (m - 1) _) fun carry => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  exact CostIs.forEach fun a n => CostIs.assertZero _ n

theorem isR1CS_lessThanTight (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb ≤ P.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThanTight.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (LessThanTight.main P tb htb htbB input) := by
  have hne : ¬ (m = 0) := NeZero.ne m
  unfold LessThanTight.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nd => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalizeTight P tb htb htbB _ (affineW_provableWitness_bigInt _ nd))
    fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec (m - 1) _) fun nc => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul (affineW_witnessVector_output _ _ _ i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output _ _ _ i.val i.isLt) (Affine.const 1))
  refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
  refine IsR1CSCirc.assertZero ?_ k
  rw [Vector.getElem_mapFinRange]
  refine isR1CSRow_of_affine ?_
  refine Affine.sub (Affine.sub (Affine.add (Affine.add (Affine.add
    (hl i.val i.isLt) (affineW_provableWitness_bigInt _ nd i.val i.isLt)) ?_) ?_)
    (hr i.val i.isLt))
    (Affine.mul_fconst _ ?_)
  · split
    · exact Affine.zero
    · exact affineW_witnessVector_output _ _ _ _ (by omega)
  · split
    · exact Affine.const 1
    · exact Affine.zero
  · split
    · exact Affine.zero
    · rename_i hne
      have hne' : ¬ (i.val = m - 1) := by simpa using hne
      exact affineW_witnessVector_output (m - 1) _ _ i.val (by omega)

theorem costIs_assertion_lessThanTight (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb ≤ P.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThanTight.Inputs m) (F circomPrime)) :
    CostIs (assertion (LessThanTight.circuit P tb htb htbB) input)
      ⟨m + ((m - 1) * (P.B - 1) + (tb - 1)) + (m - 1),
        ((m - 1) * P.B + tb) + (m - 1) + m⟩ :=
  CostIs.assertion (fun n => costIs_lessThanTight P tb htb htbB input n)

theorem isR1CS_assertion_lessThanTight (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb ≤ P.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThanTight.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (LessThanTight.circuit P tb htb htbB) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_lessThanTight P tb htb htbB input hl hr n)

/-! ## G4 — `EqViaCarries` -/

/-- Cost of `EqViaCarries.main P input` (m ≥ 1, so `2m-1 ≥ 1`): witness the
`2m-1` carries, range-check each to `W` bits, and one linear constraint per
index (the top index's constraint folds in the zero signed carry-out, so no
separate forced-top-carry row is needed). -/
theorem costIs_eqViaCarries (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (EqViaCarries.Inputs m) (F circomPrime)) :
    CostIs (EqViaCarries.main P input)
      ⟨(2 * m - 1 - 1) + (2 * m - 1 - 1) * (P.W - 1), (2 * m - 1 - 1) * P.W + (2 * m - 1)⟩ := by
  have hM : 0 < 2 * m - 1 := by have := Nat.pos_of_neZero m; omega
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
  rw [show (⟨(2 * m - 1 - 1) + (2 * m - 1 - 1) * (P.W - 1), (2 * m - 1 - 1) * P.W + (2 * m - 1)⟩ : Count)
        = ⟨2 * m - 1 - 1, 0⟩ + (⟨(2 * m - 1 - 1) * (P.W - 1), (2 * m - 1 - 1) * P.W⟩ +
            ⟨(2 * m - 1) * 0, (2 * m - 1) * 1⟩) from by
      congr 1 <;> simp only [Count.add_allocations, Count.add_constraints] <;> ring]
  unfold EqViaCarries.main
  refine CostIs.bind (CostIs.witnessVector (2 * m - 1 - 1) _) fun carry => ?_
  refine CostIs.bind (CostIs.forEach fun a n => costIs_assertion_implicitRangeCheck P.W P.hW hWpos a n) fun _ => ?_
  exact CostIs.forEach fun a n => CostIs.assertZero _ n

theorem isR1CS_eqViaCarries (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (EqViaCarries.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (EqViaCarries.main P input) := by
  have hM : 0 < 2 * m - 1 := by have := Nat.pos_of_neZero m; omega
  have hne : ¬ (2 * m - 1 = 0) := by omega
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
  unfold EqViaCarries.main
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec (2 * m - 1 - 1) _) fun nc => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- range-check each carry: `W`-bit, R1CS since carry entries are affine
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    exact isR1CS_assertion_implicitRangeCheck P.W P.hW hWpos _
      (affineW_witnessVector_output _ _ _ i.val i.isLt) k
  -- per-index linear constraint (last op) is affine (the top index's carry-out
  -- is the constant 0, affine as well)
  refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
  refine IsR1CSCirc.assertZero ?_ k
  rw [Vector.getElem_mapFinRange]
  refine isR1CSRow_of_affine ?_
  refine Affine.sub (Affine.sub (Affine.add (hl i.val i.isLt) ?_) (hr i.val i.isLt))
    (Affine.mul_fconst _ ?_)
  · split
    · exact Affine.zero
    · exact Affine.sub (affineW_witnessVector_output _ _ _ _ (by omega)) (Affine.const _)
  · split
    · exact Affine.zero
    · rename_i hne
      have hne' : ¬ (i.val = 2 * m - 1 - 1) := by simpa using hne
      exact Affine.sub (affineW_witnessVector_output (2 * m - 1 - 1) _ _ i.val (by omega))
        (Affine.const _)

theorem costIs_assertion_eqViaCarries (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)]
    [NeZero m] (input : Var (EqViaCarries.Inputs m) (F circomPrime)) :
    CostIs (assertion (EqViaCarries.circuit P) input)
      ⟨(2 * m - 1 - 1) + (2 * m - 1 - 1) * (P.W - 1), (2 * m - 1 - 1) * P.W + (2 * m - 1)⟩ :=
  CostIs.assertion (fun n => costIs_eqViaCarries P input n)

theorem isR1CS_assertion_eqViaCarries (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)]
    [NeZero m] (input : Var (EqViaCarries.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (EqViaCarries.circuit P) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_eqViaCarries P input hl hr n)

/-! ## G5 — `MulMod` -/

/-- `A*B - C` with all of `A, B, C` affine is a single R1CS row (`⟨A,z⟩·⟨B,z⟩ =
⟨C,z⟩`). Mirror of the trusted `isR1CSRow_sub_mul`, with the product on the left
(the form `MulMod.witnessedMul` produces: `a[i]·b[j] − pp[t]`). -/
theorem isR1CSRow_mul_sub {A B C : Expression (F circomPrime)}
    (hA : Affine A) (hB : Affine B) (hC : Affine C) : isR1CSRow (A * B - C) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · exact isR1CSRow_of_r1csProducts (k := 0)
      (by show r1csProducts (A * B + -C) = some 0
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_of_affine hC, h]) (by omega)
  · exact isR1CSRow_of_r1csProducts (k := 1)
      (by show r1csProducts (A * B + -C) = some 1
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_of_affine hC, h]) (by omega)

/-- Each coefficient of `bigIntMulVars pp` is an affine fold of the (affine)
witnessed products `pp`, hence affine. This is what makes the witnessed-product
multiply R1CS-clean: the convolution coefficients fed to `EqViaCarries` are linear
forms over fresh cells rather than rank-≥2 sums of products. -/
theorem affineW_bigIntMulVars [NeZero m] (pp : Vector (Expression (F circomPrime)) (m * m))
    (hpp : ∀ t (ht : t < m * m), Affine pp[t]) :
    AffineW (bigIntMulVars pp) := by
  intro k hk
  simp only [bigIntMulVars]
  rw [Vector.getElem_mapFinRange, vector_foldl_finRange]
  refine affine_finFoldl' _ _ Affine.zero fun acc i hacc => ?_
  split
  · exact Affine.add hacc (hpp _ _)
  · exact hacc

/-- The output of `witnessedMul a b` is `bigIntMulVars` over the freshly witnessed
product matrix, hence affine at every offset. -/
theorem affineW_witnessedMul_output [NeZero m] (a b : Var (BigInt m) (F circomPrime)) (off : ℕ) :
    AffineW ((MulMod.witnessedMul a b).output off) := by
  rw [show (MulMod.witnessedMul a b).output off
        = bigIntMulVars (Vector.mapRange (m * m) fun i => var (F := F circomPrime) { index := off + i })
      from MulMod.witnessedMul_output off a b]
  refine affineW_bigIntMulVars _ fun t ht => ?_
  rw [Vector.getElem_mapRange]; exact Affine.var _

/-- `witnessedMul a b` witnesses the `m·m` product matrix (`⟨m·m, 0⟩`) and asserts
each product (`m·m` rows): `⟨m·m, m·m⟩`. -/
theorem costIs_witnessedMul [NeZero m] (a b : Var (BigInt m) (F circomPrime)) :
    CostIs (MulMod.witnessedMul a b) ⟨m * m, m * m⟩ := by
  rw [show (⟨m * m, m * m⟩ : Count)
        = ⟨m * m, 0⟩ + (⟨m * m * 0, m * m * 1⟩ + Count.zero) from by
      simp only [Count.zero]; congr 1
      simp only [Count.add_constraints]; ring]
  unfold MulMod.witnessedMul
  refine CostIs.bind (CostIs.provableWitness _) fun pp => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  exact CostIs.pure _

/-- Each product assert `a[t/m]·b[t%m] − pp[t]` of `witnessedMul` is a single R1CS
row (a single rank-1 product minus an affine cell), given affine inputs `a, b`. -/
theorem isR1CS_witnessedMul [NeZero m] (a b : Var (BigInt m) (F circomPrime))
    (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (MulMod.witnessedMul a b) := by
  unfold MulMod.witnessedMul
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun npp => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun t k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul_sub (ha _ (Nat.div_lt_of_lt_mul t.isLt))
      (hb _ (Nat.mod_lt _ (Nat.pos_of_neZero m)))
      (affineW_provableWitness_bigInt (k := m * m) _ npp t.val t.isLt)
  exact IsR1CSCirc.pure _


/-! ### `interpolatedMul` (xJsnark O(m) interpolation check) — cost, R1CS, affine output -/

/-- `polyEvalExpr` over an affine coefficient vector is affine (an affine fold of
`coeffs[i] * const`). -/
theorem affine_polyEvalExpr {n : ℕ} (coeffs : Vector (Expression (F circomPrime)) n) (x : F circomPrime)
    (h : ∀ i (hi : i < n), Affine coeffs[i]) :
    Affine (MulMod.polyEvalExpr coeffs x) := by
  simp only [MulMod.polyEvalExpr]
  refine affine_finFoldl' _ _ Affine.zero fun acc i hacc => ?_
  exact Affine.add hacc (Affine.mul_fconst _ (h i.val i.isLt))

/-- The output of `interpolatedMul a b` is the affine vector of freshly witnessed
coefficient cells, hence affine at every offset. -/
theorem affineW_interpolatedMul_output [NeZero m] (a b : Var (BigInt m) (F circomPrime)) (off : ℕ) :
    AffineW ((MulMod.interpolatedMul a b).output off) := by
  rw [show (MulMod.interpolatedMul a b).output off
        = (Vector.mapRange (2 * m - 1) fun i => var (F := F circomPrime) { index := off + i })
      from MulMod.interpolatedMul_output off a b]
  intro k hk
  rw [Vector.getElem_mapRange]; exact Affine.var _

/-- `interpolatedMul a b` witnesses the `2m-1` coefficient cells (`⟨2m-1, 0⟩`) and
asserts each of the `2m-1` point constraints (`2m-1` rows): `⟨2m-1, 2m-1⟩`. -/
theorem costIs_interpolatedMul [NeZero m] (a b : Var (BigInt m) (F circomPrime)) :
    CostIs (MulMod.interpolatedMul a b) ⟨2 * m - 1, 2 * m - 1⟩ := by
  rw [show (⟨2 * m - 1, 2 * m - 1⟩ : Count)
        = ⟨2 * m - 1, 0⟩ + (⟨(2 * m - 1) * 0, (2 * m - 1) * 1⟩ + Count.zero) from by
      simp only [Count.zero]; congr 1
      simp only [Count.add_constraints]; ring]
  unfold MulMod.interpolatedMul
  refine CostIs.bind (CostIs.provableWitness _) fun z => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  exact CostIs.pure _

/-- Each point constraint `polyEval a c · polyEval b c − polyEval z c` of
`interpolatedMul` is a single R1CS row (affine·affine − affine), given affine
inputs `a, b`. -/
theorem isR1CS_interpolatedMul [NeZero m] (a b : Var (BigInt m) (F circomPrime))
    (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (MulMod.interpolatedMul a b) := by
  unfold MulMod.interpolatedMul
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nz => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun t k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul_sub (affine_polyEvalExpr _ _ (fun i hi => ha i hi))
      (affine_polyEvalExpr _ _ (fun i hi => hb i hi))
      (affine_polyEvalExpr _ _ (fun i hi =>
        affineW_provableWitness_bigInt (k := 2 * m - 1) _ nz i hi))
  exact IsR1CSCirc.pure _


/-! ### `witnessedSquare` (symmetric product matrix) — cost, R1CS, affine output -/

/-- The output coefficient vector of `witnessedSquare` is affine (a linear form
over the mirrored witnessed products). -/
theorem affineW_witnessedSquare_output [NeZero m] (a : Var (BigInt m) (F circomPrime)) (off : ℕ) :
    AffineW ((SquareModLazy.witnessedSquare a).output off) := by
  rw [show (SquareModLazy.witnessedSquare a).output off
        = bigIntMulVars (SquareModLazy.sqMatrix
            (Vector.mapRange (SquareModLazy.tri m) fun i => var (F := F circomPrime) { index := off + i }))
      from SquareModLazy.witnessedSquare_output off a]
  refine affineW_bigIntMulVars _ fun t ht => ?_
  simp only [SquareModLazy.sqMatrix, Vector.getElem_ofFn, Vector.getElem_mapRange]
  exact Affine.var _

/-- `witnessedSquare a` witnesses the `tri m = m(m+1)/2` triangular products
(`⟨tri m, 0⟩`) and asserts each (`tri m` rows): `⟨tri m, tri m⟩`. -/
theorem costIs_witnessedSquare [NeZero m] (a : Var (BigInt m) (F circomPrime)) :
    CostIs (SquareModLazy.witnessedSquare a) ⟨SquareModLazy.tri m, SquareModLazy.tri m⟩ := by
  rw [show (⟨SquareModLazy.tri m, SquareModLazy.tri m⟩ : Count)
        = ⟨SquareModLazy.tri m, 0⟩ + (⟨SquareModLazy.tri m * 0, SquareModLazy.tri m * 1⟩ + Count.zero) from by
      simp only [Count.zero]; congr 1
      simp only [Count.add_constraints]; ring]
  unfold SquareModLazy.witnessedSquare
  refine CostIs.bind (CostIs.provableWitness _) fun pp => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  exact CostIs.pure _

/-- Each product assert `a[sqPair(t).1]·a[sqPair(t).2] − pp[t]` of `witnessedSquare`
is a single R1CS row, given affine input `a`. -/
theorem isR1CS_witnessedSquare [NeZero m] (a : Var (BigInt m) (F circomPrime))
    (ha : AffineW a) :
    IsR1CSCirc (SquareModLazy.witnessedSquare a) := by
  unfold SquareModLazy.witnessedSquare
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun npp => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun t k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul_sub (ha _ (SquareModLazy.sqPair t).1.isLt)
      (ha _ (SquareModLazy.sqPair t).2.isLt)
      (affineW_provableWitness_bigInt (k := SquareModLazy.tri m) _ npp t.val t.isLt)
  exact IsR1CSCirc.pure _

/-- The per-gadget `Count` of one `MulMod` subcircuit, as a sum of the leaf
gadget counts: witness `q,r` (`m + m`), normalize `q,r` (two `⟨m·(B-1), m·B⟩`),
the two `witnessedMul` product matrices (`⟨m·m, m·m⟩` each), and the
`EqViaCarries` and `LessThan` assertions. -/
def mulModCount (B W : ℕ) : Count :=
  ⟨m, 0⟩ + (⟨m, 0⟩ + (⟨m * (B - 1), m * B⟩ + (⟨m * (B - 1), m * B⟩ +
    (⟨2 * m - 1, 2 * m - 1⟩ + (⟨2 * m - 1, 2 * m - 1⟩ +
    (⟨(2 * m - 1 - 1) + (2 * m - 1 - 1) * (W - 1), (2 * m - 1 - 1) * W + (2 * m - 1)⟩ +
      (⟨m + m * (B - 1) + (m - 1), m * B + (m - 1) + m⟩ + Count.zero)))))))

theorem costIs_mulMod (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (MulMod.Inputs m) (F circomPrime)) :
    CostIs (MulMod.main P input) (mulModCount (m := m) P.B P.W) := by
  unfold MulMod.main mulModCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pc => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Sqn => ?_
  refine CostIs.bind (costIs_assertion_eqViaCarries P _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_lessThan P _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_mulMod (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulMod.Inputs m) (F circomPrime)) :
    CostIs (subcircuit (MulMod.circuit P) b) (mulModCount (m := m) P.B P.W) :=
  CostIs.subcircuit (fun n => costIs_mulMod P b n)

/-! ## G5-lazy — `MulModLazy` cost -/

/-- Per-gadget `Count` of one `MulModLazy` subcircuit: like `mulModCount` but the
remainder is range-checked by `NormalizeTight` (`⟨(m-1)B, (m-1)(B+1)⟩ + ⟨tb, tb+1⟩`)
and there is no `LessThan`. -/
def mulModLazyCount (B W tb : ℕ) : Count :=
  ⟨m, 0⟩ + (⟨m, 0⟩ + (⟨m * (B - 1), m * B⟩ +
    ((⟨(m - 1) * (B - 1), (m - 1) * B⟩ + ⟨tb - 1, tb⟩) +
    (⟨2 * m - 1, 2 * m - 1⟩ + (⟨2 * m - 1, 2 * m - 1⟩ +
    (⟨(2 * m - 1 - 1) + (2 * m - 1 - 1) * (W - 1), (2 * m - 1 - 1) * W + (2 * m - 1)⟩ + Count.zero))))))

theorem costIs_mulModLazy (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb ≤ P.B) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (MulMod.Inputs m) (F circomPrime)) :
    CostIs (MulModLazy.main P tb htb htbB input) (mulModLazyCount (m := m) P.B P.W tb) := by
  unfold MulModLazy.main mulModLazyCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalizeTight P tb htb htbB _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pc => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Sqn => ?_
  refine CostIs.bind (costIs_assertion_eqViaCarries P _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_mulModLazy (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb ≤ P.B) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulMod.Inputs m) (F circomPrime)) :
    CostIs (subcircuit (MulModLazy.circuit P tb htb htbB) b) (mulModLazyCount (m := m) P.B P.W tb) :=
  CostIs.subcircuit (fun n => costIs_mulModLazy P tb htb htbB b n)

/-! ## G5′-lazy — `SquareModLazy` cost -/

/-- Per-gadget `Count` of one `SquareModLazy` subcircuit: like `mulModLazyCount` but
the `a·a` product matrix is witnessed symmetrically (`⟨tri m, tri m⟩` instead of
`⟨m·m, m·m⟩`). -/
def squareModLazyCount (B W tb : ℕ) : Count :=
  ⟨m, 0⟩ + (⟨m, 0⟩ + ((⟨(m - 1) * (B - 1), (m - 1) * B⟩ + ⟨tb + 2 - 1, tb + 2⟩) +
    ((⟨(m - 1) * (B - 1), (m - 1) * B⟩ + ⟨tb - 1, tb⟩) +
    (⟨2 * m - 1, 2 * m - 1⟩ + (⟨2 * m - 1, 2 * m - 1⟩ +
    (⟨(2 * m - 1 - 1) + (2 * m - 1 - 1) * (W - 1), (2 * m - 1 - 1) * W + (2 * m - 1)⟩ + Count.zero))))))

theorem costIs_squareModLazy (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 2 ≤ P.B) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (SquareModLazy.Inputs m) (F circomPrime)) :
    CostIs (SquareModLazy.main P tb htb htbB input) (squareModLazyCount (m := m) P.B P.W tb) := by
  unfold SquareModLazy.main squareModLazyCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_normalizeTight P (tb + 2) _ htbB _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalizeTight P tb htb (Nat.le_of_succ_le (Nat.le_of_succ_le htbB)) _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pc => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Sqn => ?_
  refine CostIs.bind (costIs_assertion_eqViaCarries P _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_squareModLazy (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 2 ≤ P.B) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (SquareModLazy.Inputs m) (F circomPrime)) :
    CostIs (subcircuit (SquareModLazy.circuit P tb htb htbB) b) (squareModLazyCount (m := m) P.B P.W tb) :=
  CostIs.subcircuit (fun n => costIs_squareModLazy P tb htb htbB b n)

theorem squareModLazyCount_allocations (B W tb : ℕ) :
    (squareModLazyCount (m := m) B W tb).allocations = ModExp.squareModLen (m := m) B W tb := by
  unfold squareModLazyCount ModExp.squareModLen
  simp only [Count.add_allocations, Count.zero]
  ring

/-! ## G6 — `ModExp` -/

/-- `mulModLazyCount` equals `ModExp.mulModLen` (the per-iteration allocation count)
in its `allocations` field; the loop's `localLength` formula uses `mulModLen`. -/
theorem mulModLazyCount_allocations (B W tb : ℕ) :
    (mulModLazyCount (m := m) B W tb).allocations = ModExp.mulModLen (m := m) B W tb := by
  unfold mulModLazyCount ModExp.mulModLen
  simp only [Count.add_allocations, Count.zero]
  ring

/-- The `modExpLoop` over a bit list costs `(bs.length + bs.count true)` copies of
`mulModLazyCount` (one squaring per bit, one extra multiply per set bit). -/
theorem costIs_modExpLoop (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 2 ≤ P.B) [Fact (circomPrime > 2)] [NeZero m]
    (base n : Var (BigInt m) (F circomPrime)) :
    ∀ (bs : List Bool) (acc : Var (BigInt m) (F circomPrime)),
      CostIs (ModExp.modExpLoop P tb htb htbB base n bs acc)
        ⟨bs.length * (squareModLazyCount (m := m) P.B P.W tb).allocations
            + bs.count true * (mulModLazyCount (m := m) P.B P.W tb).allocations,
         bs.length * (squareModLazyCount (m := m) P.B P.W tb).constraints
            + bs.count true * (mulModLazyCount (m := m) P.B P.W tb).constraints⟩ := by
  intro bs
  induction bs with
  | nil =>
    intro acc
    simp only [ModExp.modExpLoop, List.length_nil, List.count_nil, Nat.zero_mul, Nat.add_zero]
    exact CostIs.pure _
  | cons bit rest ih =>
    intro acc
    set S := squareModLazyCount (m := m) P.B P.W tb with hS
    set K := mulModLazyCount (m := m) P.B P.W tb with hK
    rw [show ModExp.modExpLoop P tb htb htbB base n (bit :: rest) acc
        = (do
            let sq ← subcircuit (SquareModLazy.circuit P tb htb htbB) { a := acc, modulus := n }
            let acc' ← if bit then subcircuit (MulModLazy.circuit P tb htb (Nat.le_of_succ_le (Nat.le_of_succ_le htbB))) { a := sq, b := base, modulus := n }
                       else pure sq
            ModExp.modExpLoop P tb htb htbB base n rest acc') from rfl]
    cases bit
    · -- clear bit: one squaring, then recurse
      have hcount : (Count.mk ((rest.length + 1) * S.allocations + rest.count true * K.allocations)
            ((rest.length + 1) * S.constraints + rest.count true * K.constraints))
          = (S + (Count.zero +
              Count.mk (rest.length * S.allocations + rest.count true * K.allocations)
               (rest.length * S.constraints + rest.count true * K.constraints)) : Count) := by
        congr 1 <;> simp only [Count.add_allocations, Count.add_constraints, Count.zero] <;> ring
      simp only [List.length_cons, List.count_cons, Bool.false_eq_true, if_false, Nat.add_zero,
        beq_iff_eq, hcount]
      refine CostIs.bind (costIs_sub_squareModLazy P tb htb htbB _) fun sq => ?_
      exact CostIs.bind (CostIs.pure sq) fun acc' => ih acc'
    · -- set bit: squaring + multiply, then recurse
      have hcount : (Count.mk ((rest.length + 1) * S.allocations + (rest.count true + 1) * K.allocations)
            ((rest.length + 1) * S.constraints + (rest.count true + 1) * K.constraints))
          = (S + (K +
              Count.mk (rest.length * S.allocations + rest.count true * K.allocations)
               (rest.length * S.constraints + rest.count true * K.constraints)) : Count) := by
        congr 1 <;> simp only [Count.add_allocations, Count.add_constraints] <;> ring
      simp only [List.length_cons, List.count_cons, beq_self_eq_true, if_true, hcount]
      refine CostIs.bind (costIs_sub_squareModLazy P tb htb htbB _) fun sq => ?_
      exact CostIs.bind (costIs_sub_mulModLazy P tb htb (Nat.le_of_succ_le (Nat.le_of_succ_le htbB)) _) fun acc' => ih acc'

/-- Total `Count` of `ModExp.main`: for `e ≥ 1` (`eBits = _ :: tail`), `tail.length`
squarings and `tail.count true` multiplies. -/
def modExpCountC (e B W tb : ℕ) : Count :=
  match ModExp.eBits e with
  | [] => Count.zero
  | _ :: tail =>
    ⟨tail.length * (squareModLazyCount (m := m) B W tb).allocations
        + tail.count true * (mulModLazyCount (m := m) B W tb).allocations,
     tail.length * (squareModLazyCount (m := m) B W tb).constraints
        + tail.count true * (mulModLazyCount (m := m) B W tb).constraints⟩

theorem costIs_modExp (P : RSAParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 2 ≤ P.bigIntParams.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (ModExp.Inputs m) (F circomPrime)) :
    CostIs (ModExp.main P tb htb htbB input)
      (modExpCountC (m := m) P.e P.bigIntParams.B P.bigIntParams.W tb) := by
  unfold ModExp.main modExpCountC
  cases h : ModExp.eBits P.e with
  | nil =>
    exact CostIs.pure _
  | cons headBit tail =>
    exact costIs_modExpLoop P.bigIntParams tb htb htbB _ _ tail _

theorem costIs_sub_modExp (P : RSAParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 2 ≤ P.bigIntParams.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (ModExp.Inputs m) (F circomPrime)) :
    CostIs (subcircuit (ModExp.circuit P tb htb htbB) b)
      (modExpCountC (m := m) P.e P.bigIntParams.B P.bigIntParams.W tb) :=
  CostIs.subcircuit (fun n => costIs_modExp P tb htb htbB b n)

/-! ## G5-canon — `MulModCanon` cost (structurally identical to `MulMod`) -/

theorem costIs_mulModCanon (P : BigIntParams circomPrime m) (tb : ℕ) (htbB : tb ≤ P.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (MulMod.Inputs m) (F circomPrime)) :
    CostIs (MulModCanon.main P input) (mulModCount (m := m) P.B P.W) := by
  unfold MulModCanon.main mulModCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (CostIs.provableWitness _) fun r => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_normalize P _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pc => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Sqn => ?_
  refine CostIs.bind (costIs_assertion_eqViaCarries P _) fun _ => ?_
  refine CostIs.bind (costIs_assertion_lessThan P _) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_mulModCanon (P : BigIntParams circomPrime m) (tb : ℕ) (htbB : tb ≤ P.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulMod.Inputs m) (F circomPrime)) :
    CostIs (subcircuit (MulModCanon.circuit P tb htbB) b) (mulModCount (m := m) P.B P.W) :=
  CostIs.subcircuit (fun n => costIs_mulModCanon P tb htbB b n)

/-! ## G7 — `EqMod` (bit-quotient congruence pin) -/

theorem costIs_eqMod (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (EqMod.Inputs m) (F circomPrime)) :
    CostIs (EqMod.main P input)
      ⟨1 + m + ((2 * m - 1 - 1) + (2 * m - 1 - 1) * (P.W - 1)),
       1 + m + ((2 * m - 1 - 1) * P.W + (2 * m - 1))⟩ := by
  rw [show (⟨1 + m + ((2 * m - 1 - 1) + (2 * m - 1 - 1) * (P.W - 1)),
        1 + m + ((2 * m - 1 - 1) * P.W + (2 * m - 1))⟩ : Count)
        = ⟨1, 0⟩ + (⟨0, 1⟩ + (⟨m, 0⟩ + (⟨m * 0, m * 1⟩ +
            ⟨(2 * m - 1 - 1) + (2 * m - 1 - 1) * (P.W - 1),
              (2 * m - 1 - 1) * P.W + (2 * m - 1)⟩))) from by
      congr 1 <;> simp only [Count.add_allocations, Count.add_constraints] <;> ring]
  unfold EqMod.main
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) 1 _) fun qv => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) m _) fun pp => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  exact costIs_assertion_eqViaCarries P _

theorem costIs_assertion_eqMod (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (EqMod.Inputs m) (F circomPrime)) :
    CostIs (assertion (EqMod.circuit P) b)
      ⟨1 + m + ((2 * m - 1 - 1) + (2 * m - 1 - 1) * (P.W - 1)),
       1 + m + ((2 * m - 1 - 1) * P.W + (2 * m - 1))⟩ :=
  CostIs.assertion (fun n => costIs_eqMod P b n)

theorem isR1CS_eqMod (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (EqMod.Inputs m) (F circomPrime))
    (hx : AffineW input.lhs) (hy : AffineW input.rhs) (hn : AffineW input.modulus) :
    IsR1CSCirc (EqMod.main P input) := by
  unfold EqMod.main
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec 1 _) fun nq => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero
    (isR1CSRow_mul (affineW_witnessVector_output 1 _ _ 0 (by omega))
      (Affine.sub (affineW_witnessVector_output 1 _ _ 0 (by omega)) (Affine.const 1)))) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec m _) fun npp => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul_sub (affineW_witnessVector_output 1 _ _ 0 (by omega))
      (hn i.val i.isLt)
      (affineW_witnessVector_output m _ _ i.val i.isLt)
  · refine isR1CS_assertion_eqViaCarries P _ ?_ ?_
    · intro i hi
      simp only [EqMod.padCoeffs]
      rw [Vector.getElem_mapFinRange i hi]
      split
      · rename_i h
        exact hx i h
      · exact Affine.zero
    · intro i hi
      simp only [EqMod.sumCoeffs]
      rw [Vector.getElem_mapFinRange i hi]
      split
      · rename_i h
        refine Affine.add ?_ (hy i h)
        exact affineW_witnessVector_output m _ _ i h
      · exact Affine.zero
theorem isR1CS_assertion_eqMod (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (EqMod.Inputs m) (F circomPrime))
    (hx : AffineW b.lhs) (hy : AffineW b.rhs) (hn : AffineW b.modulus) :
    IsR1CSCirc (assertion (EqMod.circuit P) b) :=
  IsR1CSCirc.assertion (fun n => isR1CS_eqMod P b hx hy hn n)

/-! ## G8 — `MulModTo` (fused final modmul + equality) -/

/-- Per-gadget `Count` of the `MulModTo` assertion: witness `q` (`m`),
`NormalizeTight q` at top-limb `tq`, the two `interpolatedMul` blocks, and the
`EqViaCarries` chain. No remainder witness, no remainder range check. -/
def mulModToCount (B W tq : ℕ) : Count :=
  ⟨m, 0⟩ + ((⟨(m - 1) * (B - 1), (m - 1) * B⟩ + ⟨tq - 1, tq⟩) +
    (⟨2 * m - 1, 2 * m - 1⟩ + (⟨2 * m - 1, 2 * m - 1⟩ +
    ⟨(2 * m - 1 - 1) + (2 * m - 1 - 1) * (W - 1), (2 * m - 1 - 1) * W + (2 * m - 1)⟩)))

theorem costIs_mulModTo (P : BigIntParams circomPrime m) (tq : ℕ)
    (htq : 1 ≤ tq ∧ (2 : ℕ) ^ tq < circomPrime) (htqB : tq ≤ P.B) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (MulModTo.InputsTo m) (F circomPrime)) :
    CostIs (MulModTo.main P tq htq htqB input) (mulModToCount (m := m) P.B P.W tq) := by
  unfold MulModTo.main mulModToCount
  refine CostIs.bind (CostIs.provableWitness _) fun q => ?_
  refine CostIs.bind (costIs_assertion_normalizeTight P tq htq htqB _) fun _ => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Pc => ?_
  refine CostIs.bind (costIs_interpolatedMul _ _) fun Sqn => ?_
  exact costIs_assertion_eqViaCarries P _

theorem costIs_assertion_mulModTo (P : BigIntParams circomPrime m) (tb tq : ℕ)
    (htq : 1 ≤ tq ∧ (2 : ℕ) ^ tq < circomPrime) (htqB : tq ≤ P.B)
    (htb1 : 1 ≤ tb) (htbq : tb ≤ tq) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulModTo.InputsTo m) (F circomPrime)) :
    CostIs (assertion (MulModTo.circuit P tb tq htq htqB htb1 htbq) b)
      (mulModToCount (m := m) P.B P.W tq) :=
  CostIs.assertion (fun n => costIs_mulModTo P tq htq htqB b n)

/-- `MulModTo.main` is single-row R1CS: the `q` witness cells are affine, the
`interpolatedMul` point rows are affine·affine − affine, and the `EqViaCarries`
right-hand side `Sqn[k] + em[k]` is affine when the `em` limbs are (they are
linear forms over the digest bits). -/
theorem isR1CS_mulModTo (P : BigIntParams circomPrime m) (tq : ℕ)
    (htq : 1 ≤ tq ∧ (2 : ℕ) ^ tq < circomPrime) (htqB : tq ≤ P.B) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (MulModTo.InputsTo m) (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hn : AffineW input.modulus)
    (hem : AffineW input.em) :
    IsR1CSCirc (MulModTo.main P tq htq htqB input) := by
  unfold MulModTo.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalizeTight P tq htq htqB _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha hb) fun nPc => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_interpolatedMul _ _ (affineW_provableWitness_bigInt _ nq) hn) fun nSqn => ?_
  refine isR1CS_assertion_eqViaCarries P _ ?_ ?_
  · exact affineW_mapRange_var _
  · intro i hi
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add (affineW_interpolatedMul_output _ _ _ i hi) (hem i (by assumption))
    · exact affineW_interpolatedMul_output _ _ _ i hi

theorem isR1CS_assertion_mulModTo (P : BigIntParams circomPrime m) (tb tq : ℕ)
    (htq : 1 ≤ tq ∧ (2 : ℕ) ^ tq < circomPrime) (htqB : tq ≤ P.B)
    (htb1 : 1 ≤ tb) (htbq : tb ≤ tq) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulModTo.InputsTo m) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus) (hem : AffineW b.em) :
    IsR1CSCirc (assertion (MulModTo.circuit P tb tq htq htqB htb1 htbq) b) :=
  IsR1CSCirc.assertion (fun n => isR1CS_mulModTo P tq htq htqB b ha hb hn hem n)

/-! ## Byte glue — `BytesToBigInt`, `PadDigest` (byte-split affine packing) -/

/-- A constant expression times an affine expression is affine. -/
theorem affine_const_mul (c : F circomPrime) {a : Expression (F circomPrime)}
    (ha : Affine a) : Affine (Expression.const c * a) :=
  Affine.fconst_mul c ha

/-- `splitLowSum` is an affine fold of the (affine) split bits. -/
theorem affine_splitLowSum {nb : ℕ} (bits : Vector (Expression (F circomPrime)) nb)
    (hbits : ∀ j (hj : j < nb), Affine bits[j]) (s : ℕ) :
    Affine (Bytes.splitLowSum bits s) := by
  unfold Bytes.splitLowSum
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    refine Affine.add hacc (Affine.mul_deg0 ?_ (degree_const _))
    split
    · exact hbits _ (by assumption)
    · exact Affine.zero

/-- `splitTop` is affine: a constant times (byte − affine bit sum). -/
theorem affine_splitTop {nb : ℕ} (bytes : Vector (Expression (F circomPrime)) 512)
    (bits : Vector (Expression (F circomPrime)) nb)
    (hbytes : ∀ j (hj : j < 512), Affine bytes[j])
    (hbits : ∀ j (hj : j < nb), Affine bits[j]) (s : ℕ) :
    Affine (Bytes.splitTop bytes bits s) := by
  unfold Bytes.splitTop
  exact affine_const_mul _ (Affine.sub (hbytes _ (by omega)) (affine_splitLowSum bits hbits s))

/-- `splitLoExpr` is an affine fold of the (affine) split bits. -/
theorem affine_splitLoExpr {nb : ℕ} (bits : Vector (Expression (F circomPrime)) nb)
    (hbits : ∀ j (hj : j < nb), Affine bits[j]) (k : ℕ) :
    Affine (Bytes.splitLoExpr bits k) := by
  unfold Bytes.splitLoExpr
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    refine Affine.add hacc ?_
    split
    · rename_i h
      exact Affine.mul_deg0 (hbits _ h.2) (degree_const _)
    · exact Affine.zero

/-- `splitHiExpr` is affine: an affine bit fold plus `splitTop · const`. -/
theorem affine_splitHiExpr {nb : ℕ} (bytes : Vector (Expression (F circomPrime)) 512)
    (bits : Vector (Expression (F circomPrime)) nb)
    (hbytes : ∀ j (hj : j < 512), Affine bytes[j])
    (hbits : ∀ j (hj : j < nb), Affine bits[j]) (k : ℕ) :
    Affine (Bytes.splitHiExpr bytes bits k) := by
  unfold Bytes.splitHiExpr
  refine Affine.add ?_ (Affine.mul_deg0 (affine_splitTop bytes bits hbytes hbits _)
    (degree_const _))
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    refine Affine.add hacc ?_
    split
    · rename_i h
      exact Affine.mul_deg0 (hbits _ h.2) (degree_const _)
    · exact Affine.zero

/-- Each limb of `packLimbsSplit` is affine when the bytes and the `lo`/`hi`
pieces are. -/
theorem affineW_packLimbsSplit (bytes : Vector (Expression (F circomPrime)) 512)
    (splitLo splitHi : ℕ → Expression (F circomPrime))
    (hbytes : ∀ j (hj : j < 512), Affine bytes[j])
    (hlo : ∀ k, Affine (splitLo k)) (hhi : ∀ k, Affine (splitHi k)) :
    AffineW (Bytes.packLimbsSplit bytes splitLo splitHi) := by
  intro k hk
  rw [Bytes.packLimbsSplit, Vector.getElem_ofFn]
  refine Affine.add (Affine.add ?_ ?_) ?_
  · split
    · exact hhi _
    · exact Affine.zero
  · apply affine_finFoldl'
    · exact Affine.zero
    · intro acc d hacc
      refine Affine.add hacc ?_
      split
      · exact Affine.mul_deg0 (hbytes _ (by omega)) (degree_const _)
      · exact Affine.zero
  · split
    · exact Affine.mul_deg0 (hlo _) (degree_const _)
    · exact Affine.zero

/-- Each entry of the EM byte-expression vector is affine (a constant or a
digest byte). -/
theorem affine_emByteExpr (digest : Vector (Expression (F circomPrime)) 32)
    (hdigest : ∀ j (hj : j < 32), Affine digest[j]) :
    ∀ j (hj : j < 512), Affine (BytesLemmas.emByteExpr digest)[j] := by
  intro j hj
  rw [BytesLemmas.emByteExpr, Vector.getElem_ofFn]
  split
  · exact Affine.const _
  · exact hdigest _ (by omega)

/-- `emSplitLo` is affine (witnessed bits or a constant). -/
theorem affine_emSplitLo (bits : Vector (Expression (F circomPrime)) 14)
    (hbits : ∀ j (hj : j < 14), Affine bits[j]) (k : ℕ) :
    Affine (Bytes.emSplitLo bits k) := by
  unfold Bytes.emSplitLo
  split
  · exact affine_splitLoExpr bits hbits k
  · exact Affine.const _

/-- `emSplitHi` is affine (witnessed bits + implicit top, or a constant). -/
theorem affine_emSplitHi (emBytes : Vector (Expression (F circomPrime)) 512)
    (bits : Vector (Expression (F circomPrime)) 14)
    (hbytes : ∀ j (hj : j < 512), Affine emBytes[j])
    (hbits : ∀ j (hj : j < 14), Affine bits[j]) (k : ℕ) :
    Affine (Bytes.emSplitHi emBytes bits k) := by
  unfold Bytes.emSplitHi
  split
  · exact affine_splitHiExpr emBytes bits hbytes hbits k
  · exact Affine.const _

/-- The output limbs of a `BytesToBigInt` subcircuit are affine (in the input
bytes and the fresh split-bit witnesses). -/
theorem affineW_sub_bytesToBigInt (bytes : Var (fields modulusBytesLen) (F circomPrime))
    (hbytes : AffineW bytes) (n : ℕ) :
    AffineW ((subcircuit BytesToBigInt.circuit bytes).output n) := by
  have h : (subcircuit BytesToBigInt.circuit bytes).output n
      = Bytes.packLimbsSplit bytes (Bytes.splitLoExpr (varFromOffset (fields 203) n))
          (Bytes.splitHiExpr bytes (varFromOffset (fields 203) n)) := by
    simp only [circuit_norm, subcircuit, BytesToBigInt.circuit, BytesToBigInt.elaborated]
  rw [h]
  exact affineW_packLimbsSplit _ _ _ (fun j hj => hbytes j hj)
    (fun k => affine_splitLoExpr _ (fun j hj => affineW_varFromOffset _ _ j hj) k)
    (fun k => affine_splitHiExpr _ _ (fun j hj => hbytes j hj)
      (fun j hj => affineW_varFromOffset _ _ j hj) k)

/-- The output limbs of a `PadDigest` subcircuit are affine (in the digest
bytes and the fresh split-bit witnesses). -/
theorem affineW_sub_padDigest (digest : Var (fields digestBytesLen) (F circomPrime))
    (hdigest : AffineW digest) (n : ℕ) :
    AffineW ((subcircuit PadDigest.circuit digest).output n) := by
  have h : (subcircuit PadDigest.circuit digest).output n
      = Bytes.packLimbsSplit (BytesLemmas.emByteExpr digest)
          (Bytes.emSplitLo (varFromOffset (fields 14) n))
          (Bytes.emSplitHi (BytesLemmas.emByteExpr digest) (varFromOffset (fields 14) n)) := by
    simp only [circuit_norm, subcircuit, PadDigest.circuit, PadDigest.elaborated]
  rw [h]
  exact affineW_packLimbsSplit _ _ _
    (affine_emByteExpr digest (fun j hj => hdigest j hj))
    (fun k => affine_emSplitLo _ (fun j hj => affineW_varFromOffset _ _ j hj) k)
    (fun k => affine_emSplitHi _ _ (affine_emByteExpr digest (fun j hj => hdigest j hj))
      (fun j hj => affineW_varFromOffset _ _ j hj) k)

/-- The output limbs of a `MulMod` subcircuit are a fresh `varFromOffset`
(the remainder `r`), hence affine. -/
theorem affineW_sub_mulMod (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulMod.Inputs m) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit (MulMod.circuit P) b).output n) := by
  have h : (subcircuit (MulMod.circuit P) b).output n = varFromOffset (BigInt m) (n + m) := by
    simp only [circuit_norm, subcircuit, MulMod.circuit, MulMod.elaborated]
  rw [h]
  exact affineW_varFromOffset _ _

/-- The output limbs of a `MulModLazy` subcircuit are a fresh `varFromOffset`. -/
theorem affineW_sub_mulModLazy (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb ≤ P.B) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulMod.Inputs m) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit (MulModLazy.circuit P tb htb htbB) b).output n) := by
  have h : (subcircuit (MulModLazy.circuit P tb htb htbB) b).output n = varFromOffset (BigInt m) (n + m) := by
    simp only [circuit_norm, subcircuit, MulModLazy.circuit, MulModLazy.elaborated]
  rw [h]
  exact affineW_varFromOffset _ _

/-- The output limbs of a `MulModCanon` subcircuit are a fresh `varFromOffset`. -/
theorem affineW_sub_mulModCanon (P : BigIntParams circomPrime m) (tb : ℕ) (htbB : tb ≤ P.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulMod.Inputs m) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit (MulModCanon.circuit P tb htbB) b).output n) := by
  have h : (subcircuit (MulModCanon.circuit P tb htbB) b).output n = varFromOffset (BigInt m) (n + m) := by
    simp only [circuit_norm, subcircuit, MulModCanon.circuit, MulModCanon.elaborated]
  rw [h]
  exact affineW_varFromOffset _ _

-- Keep the heavy affine folds opaque so `unfold *.main` below stays cheap.
attribute [local irreducible] Bytes.packLimbs Bytes.emBits Bytes.byteFromBits
  Bytes.packLimbsSplit Bytes.splitLoExpr Bytes.splitHiExpr Bytes.splitTop
  Bytes.splitLowSum Bytes.emSplitLo Bytes.emSplitHi

/-- `BytesToBigInt.main` = witness `29·7 = 203` split bits + 203 booleanity
rows + 29 implicit-top-bit rows + pure affine packing: `⟨203, 232⟩`. -/
theorem costIs_bytesToBigInt (bytes : Var (fields modulusBytesLen) (F circomPrime)) :
    CostIs (BytesToBigInt.main bytes) ⟨203, 232⟩ := by
  unfold BytesToBigInt.main
  rw [show (⟨203, 232⟩ : Count)
        = ⟨203, 0⟩ + (⟨203 * 0, 203 * 1⟩ + (⟨29 * 0, 29 * 1⟩ + Count.zero)) from by
      simp only [Count.zero]
      congr 1 <;> simp only [Count.add_allocations, Count.add_constraints] <;> omega]
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) 203 _) fun splitBits => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_bytesToBigInt (bytes : Var (fields modulusBytesLen) (F circomPrime)) :
    CostIs (subcircuit BytesToBigInt.circuit bytes) ⟨203, 232⟩ :=
  CostIs.subcircuit (fun n => costIs_bytesToBigInt bytes n)

/-- `PadDigest.main` = witness `2·7 = 14` split bits + 14 booleanity rows + 2
implicit-top-bit rows + pure affine packing: `⟨14, 16⟩`. -/
theorem costIs_padDigest (digest : Var (fields digestBytesLen) (F circomPrime)) :
    CostIs (PadDigest.main digest) ⟨14, 16⟩ := by
  unfold PadDigest.main
  rw [show (⟨14, 16⟩ : Count)
        = ⟨14, 0⟩ + (⟨14 * 0, 14 * 1⟩ + (⟨2 * 0, 2 * 1⟩ + Count.zero)) from by
      simp only [Count.zero]
      congr 1 <;> simp only [Count.add_allocations, Count.add_constraints] <;> omega]
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) 14 _) fun splitBits => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  exact CostIs.pure _

theorem costIs_sub_padDigest (digest : Var (fields digestBytesLen) (F circomPrime)) :
    CostIs (subcircuit PadDigest.circuit digest) ⟨14, 16⟩ :=
  CostIs.subcircuit (fun n => costIs_padDigest digest n)

/-! ## R1CS certificates for `MulMod` / `ModExp` and the byte subcircuits

`MulMod` is fully single-row R1CS. The key is `witnessedMul`: instead of feeding
`EqViaCarries` the schoolbook convolution `bigIntMulNoReduce a b` (whose `k`-th
coefficient is a rank-≥2 *sum of products* `a[i]·b[k−i]`), each product `a[i]·b[j]`
is first witnessed as a fresh cell (one rank-1 row `a[i]·b[j] − pp[t] = 0`), so the
convolution coefficients `bigIntMulVars pp` fed to `EqViaCarries` are linear forms
over those cells — affine, hence single-R1CS-row clean (`affineW_bigIntMulVars`). -/

/-- **R1CS certificate for `MulMod`.**

`q`, `r` are witnessed (affine); `Normalize q/r`, the two `witnessedMul` blocks,
`EqViaCarries`, and `LessThan {r, n}` are each single-row R1CS once their inputs
are affine. The `EqViaCarries` inputs are affine because `witnessedMul` returns
the convolution as a linear form over the freshly witnessed products
(`affineW_witnessedMul_output`). -/
theorem isR1CS_mulMod (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (MulMod.Inputs m) (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hn : AffineW input.modulus) :
    IsR1CSCirc (MulMod.main P input) := by
  unfold MulMod.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  -- witness the two product matrices: `a·b` and `q·n` (each `m·m` rank-1 rows)
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha hb) fun nPc => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_interpolatedMul _ _ (affineW_provableWitness_bigInt _ nq) hn) fun nSqn => ?_
  -- EqViaCarries on the affine coefficient vectors `Pc = bigIntMulVars (a·b)` and
  -- `S = bigIntMulVars (q·n) + r` (both linear forms over witnessed cells).
  refine IsR1CSCirc.bind (isR1CS_assertion_eqViaCarries P _ ?_ ?_) fun _ => ?_
  · -- `Pc` is the affine output of `interpolatedMul a b`
    exact affineW_mapRange_var _
  · -- `S[i] = Sqn[i] (+ r[i])` is affine: a sum of affine witnessed forms
    intro i hi
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add (affineW_interpolatedMul_output _ _ _ i hi)
        (affineW_provableWitness_bigInt _ nr i (by assumption))
    · exact affineW_interpolatedMul_output _ _ _ i hi
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- LessThan {r, n}: r is the witnessed remainder (affine), n is affine
    refine isR1CS_assertion_lessThan P _ ?_ hn
    intro i hi
    change Affine (varFromOffset (BigInt m) nr : Var (BigInt m) (F circomPrime))[i]
    exact affineW_varFromOffset _ _ i hi
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_mulMod (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulMod.Inputs m) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus) :
    IsR1CSCirc (subcircuit (MulMod.circuit P) b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_mulMod P b ha hb hn n)

/-- `MulModLazy.main` is single-row R1CS (like `MulMod`, minus the `LessThan`). -/
theorem isR1CS_mulModLazy (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb ≤ P.B) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (MulMod.Inputs m) (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hn : AffineW input.modulus) :
    IsR1CSCirc (MulModLazy.main P tb htb htbB input) := by
  unfold MulModLazy.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalizeTight P tb htb htbB _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha hb) fun nPc => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_interpolatedMul _ _ (affineW_provableWitness_bigInt _ nq) hn) fun nSqn => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_eqViaCarries P _ ?_ ?_) fun _ => ?_
  · exact affineW_mapRange_var _
  · intro i hi
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add (affineW_interpolatedMul_output _ _ _ i hi)
        (affineW_provableWitness_bigInt _ nr i (by assumption))
    · exact affineW_interpolatedMul_output _ _ _ i hi
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_mulModLazy (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb ≤ P.B) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulMod.Inputs m) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus) :
    IsR1CSCirc (subcircuit (MulModLazy.circuit P tb htb htbB) b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_mulModLazy P tb htb htbB b ha hb hn n)

/-- **R1CS certificate for `SquareModLazy`.** Like `isR1CS_mulModLazy` but the `a·a`
block is `witnessedSquare` (still single-row R1CS with affine input `a`). -/
theorem isR1CS_squareModLazy (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 2 ≤ P.B) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (SquareModLazy.Inputs m) (F circomPrime))
    (ha : AffineW input.a) (hn : AffineW input.modulus) :
    IsR1CSCirc (SquareModLazy.main P tb htb htbB input) := by
  unfold SquareModLazy.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalizeTight P (tb + 2) _ htbB _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalizeTight P tb htb (Nat.le_of_succ_le (Nat.le_of_succ_le htbB)) _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha ha) fun nPc => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_interpolatedMul _ _ (affineW_provableWitness_bigInt _ nq) hn) fun nSqn => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_eqViaCarries P _ ?_ ?_) fun _ => ?_
  · exact affineW_mapRange_var _
  · intro i hi
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add (affineW_interpolatedMul_output _ _ _ i hi)
        (affineW_provableWitness_bigInt _ nr i (by assumption))
    · exact affineW_interpolatedMul_output _ _ _ i hi
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_squareModLazy (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 2 ≤ P.B) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (SquareModLazy.Inputs m) (F circomPrime))
    (ha : AffineW b.a) (hn : AffineW b.modulus) :
    IsR1CSCirc (subcircuit (SquareModLazy.circuit P tb htb htbB) b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_squareModLazy P tb htb htbB b ha hn n)

theorem affineW_sub_squareModLazy (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 2 ≤ P.B) [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (SquareModLazy.Inputs m) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit (SquareModLazy.circuit P tb htb htbB) b).output n) := by
  have h : (subcircuit (SquareModLazy.circuit P tb htb htbB) b).output n
      = varFromOffset (BigInt m) (n + m) := by
    simp only [circuit_norm, subcircuit, SquareModLazy.circuit, SquareModLazy.elaborated]
  rw [h]
  exact affineW_varFromOffset _ _

/-- `MulModCanon.main` is single-row R1CS (structurally identical to `MulMod`). -/
theorem isR1CS_mulModCanon (P : BigIntParams circomPrime m) (tb : ℕ) (htbB : tb ≤ P.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (MulMod.Inputs m) (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hn : AffineW input.modulus) :
    IsR1CSCirc (MulModCanon.main P input) := by
  unfold MulModCanon.main
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nq => ?_
  refine IsR1CSCirc.bind_out (isR1CS_provableWitness_bigInt _) fun nr => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nq)) fun _ => ?_
  refine IsR1CSCirc.bind
    (isR1CS_assertion_normalize P _ (affineW_provableWitness_bigInt _ nr)) fun _ => ?_
  refine IsR1CSCirc.bind_out (isR1CS_interpolatedMul _ _ ha hb) fun nPc => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_interpolatedMul _ _ (affineW_provableWitness_bigInt _ nq) hn) fun nSqn => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_eqViaCarries P _ ?_ ?_) fun _ => ?_
  · exact affineW_mapRange_var _
  · intro i hi
    rw [Vector.getElem_mapFinRange]
    split
    · exact Affine.add (affineW_interpolatedMul_output _ _ _ i hi)
        (affineW_provableWitness_bigInt _ nr i (by assumption))
    · exact affineW_interpolatedMul_output _ _ _ i hi
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine isR1CS_assertion_lessThan P _ ?_ hn
    intro i hi
    change Affine (varFromOffset (BigInt m) nr : Var (BigInt m) (F circomPrime))[i]
    exact affineW_varFromOffset _ _ i hi
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_mulModCanon (P : BigIntParams circomPrime m) (tb : ℕ) (htbB : tb ≤ P.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (MulMod.Inputs m) (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hn : AffineW b.modulus) :
    IsR1CSCirc (subcircuit (MulModCanon.circuit P tb htbB) b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_mulModCanon P tb htbB b ha hb hn n)

/-- The final `MulModCanon`-then-`Equal` block is single-row R1CS. Isolated with
*abstract* operands so its elaboration never reduces the deep `ModExp` output that
`a` stands for (avoiding a `whnf` blow-up at the `main` call site). -/
theorem isR1CS_mulModCanon_equal (P : BigIntParams circomPrime m) (tb : ℕ) (htbB : tb ≤ P.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (a bb n h : Var (BigInt m) (F circomPrime))
    (ha : AffineW a) (hbb : AffineW bb) (hn : AffineW n) (hh : AffineW h) :
    IsR1CSCirc (do
      let recovered ← subcircuit (MulModCanon.circuit P tb htbB) { a := a, b := bb, modulus := n }
      assertion (Equal.circuit P) { lhs := recovered, rhs := h }) := by
  refine IsR1CSCirc.bind_out (isR1CS_sub_mulModCanon P tb htbB _ ha hbb hn) fun nrecc => ?_
  exact isR1CS_assertion_equal P _ (affineW_sub_mulModCanon P tb htbB _ nrecc) hh

/-- **R1CS certificate for the `modExpLoop`.** Threads the invariant "the running
accumulator's limbs are affine" through the loop: each `MulMod` is R1CS (modulo
the `MulMod` gap), and its output (the remainder) is a fresh witness, hence affine. -/
theorem isR1CS_modExpLoop (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 2 ≤ P.B) [Fact (circomPrime > 2)] [NeZero m]
    (base n : Var (BigInt m) (F circomPrime)) (hbase : AffineW base) (hn : AffineW n) :
    ∀ (bs : List Bool) (acc : Var (BigInt m) (F circomPrime)), AffineW acc →
      IsR1CSCirc (ModExp.modExpLoop P tb htb htbB base n bs acc) := by
  intro bs
  induction bs with
  | nil => intro acc hacc; simp only [ModExp.modExpLoop]; exact IsR1CSCirc.pure _
  | cons bit rest ih =>
    intro acc hacc
    rw [show ModExp.modExpLoop P tb htb htbB base n (bit :: rest) acc
        = (do
            let sq ← subcircuit (SquareModLazy.circuit P tb htb htbB) { a := acc, modulus := n }
            let acc' ← if bit then subcircuit (MulModLazy.circuit P tb htb (Nat.le_of_succ_le (Nat.le_of_succ_le htbB))) { a := sq, b := base, modulus := n }
                       else pure sq
            ModExp.modExpLoop P tb htb htbB base n rest acc') from rfl]
    refine IsR1CSCirc.bind_out (isR1CS_sub_squareModLazy P tb htb htbB _ hacc hn) fun nsq => ?_
    have hsq : AffineW ((subcircuit (SquareModLazy.circuit P tb htb htbB) { a := acc, modulus := n }).output nsq) :=
      affineW_sub_squareModLazy P tb htb htbB _ nsq
    cases bit
    · simp only [Bool.false_eq_true, if_false]
      refine IsR1CSCirc.bind_out (IsR1CSCirc.pure _) fun nacc' => ?_
      exact ih _ hsq
    · simp only [if_true]
      refine IsR1CSCirc.bind_out (isR1CS_sub_mulModLazy P tb htb (Nat.le_of_succ_le (Nat.le_of_succ_le htbB)) _ hsq hbase hn) fun nmul => ?_
      exact ih _ (affineW_sub_mulModLazy P tb htb (Nat.le_of_succ_le (Nat.le_of_succ_le htbB)) _ nmul)

theorem isR1CS_modExp (P : RSAParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 2 ≤ P.bigIntParams.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (ModExp.Inputs m) (F circomPrime))
    (hbase : AffineW input.base) (hn : AffineW input.modulus) :
    IsR1CSCirc (ModExp.main P tb htb htbB input) := by
  unfold ModExp.main
  cases h : ModExp.eBits P.e with
  | nil =>
    simp only []
    intro k
    -- the `e = 0` branch returns the constant `1`, no operations
    rw [show (Vector.ofFn fun k : Fin m => if k.val = 0 then (1 : Expression (F circomPrime)) else 0)
          = (Vector.ofFn fun k : Fin m => if k.val = 0 then (1 : Expression (F circomPrime)) else 0) from rfl]
    exact (IsR1CSCirc.pure _ : IsR1CSCirc (pure _)) k
  | cons headBit tail =>
    simp only []
    exact isR1CS_modExpLoop P.bigIntParams tb htb htbB _ _ hbase hn tail _ hbase

theorem isR1CS_sub_modExp (P : RSAParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 2 ≤ P.bigIntParams.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (ModExp.Inputs m) (F circomPrime))
    (hbase : AffineW b.base) (hn : AffineW b.modulus) :
    IsR1CSCirc (subcircuit (ModExp.circuit P tb htb htbB) b) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_modExp P tb htb htbB b hbase hn n)

/-- The accumulator output of `modExpLoop` is affine: it is either the seed `acc`
(empty bit list) or a fresh `MulModLazy` remainder witness (`varFromOffset`). -/
theorem affineW_modExpLoop_output (P : BigIntParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 2 ≤ P.B) [Fact (circomPrime > 2)] [NeZero m]
    (base n : Var (BigInt m) (F circomPrime)) (_hbase : AffineW base) (_hn : AffineW n) :
    ∀ (bs : List Bool) (acc : Var (BigInt m) (F circomPrime)) (offset : ℕ), AffineW acc →
      AffineW ((ModExp.modExpLoop P tb htb htbB base n bs acc).output offset) := by
  intro bs
  induction bs with
  | nil => intro acc offset hacc; simpa only [ModExp.modExpLoop, Circuit.pure_output_eq] using hacc
  | cons bit rest ih =>
    intro acc offset hacc
    rw [show ModExp.modExpLoop P tb htb htbB base n (bit :: rest) acc
        = (do
            let sq ← subcircuit (SquareModLazy.circuit P tb htb htbB) { a := acc, modulus := n }
            let acc' ← if bit then subcircuit (MulModLazy.circuit P tb htb (Nat.le_of_succ_le (Nat.le_of_succ_le htbB))) { a := sq, b := base, modulus := n }
                       else pure sq
            ModExp.modExpLoop P tb htb htbB base n rest acc') from rfl]
    rw [Circuit.bind_output_eq]
    cases bit
    · simp only [Bool.false_eq_true, if_false, Circuit.bind_output_eq, Circuit.pure_output_eq]
      exact ih _ _ (affineW_sub_squareModLazy P tb htb htbB _ _)
    · simp only [if_true, Circuit.bind_output_eq]
      exact ih _ _ (affineW_sub_mulModLazy P tb htb (Nat.le_of_succ_le (Nat.le_of_succ_le htbB)) _ _)

theorem affineW_sub_modExp (P : RSAParams circomPrime m) (tb : ℕ)
    (htb : 1 ≤ tb ∧ (2 : ℕ) ^ tb < circomPrime) (htbB : tb + 2 ≤ P.bigIntParams.B)
    [Fact (circomPrime > 2)] [NeZero m]
    (b : Var (ModExp.Inputs m) (F circomPrime)) (off : ℕ)
    (hbase : AffineW b.base) (hn : AffineW b.modulus) :
    AffineW ((subcircuit (ModExp.circuit P tb htb htbB) b).output off) := by
  have h : (subcircuit (ModExp.circuit P tb htb htbB) b).output off = (ModExp.main P tb htb htbB b).output off := by
    simp only [circuit_norm, subcircuit, ModExp.circuit]
  rw [h]
  unfold ModExp.main
  cases hb : ModExp.eBits P.e with
  | nil =>
    simp only [Circuit.pure_output_eq]
    intro i hi
    rw [Vector.getElem_ofFn]
    split
    · exact Affine.const 1
    · exact Affine.zero
  | cons headBit tail =>
    exact affineW_modExpLoop_output P.bigIntParams tb htb htbB _ _ hbase hn tail _ _ hbase

/-! ### Byte-subcircuit R1CS (fully R1CS — no gaps) -/

theorem isR1CS_bytesToBigInt (bytes : Var (fields modulusBytesLen) (F circomPrime))
    (hbytes : AffineW bytes) : IsR1CSCirc (BytesToBigInt.main bytes) := by
  unfold BytesToBigInt.main
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec 203 _) fun nbits => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- booleanity rows: `bit · (bit − 1)`
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    exact isR1CSRow_mul (affineW_witnessVector_output _ _ _ i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output _ _ _ i.val i.isLt) (Affine.const 1))
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- implicit-top-bit rows: `top · (top − 1)` with `top` affine
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun s k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_ofFn]
    have htop := affine_splitTop bytes
      ((Circuit.witnessVector 203 (Bytes.splitBitsWitness bytes)).output nbits)
      (fun j hj => hbytes j hj)
      (fun j hj => affineW_witnessVector_output _ _ _ j hj) s.val
    exact isR1CSRow_mul htop (Affine.sub htop (Affine.const 1))
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_bytesToBigInt (bytes : Var (fields modulusBytesLen) (F circomPrime))
    (hbytes : AffineW bytes) : IsR1CSCirc (subcircuit BytesToBigInt.circuit bytes) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_bytesToBigInt bytes hbytes n)

theorem isR1CS_padDigest (digest : Var (fields digestBytesLen) (F circomPrime))
    (hdigest : AffineW digest) : IsR1CSCirc (PadDigest.main digest) := by
  unfold PadDigest.main
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec 14 _) fun nbits => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- booleanity rows
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    exact isR1CSRow_mul (affineW_witnessVector_output _ _ _ i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output _ _ _ i.val i.isLt) (Affine.const 1))
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- implicit-top-bit rows
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun s k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_ofFn]
    have htop := affine_splitTop (BytesLemmas.emByteExpr digest)
      ((Circuit.witnessVector 14 (Bytes.digestSplitBitsWitness digest)).output nbits)
      (affine_emByteExpr digest (fun j hj => hdigest j hj))
      (fun j hj => affineW_witnessVector_output _ _ _ j hj) s.val
    exact isR1CSRow_mul htop (Affine.sub htop (Affine.const 1))
  exact IsR1CSCirc.pure _

theorem isR1CS_sub_padDigest (digest : Var (fields digestBytesLen) (F circomPrime))
    (hdigest : AffineW digest) : IsR1CSCirc (subcircuit PadDigest.circuit digest) :=
  IsR1CSCirc.subcircuit (fun n => isR1CS_padDigest digest hdigest n)

/-- The `modulus` slice of the offset-0 input allocation is a `varFromOffset`. -/
theorem affineW_input_modulus :
    AffineW (varFromOffset Input 0 : Var Input (F circomPrime)).modulus := by
  have h : (varFromOffset Input 0 : Var Input (F circomPrime)).modulus
      = varFromOffset (fields modulusBytesLen) 0 := by simp only [circuit_norm]
  rw [h]; exact affineW_varFromOffset _ _

theorem affineW_input_signature :
    AffineW (varFromOffset Input 0 : Var Input (F circomPrime)).signature := by
  have h : (varFromOffset Input 0 : Var Input (F circomPrime)).signature
      = varFromOffset (fields modulusBytesLen) (modulusBytesLen + digestBytesLen) := by
    simp only [circuit_norm]
  rw [h]; exact affineW_varFromOffset _ _

theorem affineW_input_digest :
    AffineW (varFromOffset Input 0 : Var Input (F circomPrime)).digest := by
  have h : (varFromOffset Input 0 : Var Input (F circomPrime)).digest
      = varFromOffset (fields digestBytesLen) modulusBytesLen := by simp only [circuit_norm]
  rw [h]; exact affineW_varFromOffset _ _

/-! ## G2'' — `LessThanSel` -/

/-- Cost of `LessThanSel.main P input`: witness the one-hot selector (`m`),
booleanity forEach (`m` rows), the selector-sum row (1), gating forEach
(`m - 1` rows), witness the difference cell (1), selection forEach (`m` rows),
and one implicit `B`-bit range check on the difference cell (`B - 1` / `B`). -/
theorem costIs_lessThanSel (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThanSel.Inputs m) (F circomPrime)) :
    CostIs (LessThanSel.main P input)
      ⟨m + 1 + (P.B - 1), m + 1 + (m - 1) + m + P.B⟩ := by
  rw [show (⟨m + 1 + (P.B - 1), m + 1 + (m - 1) + m + P.B⟩ : Count)
        = ⟨m, 0⟩ + (⟨m * 0, m * 1⟩ + (⟨0, 1⟩ + (⟨(m - 1) * 0, (m - 1) * 1⟩ +
            (⟨1, 0⟩ + (⟨m * 0, m * 1⟩ + ⟨P.B - 1, P.B⟩))))) from by
      congr 1 <;> simp only [Count.add_allocations, Count.add_constraints] <;> ring]
  unfold LessThanSel.main
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) m _) fun s => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) 1 _) fun d => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  exact costIs_assertion_implicitRangeCheck P.B P.hB P.hB1 _

theorem costIs_assertion_lessThanSel (P : BigIntParams circomPrime m)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThanSel.Inputs m) (F circomPrime)) :
    CostIs (assertion (LessThanSel.circuit P) input)
      ⟨m + 1 + (P.B - 1), m + 1 + (m - 1) + m + P.B⟩ :=
  CostIs.assertion (fun n => costIs_lessThanSel P input n)

theorem isR1CS_lessThanSel (P : BigIntParams circomPrime m) [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThanSel.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (LessThanSel.main P input) := by
  unfold LessThanSel.main
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec m _) fun ns => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- booleanity rows: each `s · (s - 1)` is a product of affine witnessed cells
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul (affineW_witnessVector_output _ _ _ i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output _ _ _ i.val i.isLt) (Affine.const 1))
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => ?_
  · -- the selector-sum row is affine
    exact isR1CSRow_of_affine (Affine.sub
      (LessThanSel.affine_prefixSum _ (affineW_witnessVector_output m _ ns) m)
      (Affine.const 1))
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- gating rows: `(rhs − lhs) · prefixSum` is a product of two affine forms
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    have hi1 : i.val + 1 < m := by have := i.isLt; omega
    exact isR1CSRow_mul (Affine.sub (hr (i.val + 1) hi1) (hl (i.val + 1) hi1))
      (LessThanSel.affine_prefixSum _ (affineW_witnessVector_output m _ ns) (i.val + 1))
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec 1 _) fun nd => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- selection rows: `s · (rhs − lhs − 1 − d)` is a product of two affine forms
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul (affineW_witnessVector_output m _ ns i.val i.isLt)
      (Affine.sub (Affine.sub (Affine.sub (hr i.val i.isLt) (hl i.val i.isLt))
        (Affine.const 1)) (affineW_witnessVector_output 1 _ nd 0 (by omega)))
  -- the range-check subcircuit on the witnessed difference cell
  exact isR1CS_assertion_implicitRangeCheck P.B P.hB P.hB1 _
    (affineW_witnessVector_output 1 _ nd 0 (by omega))

theorem isR1CS_assertion_lessThanSel (P : BigIntParams circomPrime m)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThanSel.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (LessThanSel.circuit P) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_lessThanSel P input hl hr n)

end GadgetCost
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
