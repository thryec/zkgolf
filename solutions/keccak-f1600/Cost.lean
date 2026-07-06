import Challenge.Instances.KeccakF1600.Interface
import Solution.KeccakF1600.Xor5Lane
import Solution.KeccakF1600.ChiLane
import Solution.KeccakF1600.KeccakRound
import Solution.KeccakF1600.MainTheorems
import Challenge.Utils.CostR1CS

namespace Solution.KeccakF1600

open Challenge.Instances.KeccakF1600.Interface
open Challenge.CostR1CS

namespace Cost

/-- All 25 lanes of a symbolic state are affine. -/
def StateAffine (s : Var KeccakBitState (F circomPrime)) : Prop :=
  ∀ j (hj : j < 25), AffineW (s[j]'hj)

/-- All 5 lanes of a symbolic row are affine. -/
def RowAffine (s : Var KeccakBitRow (F circomPrime)) : Prop :=
  ∀ j (hj : j < 5), AffineW (s[j]'hj)

theorem affineW_rotl {x : Var (fields 64) (F circomPrime)} (hx : AffineW x) (k : ℕ) :
    AffineW (rotl k x) := by
  intro i hi
  show Affine ((x.rotate (64 - k % 64))[i])
  rw [Vector.getElem_rotate]
  exact hx _ (Nat.mod_lt _ (by norm_num))

theorem affineW_notBits {x : Var (fields 64) (F circomPrime)} (hx : AffineW x) :
    AffineW (notBits x) := by
  intro i hi
  show Affine ((x.map fun ai => 1 - ai)[i])
  rw [Vector.getElem_map]
  exact Affine.sub (Affine.const 1) (hx i hi)

theorem affineW_xorConst {x : Var (fields 64) (F circomPrime)} (hx : AffineW x) (c : ℕ) :
    AffineW (xorConst c x) := by
  intro i hi
  show Affine ((Vector.ofFn fun (w : Fin 64) => if c.testBit w.val then 1 - x[w] else x[w])[i])
  rw [Vector.getElem_ofFn]
  split
  · exact Affine.sub (Affine.const 1) (hx i hi)
  · exact hx i hi

theorem stateAffine_rhoPiWire {s : Var KeccakBitState (F circomPrime)} (hs : StateAffine s) :
    StateAffine (rhoPiWire s) := by
  intro j hj
  rw [rhoPiWire_getElem s j hj]
  exact affineW_rotl (hs _ (piSource ⟨j, hj⟩).isLt) _

theorem stateAffine_toLanes {bits : Vector (Expression (F circomPrime)) 1600}
    (h : ∀ i (hi : i < 1600), Affine bits[i]) :
    StateAffine (toLanes bits) := by
  intro j hj i hi
  rw [toLanes_getElem bits j hj, Vector.getElem_ofFn]
  exact h _ (by omega)

theorem costIs_sub_xor3Lane (b : Var Xor3Lane.Inputs (F circomPrime)) :
    CostIs (subcircuit Xor3Lane.circuit b) ⟨64, 64⟩ :=
  CostIs.subcircuit (fun n => Xor3Lane.costIs_xor3 b.a b.b b.c n)

theorem costIs_xor5Lane (input : Var Xor5Lane.Inputs (F circomPrime)) :
    CostIs (Xor5Lane.main input) ⟨128, 128⟩ :=
  CostIs.bind (costIs_sub_xor3Lane _) fun _ =>
  costIs_sub_xor3Lane _

theorem costIs_sub_xor5Lane (b : Var Xor5Lane.Inputs (F circomPrime)) :
    CostIs (subcircuit Xor5Lane.circuit b) ⟨128, 128⟩ :=
  CostIs.subcircuit (fun n => costIs_xor5Lane b n)

theorem costIs_chiLane (input : Var ChiLane.Inputs (F circomPrime)) :
    CostIs (ChiLane.main input) ⟨64, 64⟩ :=
  CostIs.bind (CostIs.witnessVector 64 _) fun z =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ => CostIs.pure z

theorem costIs_sub_chiLane (b : Var ChiLane.Inputs (F circomPrime)) :
    CostIs (subcircuit ChiLane.circuit b) ⟨64, 64⟩ :=
  CostIs.subcircuit (fun n => costIs_chiLane b n)

theorem costIs_thetaC (state : Var KeccakBitState (F circomPrime)) :
    CostIs (ThetaC.main state) ⟨640, 640⟩ :=
  CostIs.mapFinRange fun _ n => (costIs_sub_xor5Lane _ : CostIs _ ⟨128, 128⟩) n

theorem costIs_thetaDXor (b : Var ThetaDXor.Inputs (F circomPrime)) :
    CostIs (ThetaDXor.main b) ⟨1600, 1600⟩ := by
  obtain ⟨state, c⟩ := b
  unfold ThetaDXor.main
  exact CostIs.mapFinRange fun i n => costIs_sub_xor3Lane _ n

theorem costIs_sub_thetaC (b : Var KeccakBitState (F circomPrime)) :
    CostIs (subcircuit ThetaC.circuit b) ⟨640, 640⟩ :=
  CostIs.subcircuit (fun n => costIs_thetaC b n)

theorem costIs_sub_thetaDXor (b : Var ThetaDXor.Inputs (F circomPrime)) :
    CostIs (subcircuit ThetaDXor.circuit b) ⟨1600, 1600⟩ :=
  CostIs.subcircuit (fun n => costIs_thetaDXor b n)

theorem costIs_theta (state : Var KeccakBitState (F circomPrime)) :
    CostIs (Theta.main state) ⟨2240, 2240⟩ :=
  CostIs.bind (costIs_sub_thetaC _) fun _ =>
  costIs_sub_thetaDXor _

theorem costIs_sub_theta (b : Var KeccakBitState (F circomPrime)) :
    CostIs (subcircuit Theta.circuit b) ⟨2240, 2240⟩ :=
  CostIs.subcircuit (fun n => costIs_theta b n)

theorem costIs_chi (state : Var KeccakBitState (F circomPrime)) :
    CostIs (Chi.main state) ⟨1600, 1600⟩ :=
  CostIs.mapFinRange fun _ n => (costIs_sub_chiLane _ : CostIs _ ⟨64, 64⟩) n

theorem costIs_sub_chi (b : Var KeccakBitState (F circomPrime)) :
    CostIs (subcircuit Chi.circuit b) ⟨1600, 1600⟩ :=
  CostIs.subcircuit (fun n => costIs_chi b n)

theorem costIs_round (c : ℕ) (state : Var KeccakBitState (F circomPrime)) :
    CostIs (KeccakRound.main c state) ⟨3840, 3840⟩ :=
  CostIs.bind (costIs_sub_theta _) fun _ =>
  CostIs.bind (costIs_sub_chi _) fun _ =>
  CostIs.pure _

theorem costIs_sub_round (c : ℕ) (hc : c < 2^64) (state : Var KeccakBitState (F circomPrime)) :
    CostIs (subcircuit (KeccakRound.circuit c hc) state) ⟨3840, 3840⟩ :=
  CostIs.subcircuit (fun n => costIs_round c state n)

-- Keep the trusted R1CS predicates opaque while *applying* the per-gadget
-- certificates: otherwise the unifier evaluates `r1csProducts` on the 64-bit
-- asserted expressions and loops.
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

theorem affineW_subOut_xor3Lane (b : Var Xor3Lane.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit Xor3Lane.circuit b).output n) := by
  rw [show (subcircuit Xor3Lane.circuit b).output n = varFromOffset (fields 64) n from rfl]
  exact affineW_varFromOffset 64 n

theorem affineW_subOut_xor5Lane (b : Var Xor5Lane.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit Xor5Lane.circuit b).output n) := by
  rw [show (subcircuit Xor5Lane.circuit b).output n = varFromOffset (fields 64) (n + 64) from rfl]
  exact affineW_varFromOffset 64 (n + 64)

theorem affineW_subOut_chiLane (b : Var ChiLane.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit ChiLane.circuit b).output n) := by
  rw [show (subcircuit ChiLane.circuit b).output n = varFromOffset (fields 64) n from rfl]
  exact affineW_varFromOffset 64 n

theorem r1cs_sub_xor3Lane (b : Var Xor3Lane.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c) :
    IsR1CSCirc (subcircuit Xor3Lane.circuit b) :=
  IsR1CSCirc.subcircuit (Xor3Lane.r1cs_xor3 _ _ _ ha hb hc)

theorem r1cs_xor5Lane (input : Var Xor5Lane.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hc : AffineW input.c)
    (hd : AffineW input.d) (he : AffineW input.e) :
    IsR1CSCirc (Xor5Lane.main input) :=
  IsR1CSCirc.bind_out (r1cs_sub_xor3Lane _ ha hb hc) fun _ =>
  r1cs_sub_xor3Lane _ (affineW_subOut_xor3Lane _ _) hd he

theorem r1cs_sub_xor5Lane (b : Var Xor5Lane.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c) (hd : AffineW b.d)
    (he : AffineW b.e) : IsR1CSCirc (subcircuit Xor5Lane.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_xor5Lane _ ha hb hc hd he)

theorem r1cs_chiLane (input : Var ChiLane.Inputs (F circomPrime))
    (ha : AffineW input.a) (hb : AffineW input.b) (hc : AffineW input.c) :
    IsR1CSCirc (ChiLane.main input) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 64 _) fun n =>
    IsR1CSCirc.bind
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_sub_mul
            (Affine.add (Affine.fconst_mul 4 (ha j.val j.isLt))
              (Affine.fconst_mul 2 (hb j.val j.isLt)))
            (Affine.sub
              (Affine.sub
                (Affine.add (affineW_witnessVector_output 64 _ n j.val j.isLt)
                  (Affine.fconst_mul 3 (ha j.val j.isLt)))
                (hb j.val j.isLt))
              (hc j.val j.isLt))
            (Affine.sub
              (Affine.add
                (Affine.add (Affine.fconst_mul 4 (ha j.val j.isLt)) (hb j.val j.isLt))
                (hc j.val j.isLt))
              (Affine.const 3))) m)
      (fun _ => IsR1CSCirc.pure _)

theorem r1cs_sub_chiLane (b : Var ChiLane.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c) :
    IsR1CSCirc (subcircuit ChiLane.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_chiLane _ ha hb hc)

theorem rowAffine_subOut_thetaC (b : Var KeccakBitState (F circomPrime)) (n : ℕ) :
    RowAffine ((subcircuit ThetaC.circuit b).output n) := by
  intro j hj i hi
  rw [show (subcircuit ThetaC.circuit b).output n = ThetaC.circuit.output b n from rfl]
  simp only [ThetaC.circuit, ThetaC.elaborated, circuit_norm]
  exact Affine.var _

theorem stateAffine_subOut_theta (b : Var KeccakBitState (F circomPrime)) (n : ℕ) :
    StateAffine ((subcircuit Theta.circuit b).output n) := by
  intro j hj i hi
  rw [show (subcircuit Theta.circuit b).output n = Theta.circuit.output b n from rfl]
  simp only [Theta.circuit, Theta.elaborated, circuit_norm]
  exact Affine.var _

theorem r1cs_thetaC (state : Var KeccakBitState (F circomPrime)) (hs : StateAffine state) :
    IsR1CSCirc (ThetaC.main state) :=
  IsR1CSCirc.mapFinRange fun x n =>
    (r1cs_sub_xor5Lane _ (hs _ (by omega)) (hs _ (by omega)) (hs _ (by omega))
      (hs _ (by omega)) (hs _ (by omega))) n

theorem r1cs_thetaDXor (b : Var ThetaDXor.Inputs (F circomPrime))
    (hs : StateAffine b.state) (hc : RowAffine b.c) :
    IsR1CSCirc (ThetaDXor.main b) := by
  obtain ⟨state, c⟩ := b
  unfold ThetaDXor.main
  exact IsR1CSCirc.mapFinRange fun i n =>
    (r1cs_sub_xor3Lane _ (hs _ i.isLt) (hc _ (by omega))
      (affineW_rotl (hc _ (by omega)) 1)) n

theorem r1cs_sub_thetaC (b : Var KeccakBitState (F circomPrime)) (hs : StateAffine b) :
    IsR1CSCirc (subcircuit ThetaC.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_thetaC b hs)

theorem r1cs_sub_thetaDXor (b : Var ThetaDXor.Inputs (F circomPrime))
    (hs : StateAffine b.state) (hc : RowAffine b.c) :
    IsR1CSCirc (subcircuit ThetaDXor.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_thetaDXor b hs hc)

theorem r1cs_theta (state : Var KeccakBitState (F circomPrime)) (hs : StateAffine state) :
    IsR1CSCirc (Theta.main state) :=
  IsR1CSCirc.bind_out (r1cs_sub_thetaC state hs) fun n1 =>
  r1cs_sub_thetaDXor _ hs (rowAffine_subOut_thetaC state n1)

theorem r1cs_chi (state : Var KeccakBitState (F circomPrime)) (hs : StateAffine state) :
    IsR1CSCirc (Chi.main state) :=
  IsR1CSCirc.mapFinRange fun j n =>
    (r1cs_sub_chiLane _ (hs _ j.isLt) (hs _ (chiSource1 j).isLt) (hs _ (chiSource2 j).isLt)) n

theorem r1cs_sub_theta (b : Var KeccakBitState (F circomPrime)) (hs : StateAffine b) :
    IsR1CSCirc (subcircuit Theta.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_theta b hs)

theorem r1cs_sub_chi (b : Var KeccakBitState (F circomPrime)) (hs : StateAffine b) :
    IsR1CSCirc (subcircuit Chi.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_chi b hs)

/-- The χ subcircuit output is a fresh witness state, hence affine. -/
theorem stateAffine_subOut_chi (b : Var KeccakBitState (F circomPrime)) (n : ℕ) :
    StateAffine ((subcircuit Chi.circuit b).output n) := by
  intro j hj i hi
  rw [show (subcircuit Chi.circuit b).output n = Chi.circuit.output b n from rfl]
  simp only [Chi.circuit, Chi.elaborated, circuit_norm]
  exact Affine.var _

/-- ι preserves affineness lane by lane (`xorConst` of an affine lane is affine). -/
theorem stateAffine_iotaWire (c : ℕ) {s : Var KeccakBitState (F circomPrime)}
    (hs : StateAffine s) : StateAffine (iotaWire c s) := by
  intro j hj
  rw [show (iotaWire c s)[j] = xorConst (if j = 0 then c else 0) s[j] from by
    rw [iotaWire, Vector.getElem_mapFinRange]]
  exact affineW_xorConst (hs j hj) _

/-- A round output (ι of the χ-output witness state) is affine. -/
theorem stateAffine_subOut_round (c : ℕ) (hc : c < 2^64)
    (b : Var KeccakBitState (F circomPrime)) (n : ℕ) :
    StateAffine ((subcircuit (KeccakRound.circuit c hc) b).output n) := by
  rw [show (subcircuit (KeccakRound.circuit c hc) b).output n
      = (KeccakRound.circuit c hc).output b n from rfl]
  simp only [KeccakRound.circuit, KeccakRound.elaborated, circuit_norm]
  apply stateAffine_iotaWire
  intro j hj i hi
  rw [Vector.getElem_mapFinRange, Vector.getElem_mapRange]
  exact Affine.var _

/-- Flattening an affine lane state to 1600 bits keeps every bit affine. -/
theorem affine_fromLanes {s : Var KeccakBitState (F circomPrime)} (hs : StateAffine s)
    (i : ℕ) (hi : i < 1600) : Affine (fromLanes s)[i] := by
  rw [fromLanes_getElem s i hi]
  exact hs (i / 64) (by omega) (i % 64) (by omega)

theorem r1cs_round (c : ℕ) (state : Var KeccakBitState (F circomPrime)) (hs : StateAffine state) :
    IsR1CSCirc (KeccakRound.main c state) :=
  IsR1CSCirc.bind_out (r1cs_sub_theta state hs) fun n1 =>
  IsR1CSCirc.bind_out
    (r1cs_sub_chi _ (stateAffine_rhoPiWire (stateAffine_subOut_theta state n1))) fun _ =>
  IsR1CSCirc.pure _

theorem r1cs_sub_round (c : ℕ) (hc : c < 2^64) (state : Var KeccakBitState (F circomPrime))
    (hs : StateAffine state) : IsR1CSCirc (subcircuit (KeccakRound.circuit c hc) state) :=
  IsR1CSCirc.subcircuit (r1cs_round c state hs)

end Cost
end Solution.KeccakF1600
