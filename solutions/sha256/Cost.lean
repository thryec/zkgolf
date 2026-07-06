import Challenge.Instances.SHA256.Interface
import Solution.SHA256.And32
import Solution.SHA256.Xor32
import Solution.SHA256.Xor3
import Solution.SHA256.AddMany
import Solution.SHA256.SHA256Rounds
import Solution.SHA256.CompressBlock
import Solution.SHA256.CompressBlockWide
import Solution.SHA256.AddManyWide
import Solution.SHA256.ScheduleStepLast
import Solution.SHA256.Round62Wide
import Solution.SHA256.Round63DMWide
import Solution.SHA256.CompressBlock5
import Solution.SHA256.CompressBlock1
import Solution.SHA256.CheckPad
import Solution.SHA256.SelectDigest
import Solution.SHA256.PaddingTheorems
import Challenge.Utils.CostR1CS

namespace Solution.SHA256

open Challenge.Instances.SHA256.Interface
open Challenge.CostR1CS

namespace Cost

instance hCircomPrimeLarge : Fact (circomPrime > 2^35) := ⟨by
  norm_num [circomPrime]⟩

/-- Each `fields 32` row of a `varFromOffset` over a `ProvableVector (fields 32) n`
is itself a `varFromOffset`, hence affine. -/
theorem affineW_varFromOffset_pvec {n : ℕ} (off j : ℕ) (hj : j < n) :
    AffineW ((varFromOffset (ProvableVector (fields 32) n) off :
      Var (ProvableVector (fields 32) n) (F circomPrime))[j]'hj) := by
  rw [varFromOffset_vector, Vector.getElem_mapRange]
  exact affineW_varFromOffset _ _

theorem affineW_of_flatten_pvec {n : ℕ}
    (input : Var (ProvableVector (fields 32) n) (F circomPrime))
    (hflat : AffineW (input.flatten : fields (n * 32) (Expression (F circomPrime))))
    (j : ℕ) (hj : j < n) : AffineW input[j] := by
  intro i hi
  have hidx : j * 32 + i < n * 32 := by
    have hlt : j * 32 + i < (j + 1) * 32 := by
      rw [Nat.succ_mul]
      exact Nat.add_lt_add_left hi (j * 32)
    exact lt_of_lt_of_le hlt (Nat.mul_le_mul_right 32 (Nat.succ_le_of_lt hj))
  have h := hflat (j * 32 + i) hidx
  rw [Vector.getElem_flatten hidx] at h
  have hdiv : (j * 32 + i) / 32 = j := by
    rw [show j * 32 + i = i + j * 32 by omega]
    rw [Nat.add_mul_div_right i j (by norm_num), Nat.div_eq_of_lt hi, Nat.zero_add]
  have hmod : (j * 32 + i) % 32 = i := by
    rw [show j * 32 + i = i + j * 32 by omega]
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  simpa [hdiv, hmod] using h

theorem affineW_of_affineProvable_pvec {n : ℕ}
    (input : Var (ProvableVector (fields 32) n) (F circomPrime))
    (hinput : AffineProvable input) (j : ℕ) (hj : j < n) :
    AffineW input[j] := by
  have hsz : size (ProvableVector (fields 32) n) = n * 32 := rfl
  have hflat : AffineW (input.flatten : fields (n * 32) (Expression (F circomPrime))) := by
    intro i hi
    simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz] using hinput i (by simpa [hsz] using hi)
  exact affineW_of_flatten_pvec input hflat j hj

theorem affineProvable_pvec_of_affineW {n : ℕ}
    (input : Var (ProvableVector (fields 32) n) (F circomPrime))
    (h : ∀ j (hj : j < n), AffineW input[j]) :
    AffineProvable input := by
  intro i hi
  have hsz : size (ProvableVector (fields 32) n) = n * 32 := rfl
  have hi' : i < n * 32 := by simpa [hsz] using hi
  have hdiv : i / 32 < n := by
    exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hi')
  have hmod : i % 32 < 32 := Nat.mod_lt _ (by norm_num)
  simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz] using h (i / 32) hdiv (i % 32) hmod

def and32Cost : Count := ⟨32, 32⟩
def xor32Cost : Count := ⟨32, 32⟩
def add32Cost : Count := ⟨32, 33⟩
def addManyCost : Count := ⟨34, 35⟩
def addMany2cCost : Count := ⟨33, 34⟩
def ch32Cost : Count := ⟨32, 32⟩
def maj32Cost : Count := ⟨32, 32⟩
def sigmaCost : Count := ⟨32, 32⟩

def scheduleStepCost : Count := ⟨91, 92⟩

def messageScheduleCost : Count :=
  ⟨48 * scheduleStepCost.allocations, 48 * scheduleStepCost.constraints⟩

def sha256RoundCost : Count :=
  ⟨2 * sigmaCost.allocations + ch32Cost.allocations + maj32Cost.allocations +
      addManyCost.allocations + addMany2cCost.allocations,
   2 * sigmaCost.constraints + ch32Cost.constraints + maj32Cost.constraints +
      addManyCost.constraints + addMany2cCost.constraints⟩

def sha256Rounds63Cost : Count :=
  ⟨63 * sha256RoundCost.allocations, 63 * sha256RoundCost.constraints⟩

/-- The cross-round packed `Maj` gadget: one witnessed 32-bit column pinned by two
CLASS-A rows per lane, `(32, 64)`. -/
def packedMajCost : Count := ⟨32, 64⟩

/-- The cross-round paired gadget (two rounds fused): 4 σ + `PackedMaj` (32,64) +
4 witnessVector 32-bit columns + 4 `BoolVec32` (0,32) + `PackedCh` (32,32) +
`FusedEAdder` (5,6) + `FusedAAdder` (3,4). -/
def sha256RoundPairCost : Count :=
  ⟨2 * sigmaCost.allocations + 2 * sigmaCost.allocations + packedMajCost.allocations +
      4 * 32 + 4 * 0 + ch32Cost.allocations + (5 + 3),
   2 * sigmaCost.constraints + 2 * sigmaCost.constraints + packedMajCost.constraints +
      4 * 0 + 4 * 32 + ch32Cost.constraints + (6 + 4)⟩

/-- The 62-round loop realised as 31 paired steps (cross-round packing). -/
def sha256Rounds62_pairedCost : Count :=
  ⟨31 * sha256RoundPairCost.allocations, 31 * sha256RoundPairCost.constraints⟩

/-- The first 63 rounds via `circuit63_paired`: 31 cross-round pairs (rounds 0..61)
followed by one plain round (round 62). -/
def sha256Rounds63_pairedCost : Count :=
  ⟨sha256Rounds62_pairedCost.allocations + sha256RoundCost.allocations,
   sha256Rounds62_pairedCost.constraints + sha256RoundCost.constraints⟩

/-- The fused compression: 63 generic rounds, then round 63 fused with the
Davies-Meyer feedforward — 2 σ + Ch + Maj as usual, two widened `AddMany`s
(n = 8 for word 0, n = 7 for word 4; `addManyCost` is the same `⟨34, 35⟩` for
any `n ≤ 8`) replacing round 63's `new_a`/`new_e` adders AND the word-0/word-4
`Add32`s, plus 6 plain `Add32`s for the pass-through Davies-Meyer words. -/
def sha256RoundsCost : Count :=
  ⟨sha256Rounds63_pairedCost.allocations + 2 * sigmaCost.allocations + ch32Cost.allocations +
      maj32Cost.allocations + 2 * addManyCost.allocations + 6 * add32Cost.allocations,
   sha256Rounds63_pairedCost.constraints + 2 * sigmaCost.constraints + ch32Cost.constraints +
      maj32Cost.constraints + 2 * addManyCost.constraints + 6 * add32Cost.constraints⟩

def compressBlockCost : Count :=
  ⟨messageScheduleCost.allocations + sha256RoundsCost.allocations,
   messageScheduleCost.constraints + sha256RoundsCost.constraints⟩

def compressBlock5Cost : Count :=
  ⟨sha256RoundsCost.allocations, sha256RoundsCost.constraints⟩

def selectDigestCost : Count := ⟨8, 40⟩

/-! ## Per-gadget offset-independent costs (`CostIs`)

Each `costIs_*` lemma computes the exact `operationCount` of a gadget at *every*
offset, by structural recursion over the gadget's own `do`-block. Higher-level
gadgets reuse the lower ones through `CostIs.subcircuit`. The final `*Cost_proof`
theorems instantiate these at offset `0`, without native evaluation or `decide`. -/

theorem costIs_and32 (a b : Var (fields 32) (F circomPrime)) :
    CostIs (And32.and32 a b) ⟨32, 32⟩ :=
  CostIs.bind (CostIs.witnessVector 32 _) fun z =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ => CostIs.pure z

theorem costIs_xor32 (a b : Var (fields 32) (F circomPrime)) :
    CostIs (Xor32.xor32 a b) ⟨32, 32⟩ :=
  CostIs.bind (CostIs.witnessVector 32 _) fun z =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ => CostIs.pure z

theorem costIs_ch32 (e f g : Var (fields 32) (F circomPrime)) :
    CostIs (Ch32.ch32 e f g) ⟨32, 32⟩ :=
  CostIs.bind (CostIs.witnessVector 32 _) fun z =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ => CostIs.pure z

theorem costIs_add32 (a b : Var (fields 32) (F circomPrime)) :
    CostIs (Add32.add32 a b) add32Cost :=
  CostIs.bind (CostIs.witnessVector 32 _) fun z =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
      CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure z

theorem costIs_maj32 (a b c : Var (fields 32) (F circomPrime)) :
    CostIs (Maj32.maj32 a b c) maj32Cost :=
  CostIs.bind (CostIs.witnessVector 32 _) fun z =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ => CostIs.pure z

theorem costIs_sub_xor32 (b : Var Xor32.Inputs (F circomPrime)) :
    CostIs (subcircuit Xor32.circuit b) ⟨32, 32⟩ :=
  CostIs.subcircuit (costIs_xor32 _ _)

theorem costIs_sub_xor3 (b : Var Xor3.Inputs (F circomPrime)) :
    CostIs (subcircuit Xor3.circuit b) ⟨32, 32⟩ :=
  CostIs.subcircuit (Xor3.costIs_xor3 _ _ _)

theorem costIs_lowerSigma0 (x : Var (fields 32) (F circomPrime)) :
    CostIs (LowerSigma0.lowerSigma0 x) ⟨32, 32⟩ :=
  costIs_sub_xor3 _

theorem costIs_lowerSigma1 (x : Var (fields 32) (F circomPrime)) :
    CostIs (LowerSigma1.lowerSigma1 x) ⟨32, 32⟩ :=
  costIs_sub_xor3 _

theorem costIs_upperSigma0 (x : Var (fields 32) (F circomPrime)) :
    CostIs (UpperSigma0.upperSigma0 x) ⟨32, 32⟩ :=
  costIs_sub_xor3 _

theorem costIs_upperSigma1 (x : Var (fields 32) (F circomPrime)) :
    CostIs (UpperSigma1.upperSigma1 x) ⟨32, 32⟩ :=
  costIs_sub_xor3 _

/-- Per-gadget subcircuit-cost wrappers. Each isolates the (single) `circuit.main`
unfolding into its own elaboration, so composite chains never accumulate the
defeq work of many subcircuit invocations into one heartbeat budget. -/
theorem costIs_sub_add32 (b : Var Add32.Inputs (F circomPrime)) :
    CostIs (subcircuit Add32.circuit b) add32Cost :=
  CostIs.subcircuit (costIs_add32 _ _)

theorem costIs_sub_ch32 (b : Var Ch32.Inputs (F circomPrime)) :
    CostIs (subcircuit Ch32.circuit b) ch32Cost :=
  CostIs.subcircuit (costIs_ch32 _ _ _)

theorem costIs_sub_maj32 (b : Var Maj32.Inputs (F circomPrime)) :
    CostIs (subcircuit Maj32.circuit b) maj32Cost :=
  CostIs.subcircuit (costIs_maj32 _ _ _)

theorem costIs_sub_upperSigma0 (b : Var (fields 32) (F circomPrime)) :
    CostIs (subcircuit UpperSigma0.circuit b) sigmaCost :=
  CostIs.subcircuit (costIs_upperSigma0 _)

theorem costIs_sub_upperSigma1 (b : Var (fields 32) (F circomPrime)) :
    CostIs (subcircuit UpperSigma1.circuit b) sigmaCost :=
  CostIs.subcircuit (costIs_upperSigma1 _)

theorem costIs_sub_lowerSigma0 (b : Var (fields 32) (F circomPrime)) :
    CostIs (subcircuit LowerSigma0.circuit b) sigmaCost :=
  CostIs.subcircuit (costIs_lowerSigma0 _)

theorem costIs_sub_lowerSigma1 (b : Var (fields 32) (F circomPrime)) :
    CostIs (subcircuit LowerSigma1.circuit b) sigmaCost :=
  CostIs.subcircuit (costIs_lowerSigma1 _)

theorem costIs_sub_addMany {n : ℕ} (hn : 2 ≤ n ∧ n ≤ 8)
    (b : Var (AddMany.Inputs n) (F circomPrime)) :
    CostIs (subcircuit (AddMany.circuit hn) b) addManyCost :=
  CostIs.subcircuit (AddMany.costIs_addMany hn _)

theorem costIs_sub_addMany2c {n : ℕ} (hn : n ≤ 4)
    (b : Var (AddMany.Inputs n) (F circomPrime)) :
    CostIs (subcircuit (AddMany.circuit2c hn) b) addMany2cCost :=
  CostIs.subcircuit (AddMany.costIs_addMany2c hn _)

theorem costIs_sub_addMany2 {n : ℕ} (hn : n ≤ 4)
    (b : Var (AddMany.Inputs n) (F circomPrime)) :
    CostIs (subcircuit (AddMany.circuit2 hn) b) addMany2cCost :=
  CostIs.subcircuit (AddMany.costIs_addMany2 hn _)

theorem costIs_sha256Round (state : Vector (Var (fields 32) (F circomPrime)) 8)
    (k w : Var (fields 32) (F circomPrime)) :
    CostIs (SHA256Round.sha256Round state k w) sha256RoundCost :=
  CostIs.bind (costIs_sub_upperSigma1 _) fun _ =>
  CostIs.bind (costIs_sub_ch32 _) fun _ =>
  CostIs.bind (costIs_sub_upperSigma0 _) fun _ =>
  CostIs.bind (costIs_sub_maj32 _) fun _ =>
  CostIs.bind (costIs_sub_addMany (n := 6) (by norm_num) _) fun _ =>
  CostIs.bind (costIs_sub_addMany2c (n := 4) (by norm_num) _) fun _ => CostIs.pure _

set_option maxHeartbeats 1600000 in
theorem costIs_scheduleStep (input : Var ScheduleStep.Inputs (F circomPrime)) :
    CostIs (ScheduleStep.main input) scheduleStepCost :=
  CostIs.bind (CostIs.witnessVector 29 _) fun _ =>
  CostIs.bind (CostIs.witnessVector 22 _) fun _ =>
  CostIs.bind (CostIs.witnessVector 6 _) fun _ =>
  CostIs.bind (CostIs.witnessField _) fun _ =>
  CostIs.bind (CostIs.witnessVector 32 _) fun _ =>
  CostIs.bind (CostIs.witnessField _) fun _ =>
  CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem costIs_sub_scheduleStep (b : Var ScheduleStep.Inputs (F circomPrime)) :
    CostIs (subcircuit ScheduleStep.circuit b) scheduleStepCost :=
  CostIs.subcircuit (costIs_scheduleStep _)

theorem costIs_messageSchedule (block : SHA256Block (Expression (F circomPrime))) :
    CostIs (MessageSchedule.main block) messageScheduleCost :=
  CostIs.foldlRange (constant := MessageSchedule.constantLength) (fun _ _ n =>
    (CostIs.bind (costIs_sub_scheduleStep _) fun _ => CostIs.pure _) n)

theorem costIs_sub_sha256Round (b : Var SHA256Round.Inputs (F circomPrime)) :
    CostIs (subcircuit SHA256Round.circuit b) sha256RoundCost :=
  CostIs.subcircuit (costIs_sha256Round _ _ _)

theorem costIs_sha256Rounds63 (input : Var SHA256Rounds63.Inputs (F circomPrime)) :
    CostIs (SHA256Rounds63.main input) sha256Rounds63Cost :=
  CostIs.foldlRange (fun _ _ n => costIs_sub_sha256Round _ n)

theorem costIs_sub_sha256Rounds63 (b : Var SHA256Rounds63.Inputs (F circomPrime)) :
    CostIs (subcircuit SHA256Rounds63.circuit b) sha256Rounds63Cost :=
  CostIs.subcircuit (costIs_sha256Rounds63 _)

/-! ### Cross-round paired gadget cost -/

theorem costIs_boolVec32 (v : Var (fields 32) (F circomPrime)) :
    CostIs (BoolVec32.main v) ⟨0, 32⟩ := by
  unfold BoolVec32.main
  exact CostIs.forEach fun _ => CostIs.assertZero _

theorem costIs_sub_boolVec32 (v : Var (fields 32) (F circomPrime)) :
    CostIs (assertion BoolVec32.circuit v) ⟨0, 32⟩ :=
  CostIs.assertion (costIs_boolVec32 _)

theorem costIs_packedCh (input : Var PackedCh.Inputs (F circomPrime)) :
    CostIs (PackedCh.main input) ⟨32, 32⟩ := by
  unfold PackedCh.main PackedCh.packedCh
  exact CostIs.bind (CostIs.witnessVector 32 _) fun _ =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ => CostIs.pure _

theorem costIs_sub_packedCh (input : Var PackedCh.Inputs (F circomPrime)) :
    CostIs (subcircuit PackedCh.circuit input) ⟨32, 32⟩ :=
  CostIs.subcircuit (costIs_packedCh _)

theorem costIs_packedMaj (input : Var PackedMaj.Inputs (F circomPrime)) :
    CostIs (PackedMaj.main input) ⟨32, 64⟩ := by
  unfold PackedMaj.main PackedMaj.packedMaj
  exact CostIs.bind (CostIs.witnessVector 32 _) fun _ =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ => CostIs.pure _

theorem costIs_sub_packedMaj (input : Var PackedMaj.Inputs (F circomPrime)) :
    CostIs (subcircuit PackedMaj.circuit input) ⟨32, 64⟩ :=
  CostIs.subcircuit (costIs_packedMaj _)

theorem costIs_fusedEAdder (input : Var FusedEAdder.Inputs (F circomPrime)) :
    CostIs (FusedEAdder.main input) ⟨5, 6⟩ := by
  unfold FusedEAdder.main
  exact
    CostIs.bind (CostIs.witnessVector 2 _) fun _ =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.witnessVector 3 _) fun _ =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem costIs_sub_fusedEAdder (input : Var FusedEAdder.Inputs (F circomPrime)) :
    CostIs (assertion FusedEAdder.circuit input) ⟨5, 6⟩ :=
  CostIs.assertion (costIs_fusedEAdder _)

theorem costIs_fusedAAdder (input : Var FusedAAdder.Inputs (F circomPrime)) :
    CostIs (FusedAAdder.main input) ⟨3, 4⟩ := by
  unfold FusedAAdder.main
  exact
    CostIs.bind (CostIs.witnessVector 1 _) fun _ =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.witnessVector 2 _) fun _ =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
    CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

theorem costIs_sub_fusedAAdder (input : Var FusedAAdder.Inputs (F circomPrime)) :
    CostIs (assertion FusedAAdder.circuit input) ⟨3, 4⟩ :=
  CostIs.assertion (costIs_fusedAAdder _)

set_option maxHeartbeats 1600000 in
theorem costIs_sha256RoundPair (input : Var SHA256RoundPair.Inputs (F circomPrime)) :
    CostIs (SHA256RoundPair.main input) sha256RoundPairCost := by
  unfold SHA256RoundPair.main
  exact
    CostIs.bind (costIs_sub_upperSigma1 _) fun _ =>
    CostIs.bind (costIs_sub_upperSigma0 _) fun _ =>
    CostIs.bind (CostIs.witnessVector 32 _) fun _ =>
    CostIs.bind (CostIs.witnessVector 32 _) fun _ =>
    CostIs.bind (costIs_sub_boolVec32 _) fun _ =>
    CostIs.bind (costIs_sub_boolVec32 _) fun _ =>
    CostIs.bind (costIs_sub_upperSigma1 _) fun _ =>
    CostIs.bind (costIs_sub_upperSigma0 _) fun _ =>
    CostIs.bind (CostIs.witnessVector 32 _) fun _ =>
    CostIs.bind (CostIs.witnessVector 32 _) fun _ =>
    CostIs.bind (costIs_sub_boolVec32 _) fun _ =>
    CostIs.bind (costIs_sub_boolVec32 _) fun _ =>
    CostIs.bind (costIs_sub_packedCh _) fun _ =>
    CostIs.bind (costIs_sub_packedMaj _) fun _ =>
    CostIs.bind (costIs_sub_fusedEAdder _) fun _ =>
    CostIs.bind (costIs_sub_fusedAAdder _) fun _ => CostIs.pure _

theorem costIs_sub_sha256RoundPair (b : Var SHA256RoundPair.Inputs (F circomPrime)) :
    CostIs (subcircuit SHA256RoundPair.circuit b) sha256RoundPairCost :=
  CostIs.subcircuit (costIs_sha256RoundPair _)

theorem costIs_sha256Rounds62_paired (input : Var SHA256Rounds63.Inputs (F circomPrime)) :
    CostIs (SHA256Rounds63.main62_paired input) sha256Rounds62_pairedCost :=
  CostIs.foldlRange (fun _ _ n => costIs_sub_sha256RoundPair _ n)

theorem costIs_sub_sha256Rounds62_paired (b : Var SHA256Rounds63.Inputs (F circomPrime)) :
    CostIs (subcircuit SHA256Rounds63.circuit62_paired b) sha256Rounds62_pairedCost :=
  CostIs.subcircuit (costIs_sha256Rounds62_paired _)

theorem costIs_main63_paired (input : Var SHA256Rounds63.Inputs (F circomPrime)) :
    CostIs (SHA256Rounds63.main63_paired input) sha256Rounds63_pairedCost :=
  CostIs.bind (costIs_sub_sha256Rounds62_paired _) fun _ =>
    costIs_sub_sha256Round _

theorem costIs_sub_circuit63_paired (b : Var SHA256Rounds63.Inputs (F circomPrime)) :
    CostIs (subcircuit SHA256Rounds63.circuit63_paired b) sha256Rounds63_pairedCost :=
  CostIs.subcircuit (costIs_main63_paired _)

theorem costIs_sha256Rounds (input : Var SHA256Rounds.Inputs (F circomPrime)) :
    CostIs (SHA256Rounds.main input) sha256RoundsCost :=
  CostIs.bind (costIs_sub_circuit63_paired _) fun _ =>
  CostIs.bind (costIs_sub_upperSigma1 _) fun _ =>
  CostIs.bind (costIs_sub_ch32 _) fun _ =>
  CostIs.bind (costIs_sub_upperSigma0 _) fun _ =>
  CostIs.bind (costIs_sub_maj32 _) fun _ =>
  CostIs.bind (costIs_sub_addMany (n := 8) (by norm_num) _) fun _ =>
  CostIs.bind (costIs_sub_addMany (n := 7) (by norm_num) _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ => CostIs.pure _

theorem costIs_sub_messageSchedule (b : Var SHA256Block (F circomPrime)) :
    CostIs (subcircuit MessageSchedule.circuit b) messageScheduleCost :=
  CostIs.subcircuit (costIs_messageSchedule _)

theorem costIs_sub_sha256Rounds (b : Var SHA256Rounds.Inputs (F circomPrime)) :
    CostIs (subcircuit SHA256Rounds.circuit b) sha256RoundsCost :=
  CostIs.subcircuit (costIs_sha256Rounds _)

theorem costIs_compressBlock (input : Var CompressBlock.Inputs (F circomPrime)) :
    CostIs (CompressBlock.main input) compressBlockCost :=
  CostIs.bind (costIs_sub_messageSchedule _) fun _ =>
    costIs_sub_sha256Rounds _

theorem costIs_compressBlock5 (input : Var CompressBlock5.Inputs (F circomPrime)) :
    CostIs (CompressBlock5.main input) compressBlock5Cost :=
  costIs_sub_sha256Rounds _

theorem and32Cost_proof :
    circuitCount (And32.main (varFromOffset And32.Inputs 0 : Var And32.Inputs (F circomPrime))) =
      and32Cost :=
  costIs_and32 _ _ 0

theorem xor32Cost_proof :
    circuitCount (Xor32.main (varFromOffset Xor32.Inputs 0 : Var Xor32.Inputs (F circomPrime))) =
      xor32Cost :=
  costIs_xor32 _ _ 0

theorem add32Cost_proof :
    circuitCount (Add32.main (varFromOffset Add32.Inputs 0 : Var Add32.Inputs (F circomPrime))) =
      add32Cost :=
  costIs_add32 _ _ 0

theorem ch32Cost_proof :
    circuitCount (Ch32.main (varFromOffset Ch32.Inputs 0 : Var Ch32.Inputs (F circomPrime))) =
      ch32Cost :=
  costIs_ch32 _ _ _ 0

theorem maj32Cost_proof :
    circuitCount (Maj32.main (varFromOffset Maj32.Inputs 0 : Var Maj32.Inputs (F circomPrime))) =
      maj32Cost :=
  costIs_maj32 _ _ _ 0

theorem lowerSigma0Cost_proof :
    circuitCount (LowerSigma0.main (varFromOffset (fields 32) 0 : Var (fields 32) (F circomPrime))) =
      sigmaCost :=
  costIs_lowerSigma0 _ 0

theorem lowerSigma1Cost_proof :
    circuitCount (LowerSigma1.main (varFromOffset (fields 32) 0 : Var (fields 32) (F circomPrime))) =
      sigmaCost :=
  costIs_lowerSigma1 _ 0

theorem upperSigma0Cost_proof :
    circuitCount (UpperSigma0.main (varFromOffset (fields 32) 0 : Var (fields 32) (F circomPrime))) =
      sigmaCost :=
  costIs_upperSigma0 _ 0

theorem upperSigma1Cost_proof :
    circuitCount (UpperSigma1.main (varFromOffset (fields 32) 0 : Var (fields 32) (F circomPrime))) =
      sigmaCost :=
  costIs_upperSigma1 _ 0

theorem messageScheduleCost_proof :
    circuitCount (MessageSchedule.main
      (varFromOffset SHA256Block 0 : Var SHA256Block (F circomPrime))) =
      messageScheduleCost :=
  costIs_messageSchedule _ 0

theorem sha256RoundCost_proof :
    circuitCount (SHA256Round.main
      (varFromOffset SHA256Round.Inputs 0 : Var SHA256Round.Inputs (F circomPrime))) =
      sha256RoundCost :=
  costIs_sha256Round _ _ _ 0

theorem sha256RoundsCost_proof :
    circuitCount (SHA256Rounds.main
      (varFromOffset SHA256Rounds.Inputs 0 : Var SHA256Rounds.Inputs (F circomPrime))) =
      sha256RoundsCost :=
  costIs_sha256Rounds _ 0

theorem compressBlockCost_proof :
    circuitCount (CompressBlock.main
      (varFromOffset CompressBlock.Inputs 0 : Var CompressBlock.Inputs (F circomPrime))) =
      compressBlockCost :=
  costIs_compressBlock _ 0

theorem compressBlock5Cost_proof :
    circuitCount (CompressBlock5.main
      (varFromOffset CompressBlock5.Inputs 0 : Var CompressBlock5.Inputs (F circomPrime))) =
      compressBlock5Cost :=
  costIs_compressBlock5 _ 0

/-! ## Per-gadget R1CS certificates (`IsR1CSCirc`)

`r1cs_*` lemmas certify, structurally, that every asserted expression of a gadget
is a single R1CS row, given that the gadget's input vectors are affine (`AffineW`,
i.e. each entry has structural degree ≤ 1 — true for all variable/constant atoms).
The witnessed outputs are `varFromOffset` vectors, hence affine, so the property
propagates through composition, without native evaluation. -/

-- The trusted R1CS predicates are now `Prop`-valued `def`s (matching on
-- `r1csProducts` / the operation list). Left reducible, the unifier tries to
-- *evaluate* them on the asserted expressions when matching the single-row
-- lemmas / `assertZero` / `forEach` against a goal, which loops on neutral
-- subterms like `a[i]`. We only ever *apply* these certificates (never compute
-- the predicates), so keep them opaque for the R1CS proofs below.
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

/-- `A*B - C` with all of `A, B, C` affine is a single R1CS row. -/
theorem isR1CSRow_mul_sub {A B C : Expression (F circomPrime)}
    (hA : Affine A) (hB : Affine B) (hC : Affine C) : isR1CSRow (A * B - C) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · exact isR1CSRow_of_r1csProducts (k := 0)
      (by show r1csProducts (A * B + -C) = some 0
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_of_affine hC, h]) (by omega)
  · exact isR1CSRow_of_r1csProducts (k := 1)
      (by show r1csProducts (A * B + -C) = some 1
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_of_affine hC, h]) (by omega)

theorem affineW_rotr32 {x : Var (fields 32) (F circomPrime)} {k : Fin 32} (hx : AffineW x) :
    AffineW (rotr32 k x) := by
  intro i hi
  show Affine ((x.rotate k.val)[i])
  rw [Vector.getElem_rotate hi]
  exact hx _ _

theorem affineW_shr32 {x : Var (fields 32) (F circomPrime)} {k : Fin 32} (hx : AffineW x) :
    AffineW (shr32 k x) := by
  intro i hi
  show Affine ((shr32 k x)[i])
  rw [shr32, Vector.getElem_ofFn]
  split
  · exact hx _ _
  · exact Affine.zero

theorem affine_fieldFromBitsExpr {m : ℕ} (v : Var (fields m) (F circomPrime)) (h : AffineW v) :
    Affine (Utils.Bits.fieldFromBitsExpr v) := by
  unfold Utils.Bits.fieldFromBitsExpr
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    exact Affine.add hacc (Affine.mul_fconst _ (h i.val i.isLt))

/-- The output of `xor32` is its witness vector, hence affine. Stated via `circuit_norm`
so the offset reasoning stays cheap (avoids whnf-reducing the whole bind). -/
theorem affineW_xor32_output (a b : Var (fields 32) (F circomPrime)) (n : ℕ) :
    AffineW ((Xor32.xor32 a b).output n) := by
  have h : (Xor32.xor32 a b).output n = varFromOffset (fields 32) n := by
    simp only [Xor32.xor32, circuit_norm]
  rw [h]; exact affineW_varFromOffset _ _

theorem affineW_and32_output (a b : Var (fields 32) (F circomPrime)) (n : ℕ) :
    AffineW ((And32.and32 a b).output n) := by
  have h : (And32.and32 a b).output n = varFromOffset (fields 32) n := by
    simp only [And32.and32, circuit_norm]
  rw [h]; exact affineW_varFromOffset _ _

theorem affineW_add32_output (a b : Var (fields 32) (F circomPrime)) (n : ℕ) :
    AffineW ((Add32.add32 a b).output n) := by
  have h : (Add32.add32 a b).output n = varFromOffset (fields 32) n := by
    simp only [Add32.add32, circuit_norm]
  rw [h]; exact affineW_varFromOffset _ _

theorem affineW_ch32_output (e f g : Var (fields 32) (F circomPrime)) (n : ℕ) :
    AffineW ((Ch32.ch32 e f g).output n) := by
  have h : (Ch32.ch32 e f g).output n = varFromOffset (fields 32) n := by
    simp only [Ch32.ch32, circuit_norm]
  rw [h]; exact affineW_varFromOffset _ _

theorem affineW_maj32_output (a b c : Var (fields 32) (F circomPrime)) (n : ℕ) :
    AffineW ((Maj32.maj32 a b c).output n) := by
  have h : (Maj32.maj32 a b c).output n = varFromOffset (fields 32) n := by
    simp only [Maj32.maj32, circuit_norm]
  rw [h]; exact affineW_varFromOffset _ _

theorem r1cs_and32 (a b : Var (fields 32) (F circomPrime)) (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (And32.and32 a b) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun n =>
    IsR1CSCirc.bind
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_sub_mul (affineW_witnessVector_output 32 _ n j.val j.isLt)
            (ha j.val j.isLt) (hb j.val j.isLt)) m)
      (fun _ => IsR1CSCirc.pure _)

theorem and32_isR1CS : isR1CS (F := F circomPrime) And32.main :=
  isR1CS_of_IsR1CSCirc
  (fun (input : Var And32.Inputs (F circomPrime)) hinput =>
    let hflat : AffineW (input.a ++ input.b : fields 64 (Expression (F circomPrime))) := by
      intro i hi
      have hsz : size And32.Inputs = 64 := rfl
      simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz] using hinput i (by omega)
    r1cs_and32 input.a input.b (AffineW.left_of_append hflat) (AffineW.right_of_append hflat))
  (fun input _ n => (affineW_and32_output input.a input.b n).affineProvable)

theorem r1cs_xor32 (a b : Var (fields 32) (F circomPrime)) (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (Xor32.xor32 a b) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun n =>
    IsR1CSCirc.bind
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_add_mul
            (Affine.sub (Affine.sub (affineW_witnessVector_output 32 _ n j.val j.isLt)
              (ha j.val j.isLt)) (hb j.val j.isLt))
            (Affine.fconst_mul _ (ha j.val j.isLt)) (hb j.val j.isLt)) m)
      (fun _ => IsR1CSCirc.pure _)

theorem xor32_isR1CS : isR1CS (F := F circomPrime) Xor32.main :=
  isR1CS_of_IsR1CSCirc
  (fun (input : Var Xor32.Inputs (F circomPrime)) hinput =>
    let hflat : AffineW (input.a ++ input.b : fields 64 (Expression (F circomPrime))) := by
      intro i hi
      have hsz : size Xor32.Inputs = 64 := rfl
      simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz] using hinput i (by omega)
    r1cs_xor32 input.a input.b (AffineW.left_of_append hflat) (AffineW.right_of_append hflat))
  (fun input _ n => (affineW_xor32_output input.a input.b n).affineProvable)

theorem r1cs_add32 (a b : Var (fields 32) (F circomPrime)) (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (Add32.add32 a b) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun n =>
  IsR1CSCirc.bind
    (IsR1CSCirc.forEach fun j m =>
      IsR1CSCirc.assertZero
        (isR1CSRow_mul (affineW_witnessVector_output 32 _ n j.val j.isLt)
          (Affine.sub (affineW_witnessVector_output 32 _ n j.val j.isLt) (Affine.const 1))) m)
    fun _ =>
  let carryAffine :=
    Affine.fconst_mul _
      (Affine.sub
        (Affine.add (affine_fieldFromBitsExpr a ha) (affine_fieldFromBitsExpr b hb))
        (affine_fieldFromBitsExpr _ (affineW_witnessVector_output 32 _ n)))
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_mul carryAffine (Affine.sub carryAffine (Affine.const 1))))
    fun _ => IsR1CSCirc.pure _

theorem add32_isR1CS : isR1CS (F := F circomPrime) Add32.main :=
  isR1CS_of_IsR1CSCirc
  (fun (input : Var Add32.Inputs (F circomPrime)) hinput =>
    let hflat : AffineW (input.a ++ input.b : fields 64 (Expression (F circomPrime))) := by
      intro i hi
      have hsz : size Add32.Inputs = 64 := rfl
      simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz] using hinput i (by omega)
    r1cs_add32 input.a input.b (AffineW.left_of_append hflat) (AffineW.right_of_append hflat))
  (fun input _ n => (affineW_add32_output input.a input.b n).affineProvable)

theorem r1cs_ch32 (e f g : Var (fields 32) (F circomPrime))
    (he : AffineW e) (hf : AffineW f) (hg : AffineW g) :
    IsR1CSCirc (Ch32.ch32 e f g) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun n =>
    IsR1CSCirc.bind
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_sub_mul
            (Affine.sub (affineW_witnessVector_output 32 _ n j.val j.isLt) (hg j.val j.isLt))
            (he j.val j.isLt)
            (Affine.sub (hf j.val j.isLt) (hg j.val j.isLt))) m)
      (fun _ => IsR1CSCirc.pure _)

theorem ch32_isR1CS : isR1CS (F := F circomPrime) Ch32.main :=
  isR1CS_of_IsR1CSCirc
  (fun (input : Var Ch32.Inputs (F circomPrime)) hinput =>
    let hflat : AffineW (input.e ++ (input.f ++ input.g) :
        fields 96 (Expression (F circomPrime))) := by
      intro i hi
      have hsz : size Ch32.Inputs = 96 := rfl
      simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz] using hinput i (by omega)
    let htail : AffineW (input.f ++ input.g : fields 64 (Expression (F circomPrime))) :=
      AffineW.right_of_append hflat
    r1cs_ch32 input.e input.f input.g
      (AffineW.left_of_append hflat) (AffineW.left_of_append htail) (AffineW.right_of_append htail))
  (fun input _ n => (affineW_ch32_output input.e input.f input.g n).affineProvable)

theorem r1cs_maj32 (a b c : Var (fields 32) (F circomPrime))
    (ha : AffineW a) (hb : AffineW b) (hc : AffineW c) :
    IsR1CSCirc (Maj32.maj32 a b c) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun n =>
    IsR1CSCirc.bind
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_add_mul (Affine.const 12)
            (Affine.add (Affine.sub (Affine.add
              (Affine.add (affineW_witnessVector_output 32 _ n j.val j.isLt)
                (ha j.val j.isLt)) (hb j.val j.isLt))
              (Affine.fconst_mul _ (hc j.val j.isLt))) (Affine.const 3))
            (Affine.sub (Affine.add (Affine.add (ha j.val j.isLt) (hb j.val j.isLt))
              (Affine.fconst_mul _ (hc j.val j.isLt))) (Affine.const 4))) m)
      fun _ => IsR1CSCirc.pure _

theorem maj32_isR1CS : isR1CS (F := F circomPrime) Maj32.main :=
  isR1CS_of_IsR1CSCirc
  (fun (input : Var Maj32.Inputs (F circomPrime)) hinput =>
    let hflat : AffineW (input.a ++ (input.b ++ input.c) :
        fields 96 (Expression (F circomPrime))) := by
      intro i hi
      have hsz : size Maj32.Inputs = 96 := rfl
      simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz] using hinput i (by omega)
    let htail : AffineW (input.b ++ input.c : fields 64 (Expression (F circomPrime))) :=
      AffineW.right_of_append hflat
    r1cs_maj32 input.a input.b input.c
      (AffineW.left_of_append hflat) (AffineW.left_of_append htail) (AffineW.right_of_append htail))
  (fun input _ n => (affineW_maj32_output input.a input.b input.c n).affineProvable)

/-- Output of a `subcircuit Xor32.circuit` is its witness row, hence affine. -/
theorem affineW_subOut_xor32 (b : Var Xor32.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit Xor32.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, Xor32.circuit, Xor32.elaborated]; exact Affine.var _

theorem r1cs_sub_xor32 (b : Var Xor32.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) : IsR1CSCirc (subcircuit Xor32.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_xor32 _ _ ha hb)

theorem r1cs_sub_xor3 (b : Var Xor3.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c) :
    IsR1CSCirc (subcircuit Xor3.circuit b) :=
  IsR1CSCirc.subcircuit (Xor3.r1cs_xor3 _ _ _ ha hb hc)

theorem r1cs_lowerSigma0 (x : Var (fields 32) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (LowerSigma0.lowerSigma0 x) :=
  r1cs_sub_xor3 _ (affineW_rotr32 hx) (affineW_rotr32 hx) (affineW_shr32 hx)

theorem lowerSigma0_isR1CS : isR1CS (F := F circomPrime) LowerSigma0.main :=
  isR1CS_of_IsR1CSCirc
    (fun input hinput => r1cs_lowerSigma0 input hinput.affineW)
    (fun input _ n => by
      apply AffineW.affineProvable
      intro i hi
      simp only [LowerSigma0.main, LowerSigma0.lowerSigma0, circuit_norm, Xor3.circuit,
        Xor3.elaborated]
      exact Affine.var _)

theorem r1cs_lowerSigma1 (x : Var (fields 32) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (LowerSigma1.lowerSigma1 x) :=
  r1cs_sub_xor3 _ (affineW_rotr32 hx) (affineW_rotr32 hx) (affineW_shr32 hx)

theorem lowerSigma1_isR1CS : isR1CS (F := F circomPrime) LowerSigma1.main :=
  isR1CS_of_IsR1CSCirc
    (fun input hinput => r1cs_lowerSigma1 input hinput.affineW)
    (fun input _ n => by
      apply AffineW.affineProvable
      intro i hi
      simp only [LowerSigma1.main, LowerSigma1.lowerSigma1, circuit_norm, Xor3.circuit,
        Xor3.elaborated]
      exact Affine.var _)

theorem r1cs_upperSigma0 (x : Var (fields 32) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (UpperSigma0.upperSigma0 x) :=
  r1cs_sub_xor3 _ (affineW_rotr32 hx) (affineW_rotr32 hx) (affineW_rotr32 hx)

theorem upperSigma0_isR1CS : isR1CS (F := F circomPrime) UpperSigma0.main :=
  isR1CS_of_IsR1CSCirc
    (fun input hinput => r1cs_upperSigma0 input hinput.affineW)
    (fun input _ n => by
      apply AffineW.affineProvable
      intro i hi
      simp only [UpperSigma0.main, UpperSigma0.upperSigma0, circuit_norm, Xor3.circuit,
        Xor3.elaborated]
      exact Affine.var _)

theorem r1cs_upperSigma1 (x : Var (fields 32) (F circomPrime)) (hx : AffineW x) :
    IsR1CSCirc (UpperSigma1.upperSigma1 x) :=
  r1cs_sub_xor3 _ (affineW_rotr32 hx) (affineW_rotr32 hx) (affineW_rotr32 hx)

theorem upperSigma1_isR1CS : isR1CS (F := F circomPrime) UpperSigma1.main :=
  isR1CS_of_IsR1CSCirc
    (fun input hinput => r1cs_upperSigma1 input hinput.affineW)
    (fun input _ n => by
      apply AffineW.affineProvable
      intro i hi
      simp only [UpperSigma1.main, UpperSigma1.upperSigma1, circuit_norm, Xor3.circuit,
        Xor3.elaborated]
      exact Affine.var _)

/-! ### Affineness of constants, witness rows and subcircuit outputs -/

theorem affineW_constWord32 (m : ℕ) :
    AffineW (constWord32 m : Var (fields 32) (F circomPrime)) := by
  intro j hj; rw [constWord32, Vector.getElem_ofFn]; exact Affine.const _

theorem affineW_mapRange_var (f : ℕ → ℕ) :
    AffineW (Vector.mapRange 32 (fun i => Expression.var ⟨f i⟩) : Var (fields 32) (F circomPrime)) := by
  intro j hj; rw [Vector.getElem_mapRange]; exact Affine.var _

theorem affineW_subOut_add32 (b : Var Add32.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit Add32.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, Add32.circuit, Add32.elaborated]; exact Affine.var _

theorem affineW_subOut_ch32 (b : Var Ch32.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit Ch32.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, Ch32.circuit, Ch32.elaborated]; exact Affine.var _

theorem affineW_subOut_maj32 (b : Var Maj32.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit Maj32.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, Maj32.circuit, Maj32.elaborated]; exact Affine.var _

theorem affineW_subOut_upperSigma0 (b : Var (fields 32) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit UpperSigma0.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, UpperSigma0.circuit, UpperSigma0.elaborated]
  exact Affine.var _

theorem affineW_subOut_upperSigma1 (b : Var (fields 32) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit UpperSigma1.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, UpperSigma1.circuit, UpperSigma1.elaborated]
  exact Affine.var _

theorem affineW_subOut_lowerSigma0 (b : Var (fields 32) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit LowerSigma0.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, LowerSigma0.circuit, LowerSigma0.elaborated]
  exact Affine.var _

theorem affineW_subOut_lowerSigma1 (b : Var (fields 32) (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit LowerSigma1.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, LowerSigma1.circuit, LowerSigma1.elaborated]
  exact Affine.var _

theorem affineW_subOut_addMany {n : ℕ} (hn : 2 ≤ n ∧ n ≤ 8)
    (b : Var (AddMany.Inputs n) (F circomPrime)) (off : ℕ) :
    AffineW ((subcircuit (AddMany.circuit hn) b).output off) := by
  intro i hi
  simp only [circuit_norm, subcircuit, AddMany.circuit, AddMany.elaborated]
  exact Affine.var _

theorem affineW_subOut_addMany2c {n : ℕ} (hn : n ≤ 4)
    (b : Var (AddMany.Inputs n) (F circomPrime)) (off : ℕ) :
    AffineW ((subcircuit (AddMany.circuit2c hn) b).output off) := by
  intro i hi
  simp only [circuit_norm, subcircuit, AddMany.circuit2c, AddMany.elaborated2c]
  exact Affine.var _

theorem affineW_subOut_addMany2 {n : ℕ} (hn : n ≤ 4)
    (b : Var (AddMany.Inputs n) (F circomPrime)) (off : ℕ) :
    AffineW ((subcircuit (AddMany.circuit2 hn) b).output off) := by
  intro i hi
  simp only [circuit_norm, subcircuit, AddMany.circuit2, AddMany.elaborated2]
  exact Affine.var _

/-- The bit-complement of an affine word is affine (each entry is `1 − xᵢ`). -/
theorem affineW_not32 {x : Var (fields 32) (F circomPrime)} (hx : AffineW x) :
    AffineW (not32 x) := by
  intro i hi
  rw [not32, Vector.getElem_map]
  exact Affine.sub (Affine.const 1) (hx i hi)

/-! ### Subcircuit R1CS wrappers (each isolates one `circuit.main` defeq) -/

theorem r1cs_sub_add32 (b : Var Add32.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) : IsR1CSCirc (subcircuit Add32.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_add32 _ _ ha hb)

theorem r1cs_sub_ch32 (b : Var Ch32.Inputs (F circomPrime))
    (he : AffineW b.e) (hf : AffineW b.f) (hg : AffineW b.g) :
    IsR1CSCirc (subcircuit Ch32.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_ch32 _ _ _ he hf hg)

theorem r1cs_sub_maj32 (b : Var Maj32.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c) :
    IsR1CSCirc (subcircuit Maj32.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_maj32 _ _ _ ha hb hc)

theorem r1cs_sub_upperSigma0 (b : Var (fields 32) (F circomPrime)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit UpperSigma0.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_upperSigma0 _ hb)

theorem r1cs_sub_upperSigma1 (b : Var (fields 32) (F circomPrime)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit UpperSigma1.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_upperSigma1 _ hb)

theorem r1cs_sub_lowerSigma0 (b : Var (fields 32) (F circomPrime)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit LowerSigma0.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_lowerSigma0 _ hb)

theorem r1cs_sub_lowerSigma1 (b : Var (fields 32) (F circomPrime)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit LowerSigma1.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_lowerSigma1 _ hb)

theorem r1cs_sub_addMany {n : ℕ} (hn : 2 ≤ n ∧ n ≤ 8)
    (b : Var (AddMany.Inputs n) (F circomPrime))
    (hxs : ∀ k : Fin n, AffineW b[k]) :
    IsR1CSCirc (subcircuit (AddMany.circuit hn) b) :=
  IsR1CSCirc.subcircuit (AddMany.r1cs_addMany hn b hxs)

theorem r1cs_sub_addMany2c {n : ℕ} (hn : n ≤ 4)
    (b : Var (AddMany.Inputs n) (F circomPrime))
    (hxs : ∀ k : Fin n, AffineW b[k]) :
    IsR1CSCirc (subcircuit (AddMany.circuit2c hn) b) :=
  IsR1CSCirc.subcircuit (AddMany.r1cs_addMany2c hn b hxs)

theorem r1cs_sub_addMany2 {n : ℕ} (hn : n ≤ 4)
    (b : Var (AddMany.Inputs n) (F circomPrime))
    (hxs : ∀ k : Fin n, AffineW b[k]) :
    IsR1CSCirc (subcircuit (AddMany.circuit2 hn) b) :=
  IsR1CSCirc.subcircuit (AddMany.r1cs_addMany2 hn b hxs)

theorem affineW_vec6 {a0 a1 a2 a3 a4 a5 : Var (fields 32) (F circomPrime)}
    (h0 : AffineW a0) (h1 : AffineW a1) (h2 : AffineW a2) (h3 : AffineW a3)
    (h4 : AffineW a4) (h5 : AffineW a5) :
    ∀ k : Fin 6, AffineW ((#v[a0, a1, a2, a3, a4, a5] :
      Var (ProvableVector (fields 32) 6) (F circomPrime))[k]) := by
  intro k
  fin_cases k
  exacts [h0, h1, h2, h3, h4, h5]

theorem affineW_vec4 {a0 a1 a2 a3 : Var (fields 32) (F circomPrime)}
    (h0 : AffineW a0) (h1 : AffineW a1) (h2 : AffineW a2) (h3 : AffineW a3) :
    ∀ k : Fin 4, AffineW ((#v[a0, a1, a2, a3] :
      Var (ProvableVector (fields 32) 4) (F circomPrime))[k]) := by
  intro k
  fin_cases k
  exacts [h0, h1, h2, h3]

theorem r1cs_sha256Round (state : Vector (Var (fields 32) (F circomPrime)) 8)
    (k w : Var (fields 32) (F circomPrime))
    (hstate : ∀ i (hi : i < 8), AffineW state[i]) (hk : AffineW k) (hw : AffineW w) :
    IsR1CSCirc (SHA256Round.sha256Round state k w) :=
  IsR1CSCirc.bind_out (r1cs_sub_upperSigma1 _ (hstate 4 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_ch32 _ (hstate 4 (by omega)) (hstate 5 (by omega)) (hstate 6 (by omega))) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_upperSigma0 _ (hstate 0 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_maj32 _ (hstate 0 (by omega)) (hstate 1 (by omega)) (hstate 2 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_addMany (n := 6) (by norm_num) _
      (affineW_vec6 (hstate 3 (by omega)) (hstate 7 (by omega))
        (affineW_subOut_upperSigma1 _ _) (affineW_subOut_ch32 _ _) hk hw)) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_addMany2c (n := 4) (by norm_num) _
      (affineW_vec4 (affineW_subOut_addMany (by norm_num) _ _)
        (affineW_subOut_upperSigma0 _ _) (affineW_subOut_maj32 _ _)
        (affineW_not32 (hstate 3 (by omega))))) fun _ =>
  IsR1CSCirc.pure _

/-- The 8 output words of a `SHA256Round` are affine when the input state is.
Each word's `circuit_norm` reduction is a separate declaration so it gets its own
heartbeat budget (reducing all eight at once is too expensive). -/
theorem affineW_sha256Round_out_w0 (input : Var SHA256Round.Inputs (F circomPrime)) (n : ℕ) :
    AffineW (((subcircuit SHA256Round.circuit input).output n)[0]) := by
  simp only [circuit_norm, subcircuit, SHA256Round.circuit, SHA256Round.elaborated]
  exact affineW_mapRange_var _

theorem affineW_sha256Round_out_w4 (input : Var SHA256Round.Inputs (F circomPrime)) (n : ℕ) :
    AffineW (((subcircuit SHA256Round.circuit input).output n)[4]) := by
  simp only [circuit_norm, subcircuit, SHA256Round.circuit, SHA256Round.elaborated]
  exact affineW_mapRange_var _

theorem affineW_sha256Round_out_w1 (input : Var SHA256Round.Inputs (F circomPrime)) (n : ℕ)
    (h : AffineW input.state[0]) :
    AffineW (((subcircuit SHA256Round.circuit input).output n)[1]) := by
  simp only [circuit_norm, subcircuit, SHA256Round.circuit, SHA256Round.elaborated]; exact h

theorem affineW_sha256Round_out_w2 (input : Var SHA256Round.Inputs (F circomPrime)) (n : ℕ)
    (h : AffineW input.state[1]) :
    AffineW (((subcircuit SHA256Round.circuit input).output n)[2]) := by
  simp only [circuit_norm, subcircuit, SHA256Round.circuit, SHA256Round.elaborated]; exact h

theorem affineW_sha256Round_out_w3 (input : Var SHA256Round.Inputs (F circomPrime)) (n : ℕ)
    (h : AffineW input.state[2]) :
    AffineW (((subcircuit SHA256Round.circuit input).output n)[3]) := by
  simp only [circuit_norm, subcircuit, SHA256Round.circuit, SHA256Round.elaborated]; exact h

theorem affineW_sha256Round_out_w5 (input : Var SHA256Round.Inputs (F circomPrime)) (n : ℕ)
    (h : AffineW input.state[4]) :
    AffineW (((subcircuit SHA256Round.circuit input).output n)[5]) := by
  simp only [circuit_norm, subcircuit, SHA256Round.circuit, SHA256Round.elaborated]; exact h

theorem affineW_sha256Round_out_w6 (input : Var SHA256Round.Inputs (F circomPrime)) (n : ℕ)
    (h : AffineW input.state[5]) :
    AffineW (((subcircuit SHA256Round.circuit input).output n)[6]) := by
  simp only [circuit_norm, subcircuit, SHA256Round.circuit, SHA256Round.elaborated]; exact h

theorem affineW_sha256Round_out_w7 (input : Var SHA256Round.Inputs (F circomPrime)) (n : ℕ)
    (h : AffineW input.state[6]) :
    AffineW (((subcircuit SHA256Round.circuit input).output n)[7]) := by
  simp only [circuit_norm, subcircuit, SHA256Round.circuit, SHA256Round.elaborated]; exact h

theorem affineW_sha256Round_output (input : Var SHA256Round.Inputs (F circomPrime)) (n : ℕ)
    (hstate : ∀ j (hj : j < 8), AffineW input.state[j]) :
    ∀ j (hj : j < 8), AffineW (((subcircuit SHA256Round.circuit input).output n)[j]) := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact affineW_sha256Round_out_w0 _ _
  · exact affineW_sha256Round_out_w1 _ _ (hstate 0 (by omega))
  · exact affineW_sha256Round_out_w2 _ _ (hstate 1 (by omega))
  · exact affineW_sha256Round_out_w3 _ _ (hstate 2 (by omega))
  · exact affineW_sha256Round_out_w4 _ _
  · exact affineW_sha256Round_out_w5 _ _ (hstate 4 (by omega))
  · exact affineW_sha256Round_out_w6 _ _ (hstate 5 (by omega))
  · exact affineW_sha256Round_out_w7 _ _ (hstate 6 (by omega))

theorem r1cs_sha256Rounds63 (input : Var SHA256Rounds63.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW input.state[j])
    (hsched : ∀ k (hk : k < 64), AffineW input.schedule[k]) :
    IsR1CSCirc (SHA256Rounds63.main input) := by
  refine IsR1CSCirc.foldlRange_inv (fun s => ∀ j (hj : j < 8), AffineW s[j]) hstate ?_ ?_
  · intro s i hs
    exact IsR1CSCirc.subcircuit
      (r1cs_sha256Round _ _ _ hs (affineW_constWord32 _) (hsched _ (by have := i.isLt; omega)))
  · intro s i n hs
    exact affineW_sha256Round_output _ n hs

theorem r1cs_sub_sha256Rounds63 (b : Var SHA256Rounds63.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW b.state[j])
    (hsched : ∀ k (hk : k < 64), AffineW b.schedule[k]) :
    IsR1CSCirc (subcircuit SHA256Rounds63.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_sha256Rounds63 _ hstate hsched)

theorem affineW_tVec (s0 : Var (fields 29) (F circomPrime)) (s1 : Var (fields 22) (F circomPrime))
    (u : Var (fields 6) (F circomPrime)) (v : Expression (F circomPrime))
    (hs0 : AffineW s0) (hs1 : AffineW s1) (hu : AffineW u) (hv : Affine v) :
    AffineW (SigmaSum.tVec s0 s1 u v) := by
  intro j hj
  by_cases h22 : j < 22
  · rw [SigmaSum.tVec_get_low s0 s1 u v j h22]
    exact Affine.add (hs0 _ (by omega)) (hs1 _ h22)
  · rcases (by omega : j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29
        ∨ j = 30 ∨ j = 31) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [SigmaSum.tVec_get_22]; exact Affine.add (hs0 _ (by norm_num)) (hu _ (by norm_num))
    · rw [SigmaSum.tVec_get_23]; exact Affine.add (hs0 _ (by norm_num)) (hu _ (by norm_num))
    · rw [SigmaSum.tVec_get_24]; exact hs0 _ (by norm_num)
    · rw [SigmaSum.tVec_get_25]; exact hs0 _ (by norm_num)
    · rw [SigmaSum.tVec_get_26]; exact Affine.add (hs0 _ (by norm_num)) (hu _ (by norm_num))
    · rw [SigmaSum.tVec_get_27]; exact Affine.add (hs0 _ (by norm_num)) (hu _ (by norm_num))
    · rw [SigmaSum.tVec_get_28]; exact hs0 _ (by norm_num)
    · rw [SigmaSum.tVec_get_29]; exact hv
    · rw [SigmaSum.tVec_get_30]; exact hu _ (by norm_num)
    · rw [SigmaSum.tVec_get_31]; exact hu _ (by norm_num)

set_option maxHeartbeats 1600000 in
theorem r1cs_scheduleStep (input : Var ScheduleStep.Inputs (F circomPrime))
    (h2 : AffineW input.wm2) (h7 : AffineW input.wm7)
    (h15 : AffineW input.wm15) (h16 : AffineW input.wm16) :
    IsR1CSCirc (ScheduleStep.main input) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 29 _) fun ns0 =>
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 22 _) fun ns1 =>
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 6 _) fun nu =>
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun nv =>
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun nz =>
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun nc =>
  -- σ₀ 3-input rows
  IsR1CSCirc.bind
    (IsR1CSCirc.forEach fun j m =>
      IsR1CSCirc.assertZero
        (isR1CSRow_sub_mul
          (Affine.sub (Affine.add
              (Affine.fconst_mul _ (affineW_rotr32 h15 j.val (by omega)))
              (Affine.fconst_mul _ (affineW_rotr32 h15 j.val (by omega))))
            (Affine.fconst_mul _ (h15 (j.val + 3) (by omega))))
          (Affine.add (Affine.add
            (Affine.add (affineW_witnessVector_output 29 _ ns0 j.val (by omega))
              (Affine.fconst_mul _ (affineW_rotr32 h15 j.val (by omega))))
            (Affine.fconst_mul _ (affineW_rotr32 h15 j.val (by omega))))
            (Affine.fconst_mul _ (h15 (j.val + 3) (by omega))))
          (Affine.add (Affine.sub (Affine.add (affineW_rotr32 h15 j.val (by omega))
            (affineW_rotr32 h15 j.val (by omega)))
            (Affine.fconst_mul _ (h15 (j.val + 3) (by omega)))) (Affine.const 1))) m)
    fun _ =>
  -- σ₁ 3-input rows
  IsR1CSCirc.bind
    (IsR1CSCirc.forEach fun j m =>
      IsR1CSCirc.assertZero
        (isR1CSRow_sub_mul
          (Affine.sub (Affine.add
              (Affine.fconst_mul _ (affineW_rotr32 h2 j.val (by omega)))
              (Affine.fconst_mul _ (affineW_rotr32 h2 j.val (by omega))))
            (Affine.fconst_mul _ (h2 (j.val + 10) (by omega))))
          (Affine.add (Affine.add
            (Affine.add (affineW_witnessVector_output 22 _ ns1 j.val (by omega))
              (Affine.fconst_mul _ (affineW_rotr32 h2 j.val (by omega))))
            (Affine.fconst_mul _ (affineW_rotr32 h2 j.val (by omega))))
            (Affine.fconst_mul _ (h2 (j.val + 10) (by omega))))
          (Affine.add (Affine.sub (Affine.add (affineW_rotr32 h2 j.val (by omega))
            (affineW_rotr32 h2 j.val (by omega)))
            (Affine.fconst_mul _ (h2 (j.val + 10) (by omega)))) (Affine.const 1))) m)
    fun _ =>
  -- pair rows (weight 4)
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_sub_mul
        (Affine.sub (Affine.sub (Affine.add
            (Affine.sub (Affine.fconst_mul _ (affineW_rotr32 h2 22 (by norm_num)))
              (Affine.fconst_mul _ (affineW_rotr32 h2 22 (by norm_num))))
            (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 24 (by norm_num))
              (affineW_rotr32 h2 24 (by norm_num)))))
          (Affine.const 1)) (affineW_witnessVector_output 6 _ nu 0 (by norm_num)))
        (Affine.sub (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 24 (by norm_num))
            (affineW_rotr32 h2 24 (by norm_num))))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 22 (by norm_num)))
            (affineW_rotr32 h2 22 (by norm_num))))
        (Affine.add (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 24 (by norm_num))
            (affineW_rotr32 h2 24 (by norm_num))))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 22 (by norm_num)))
            (affineW_rotr32 h2 22 (by norm_num))))))
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_sub_mul
        (Affine.sub (Affine.sub (Affine.add
            (Affine.sub (Affine.fconst_mul _ (affineW_rotr32 h2 23 (by norm_num)))
              (Affine.fconst_mul _ (affineW_rotr32 h2 23 (by norm_num))))
            (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 25 (by norm_num))
              (affineW_rotr32 h2 25 (by norm_num)))))
          (Affine.const 1)) (affineW_witnessVector_output 6 _ nu 1 (by norm_num)))
        (Affine.sub (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 25 (by norm_num))
            (affineW_rotr32 h2 25 (by norm_num))))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 23 (by norm_num)))
            (affineW_rotr32 h2 23 (by norm_num))))
        (Affine.add (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 25 (by norm_num))
            (affineW_rotr32 h2 25 (by norm_num))))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 23 (by norm_num)))
            (affineW_rotr32 h2 23 (by norm_num))))))
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_sub_mul
        (Affine.sub (Affine.sub (Affine.add
            (Affine.sub (Affine.fconst_mul _ (affineW_rotr32 h2 26 (by norm_num)))
              (Affine.fconst_mul _ (affineW_rotr32 h2 26 (by norm_num))))
            (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 28 (by norm_num))
              (affineW_rotr32 h2 28 (by norm_num)))))
          (Affine.const 1)) (affineW_witnessVector_output 6 _ nu 2 (by norm_num)))
        (Affine.sub (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 28 (by norm_num))
            (affineW_rotr32 h2 28 (by norm_num))))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 26 (by norm_num)))
            (affineW_rotr32 h2 26 (by norm_num))))
        (Affine.add (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 28 (by norm_num))
            (affineW_rotr32 h2 28 (by norm_num))))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 26 (by norm_num)))
            (affineW_rotr32 h2 26 (by norm_num))))))
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_sub_mul
        (Affine.sub (Affine.sub (Affine.add
            (Affine.sub (Affine.fconst_mul _ (affineW_rotr32 h2 27 (by norm_num)))
              (Affine.fconst_mul _ (affineW_rotr32 h2 27 (by norm_num))))
            (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 29 (by norm_num))
              (affineW_rotr32 h2 29 (by norm_num)))))
          (Affine.const 1)) (affineW_witnessVector_output 6 _ nu 3 (by norm_num)))
        (Affine.sub (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 29 (by norm_num))
            (affineW_rotr32 h2 29 (by norm_num))))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 27 (by norm_num)))
            (affineW_rotr32 h2 27 (by norm_num))))
        (Affine.add (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 29 (by norm_num))
            (affineW_rotr32 h2 29 (by norm_num))))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 27 (by norm_num)))
            (affineW_rotr32 h2 27 (by norm_num))))))
    fun _ =>
  -- pair rows (weight 1, σ₁ paired with σ₀)
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_sub_mul
        (Affine.sub (Affine.sub (Affine.add
            (Affine.sub (Affine.fconst_mul _ (affineW_rotr32 h2 30 (by norm_num)))
              (Affine.fconst_mul _ (affineW_rotr32 h2 30 (by norm_num))))
            (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h15 30 (by norm_num))
              (affineW_rotr32 h15 30 (by norm_num)))))
          (Affine.const 1)) (affineW_witnessVector_output 6 _ nu 4 (by norm_num)))
        (Affine.sub (Affine.add (affineW_rotr32 h15 30 (by norm_num))
            (affineW_rotr32 h15 30 (by norm_num)))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 30 (by norm_num)))
            (affineW_rotr32 h2 30 (by norm_num))))
        (Affine.add (Affine.add (affineW_rotr32 h15 30 (by norm_num))
            (affineW_rotr32 h15 30 (by norm_num)))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 30 (by norm_num)))
            (affineW_rotr32 h2 30 (by norm_num))))))
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_sub_mul
        (Affine.sub (Affine.sub (Affine.add
            (Affine.sub (Affine.fconst_mul _ (affineW_rotr32 h2 31 (by norm_num)))
              (Affine.fconst_mul _ (affineW_rotr32 h2 31 (by norm_num))))
            (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h15 31 (by norm_num))
              (affineW_rotr32 h15 31 (by norm_num)))))
          (Affine.const 1)) (affineW_witnessVector_output 6 _ nu 5 (by norm_num)))
        (Affine.sub (Affine.add (affineW_rotr32 h15 31 (by norm_num))
            (affineW_rotr32 h15 31 (by norm_num)))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 31 (by norm_num)))
            (affineW_rotr32 h2 31 (by norm_num))))
        (Affine.add (Affine.add (affineW_rotr32 h15 31 (by norm_num))
            (affineW_rotr32 h15 31 (by norm_num)))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 31 (by norm_num)))
            (affineW_rotr32 h2 31 (by norm_num))))))
    fun _ =>
  -- lone σ₀ lane 29: determined 2-input row
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_add_mul
        (Affine.sub (Affine.sub (affine_witnessField_output _ nv)
          (affineW_rotr32 h15 29 (by norm_num))) (affineW_rotr32 h15 29 (by norm_num)))
        (Affine.fconst_mul _ (affineW_rotr32 h15 29 (by norm_num)))
        (affineW_rotr32 h15 29 (by norm_num))))
    fun _ =>
  -- output-bit booleanity
  IsR1CSCirc.bind
    (IsR1CSCirc.forEach fun j m =>
      IsR1CSCirc.assertZero
        (isR1CSRow_mul (affineW_witnessVector_output 32 _ nz j.val j.isLt)
          (Affine.sub (affineW_witnessVector_output 32 _ nz j.val j.isLt) (Affine.const 1))) m)
    fun _ =>
  -- high-carry booleanity
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_mul (affine_witnessField_output _ nc)
        (Affine.sub (affine_witnessField_output _ nc) (Affine.const 1))))
    fun _ =>
  -- fused affine low-carry booleanity row
  let he0 :=
    Affine.sub
      (Affine.fconst_mul ((2^32 : F circomPrime)⁻¹) (Affine.sub
        (Affine.add (Affine.add
          (affine_fieldFromBitsExpr _ h7)
          (affine_fieldFromBitsExpr _ h16))
          (affine_fieldFromBitsExpr _
            (affineW_tVec _ _ _ _ (affineW_witnessVector_output 29 _ ns0)
              (affineW_witnessVector_output 22 _ ns1) (affineW_witnessVector_output 6 _ nu)
              (affine_witnessField_output _ nv))))
        (affine_fieldFromBitsExpr _ (affineW_witnessVector_output 32 _ nz))))
      (Affine.fconst_mul 2 (affine_witnessField_output _ nc))
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero (isR1CSRow_mul he0 (Affine.sub he0 (Affine.const 1))))
    fun _ => IsR1CSCirc.pure _

theorem affineW_subOut_scheduleStep (b : Var ScheduleStep.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit ScheduleStep.circuit b).output n) := by
  intro i hi; simp only [circuit_norm, subcircuit, ScheduleStep.circuit, ScheduleStep.elaborated]
  exact Affine.var _

theorem r1cs_sub_scheduleStep (b : Var ScheduleStep.Inputs (F circomPrime))
    (h2 : AffineW b.wm2) (h7 : AffineW b.wm7) (h15 : AffineW b.wm15) (h16 : AffineW b.wm16) :
    IsR1CSCirc (subcircuit ScheduleStep.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_scheduleStep b h2 h7 h15 h16)

theorem r1cs_messageSchedule (block : SHA256Block (Expression (F circomPrime)))
    (hblock : ∀ k (hk : k < 16), AffineW block[k]) : IsR1CSCirc (MessageSchedule.main block) := by
  refine IsR1CSCirc.foldlRange_inv (constant := MessageSchedule.constantLength)
    (fun w => ∀ k (hk : k < 64), AffineW w[k]) ?_ ?_ ?_
  · intro k hk
    show AffineW ((block ++ Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F circomPrime))))[k])
    rw [Vector.getElem_append]
    split
    · exact hblock _ _
    · rw [Vector.getElem_replicate]
      intro j hj
      rw [Vector.getElem_replicate]
      exact Affine.zero (F := F circomPrime)
  · intro w i hw
    exact IsR1CSCirc.bind_out
      (r1cs_sub_scheduleStep _ (hw _ (by omega)) (hw _ (by omega)) (hw _ (by omega)) (hw _ (by omega)))
      (fun _ => IsR1CSCirc.pure _)
  · intro w i n hw k hk
    simp only [circuit_norm, Vector.getElem_set]
    split
    · exact affineW_varFromOffset _ _
    · exact hw _ _

/-- Every word of `stateVar` is affine when the input state is (recursion over
rounds; each word is either a fresh witness row or a pass-through). -/
theorem affineW_stateVar (i₀ : ℕ) (s : Var SHA256State (F circomPrime))
    (hs : ∀ j (hj : j < 8), AffineW s[j]) :
    ∀ (m j : ℕ) (hj : j < 8), AffineW ((SHA256Rounds.stateVar i₀ s m)[j]) := by
  intro m
  induction m with
  | zero => intro j hj; exact hs j hj
  | succ p ih =>
      intro j hj
      rw [SHA256Rounds.stateVar]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact affineW_mapRange_var _
      · exact ih 0 (by omega)
      · exact ih 1 (by omega)
      · exact ih 2 (by omega)
      · exact affineW_mapRange_var _
      · exact ih 4 (by omega)
      · exact ih 5 (by omega)
      · exact ih 6 (by omega)

/-- The 63-round subcircuit's output is `stateVar n b.state 63`; every word is affine. -/
theorem affineW_subOut_sha256Rounds63 (b : Var SHA256Rounds63.Inputs (F circomPrime)) (n : ℕ)
    (hb : ∀ j (hj : j < 8), AffineW b.state[j]) :
    ∀ j (hj : j < 8), AffineW (((subcircuit SHA256Rounds63.circuit b).output n)[j]) := by
  intro j hj
  have heq : (subcircuit SHA256Rounds63.circuit b).output n = SHA256Rounds.stateVar n b.state 63 := by
    simp only [circuit_norm, subcircuit, SHA256Rounds63.circuit, SHA256Rounds63.elaborated]
  rw [heq]; exact affineW_stateVar n b.state hb 63 j hj

/-- Package per-element affineness of a concrete 8-word input vector (for the
fused word-0 Davies-Meyer `AddMany`). -/
theorem affineW_vec8 {a0 a1 a2 a3 a4 a5 a6 a7 : Var (fields 32) (F circomPrime)}
    (h0 : AffineW a0) (h1 : AffineW a1) (h2 : AffineW a2) (h3 : AffineW a3)
    (h4 : AffineW a4) (h5 : AffineW a5) (h6 : AffineW a6) (h7 : AffineW a7) :
    ∀ k : Fin 8, AffineW ((#v[a0, a1, a2, a3, a4, a5, a6, a7] :
      Var (ProvableVector (fields 32) 8) (F circomPrime))[k]) := by
  intro k
  fin_cases k
  exacts [h0, h1, h2, h3, h4, h5, h6, h7]

/-- Package per-element affineness of a concrete 7-word input vector (for the
fused word-4 Davies-Meyer `AddMany`). -/
theorem affineW_vec7 {a0 a1 a2 a3 a4 a5 a6 : Var (fields 32) (F circomPrime)}
    (h0 : AffineW a0) (h1 : AffineW a1) (h2 : AffineW a2) (h3 : AffineW a3)
    (h4 : AffineW a4) (h5 : AffineW a5) (h6 : AffineW a6) :
    ∀ k : Fin 7, AffineW ((#v[a0, a1, a2, a3, a4, a5, a6] :
      Var (ProvableVector (fields 32) 7) (F circomPrime))[k]) := by
  intro k
  fin_cases k
  exacts [h0, h1, h2, h3, h4, h5, h6]

/-! ### Cross-round paired gadget R1CS certificates -/

local notation "λE" => (((2^40 : F circomPrime) : Expression (F circomPrime)))

/-- A degree-0 factor times an affine factor is affine. -/
theorem affine_deg0_mul (a : Expression (F circomPrime)) {b : Expression (F circomPrime)}
    (ha : degree a = 0) (hb : Affine b) : Affine (a * b) := by
  show degree (a * b) ≤ 1
  rw [degree_mul, ha, Nat.zero_add]; exact hb

/-- The 3-bit carry recomposition `carryE` is affine. -/
theorem affine_carryE (c : Var (fields 3) (F circomPrime)) (hc : AffineW c) :
    Affine (RPShared.carryE c) := by
  unfold RPShared.carryE
  exact Affine.add (Affine.add (hc 0 (by norm_num))
    (Affine.fconst_mul _ (hc 1 (by norm_num)))) (Affine.fconst_mul _ (hc 2 (by norm_num)))

/-- The 2-bit carry recomposition `carryE2` is affine. -/
theorem affine_carryE2 (c : Var (fields 2) (F circomPrime)) (hc : AffineW c) :
    Affine (RPShared.carryE2 c) := by
  unfold RPShared.carryE2
  exact Affine.add (hc 0 (by norm_num)) (Affine.fconst_mul _ (hc 1 (by norm_num)))

/-- `A*B + C` with all of `A, B, C` affine is a single R1CS row. -/
theorem isR1CSRow_mul_add {A B C : Expression (F circomPrime)}
    (hA : Affine A) (hB : Affine B) (hC : Affine C) : isR1CSRow (A * B + C) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · exact isR1CSRow_of_r1csProducts (k := 0)
      (by rw [r1csProducts_add, h, r1csProducts_of_affine hC]) (by omega)
  · exact isR1CSRow_of_r1csProducts (k := 1)
      (by rw [r1csProducts_add, h, r1csProducts_of_affine hC]) (by omega)

theorem r1cs_boolVec32 (v : Var (fields 32) (F circomPrime)) (hv : AffineW v) :
    IsR1CSCirc (BoolVec32.main v) := by
  unfold BoolVec32.main
  exact IsR1CSCirc.forEach fun j m =>
    IsR1CSCirc.assertZero
      (isR1CSRow_mul (hv j.val j.isLt) (Affine.sub (hv j.val j.isLt) (Affine.const 1))) m

theorem r1cs_sub_boolVec32 (v : Var (fields 32) (F circomPrime)) (hv : AffineW v) :
    IsR1CSCirc (assertion BoolVec32.circuit v) :=
  IsR1CSCirc.assertion (fun n => r1cs_boolVec32 v hv n)

set_option maxHeartbeats 800000 in
theorem r1cs_packedCh (e f g u : Var (fields 32) (F circomPrime))
    (he : AffineW e) (hf : AffineW f) (hg : AffineW g) (hu : AffineW u) :
    IsR1CSCirc (PackedCh.packedCh e f g u) := by
  unfold PackedCh.packedCh
  exact
    IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun n =>
    IsR1CSCirc.bind
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_mul_add
            (Affine.add (Affine.add (Affine.add
              (affine_deg0_mul (-3) (by rfl) (he j.val j.isLt))
              (affine_deg0_mul 2 (by rfl) (hf j.val j.isLt)))
              (affine_deg0_mul 4 (by rfl) (hg j.val j.isLt)))
              (affine_deg0_mul (2 * λE) (by rfl) (hu j.val j.isLt)))
            (Affine.sub (Affine.add (Affine.sub
              (he j.val j.isLt)
              (affine_deg0_mul 2 (by rfl) (hf j.val j.isLt)))
              (affine_deg0_mul 4 (by rfl) (hg j.val j.isLt)))
              (affine_deg0_mul (2 * λE) (by rfl) (hu j.val j.isLt)))
            (Affine.sub (Affine.add (Affine.sub (Affine.add
              (affine_deg0_mul 3 (by rfl) (he j.val j.isLt))
              (affine_deg0_mul (8 * λE + 4) (by rfl) (hf j.val j.isLt)))
              (affine_deg0_mul 8 (by rfl) (hg j.val j.isLt)))
              (affine_deg0_mul (4 * (λE * λE)) (by rfl) (hu j.val j.isLt)))
              (affine_deg0_mul 8 (by rfl) (affineW_witnessVector_output 32 _ n j.val j.isLt)))) m)
      fun _ => IsR1CSCirc.pure _

theorem r1cs_sub_packedCh (b : Var PackedCh.Inputs (F circomPrime))
    (he : AffineW b.e) (hf : AffineW b.f) (hg : AffineW b.g) (hu : AffineW b.u) :
    IsR1CSCirc (subcircuit PackedCh.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_packedCh _ _ _ _ he hf hg hu)

theorem affineW_subOut_packedCh (b : Var PackedCh.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit PackedCh.circuit b).output n) := by
  intro i hi
  simp only [circuit_norm, subcircuit, PackedCh.circuit, PackedCh.elaborated]
  exact Affine.var _

set_option maxHeartbeats 800000 in
theorem r1cs_packedMaj (a b c u : Var (fields 32) (F circomPrime))
    (ha : AffineW a) (hb : AffineW b) (hc : AffineW c) (hu : AffineW u) :
    IsR1CSCirc (PackedMaj.packedMaj a b c u) := by
  unfold PackedMaj.packedMaj
  exact
    IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun n =>
    IsR1CSCirc.bind
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_mul
            (Affine.sub (affineW_witnessVector_output 32 _ n j.val j.isLt)
              (affine_deg0_mul (λE + 1) (by rfl) (ha j.val j.isLt)))
            (Affine.sub (affineW_witnessVector_output 32 _ n j.val j.isLt)
              (Affine.add (hc j.val j.isLt) (affine_deg0_mul λE (by rfl) (hu j.val j.isLt))))) m)
      fun _ =>
    IsR1CSCirc.bind
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_mul
            (Affine.sub (affineW_witnessVector_output 32 _ n j.val j.isLt)
              (Affine.add (ha j.val j.isLt) (affine_deg0_mul λE (by rfl) (hb j.val j.isLt))))
            (Affine.sub (affineW_witnessVector_output 32 _ n j.val j.isLt)
              (Affine.add
                (affine_deg0_mul λE (by rfl)
                  (Affine.sub
                    (Affine.add (Affine.add (ha j.val j.isLt) (hb j.val j.isLt)) (hu j.val j.isLt))
                    (Affine.const 1)))
                (hc j.val j.isLt)))) m)
      fun _ => IsR1CSCirc.pure _

theorem r1cs_sub_packedMaj (b : Var PackedMaj.Inputs (F circomPrime))
    (ha : AffineW b.a) (hb : AffineW b.b) (hc : AffineW b.c) (hu : AffineW b.u) :
    IsR1CSCirc (subcircuit PackedMaj.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_packedMaj _ _ _ _ ha hb hc hu)

theorem affineW_subOut_packedMaj (b : Var PackedMaj.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit PackedMaj.circuit b).output n) := by
  intro i hi
  simp only [circuit_norm, subcircuit, PackedMaj.circuit, PackedMaj.elaborated]
  exact Affine.var _

set_option maxHeartbeats 1200000 in
theorem r1cs_fusedEAdder (inp : Var FusedEAdder.Inputs (F circomPrime))
    (h_newE : AffineW inp.newE) (h_newEp : AffineW inp.newEp) (h_z : AffineW inp.z)
    (h_e : AffineW inp.e) (h_f : AffineW inp.f) (h_g : AffineW inp.g)
    (h_sig1t : AffineW inp.sig1t) (h_sig1tp : AffineW inp.sig1tp)
    (h_d : AffineW inp.d) (h_h : AffineW inp.h) (h_k0 : AffineW inp.k0) (h_w0 : AffineW inp.w0)
    (h_c : AffineW inp.c) (h_k1 : AffineW inp.k1) (h_w1 : AffineW inp.w1) :
    IsR1CSCirc (FusedEAdder.main inp) := by
  unfold FusedEAdder.main FusedEAdder.lowCarry
  exact
    IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 2 _) fun ncet =>
    IsR1CSCirc.bind_out
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_mul (affineW_witnessVector_output 2 _ ncet j.val j.isLt)
            (Affine.sub (affineW_witnessVector_output 2 _ ncet j.val j.isLt) (Affine.const 1))) m) fun _ =>
    IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 3 _) fun ncetp =>
    IsR1CSCirc.bind_out
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_mul (affineW_witnessVector_output 3 _ ncetp j.val j.isLt)
            (Affine.sub (affineW_witnessVector_output 3 _ ncetp j.val j.isLt) (Affine.const 1))) m) fun _ =>
    IsR1CSCirc.bind_out
      (IsR1CSCirc.assertZero
        (isR1CSRow_mul
          (Affine.sub
            (Affine.sub
              (Affine.fconst_mul _
                (Affine.sub
                  (Affine.sub
                    (Affine.add
                      (Affine.add
                        (Affine.add (Affine.add (Affine.add (Affine.add
                          (affine_fieldFromBitsExpr _ h_d) (affine_fieldFromBitsExpr _ h_h))
                          (affine_fieldFromBitsExpr _ h_sig1t)) (affine_fieldFromBitsExpr _ h_k0))
                          (affine_fieldFromBitsExpr _ h_w0))
                        (affine_fieldFromBitsExpr _ h_z))
                      (Affine.fconst_mul _ (Affine.add (Affine.add (Affine.add (Affine.add
                        (affine_fieldFromBitsExpr _ h_c) (affine_fieldFromBitsExpr _ h_g))
                        (affine_fieldFromBitsExpr _ h_sig1tp)) (affine_fieldFromBitsExpr _ h_k1))
                        (affine_fieldFromBitsExpr _ h_w1))))
                    (affine_fieldFromBitsExpr _ h_newE))
                  (Affine.fconst_mul _ (Affine.add (affine_fieldFromBitsExpr _ h_newEp)
                    (Affine.fconst_mul _ (affine_carryE _ (affineW_witnessVector_output 3 _ ncetp)))))))
              (Affine.fconst_mul _ (affineW_witnessVector_output 2 _ ncet 0 (by norm_num))))
            (Affine.fconst_mul _ (affineW_witnessVector_output 2 _ ncet 1 (by norm_num))))
          (Affine.sub
            (Affine.sub
              (Affine.sub
                (Affine.fconst_mul _
                  (Affine.sub
                    (Affine.sub
                      (Affine.add
                        (Affine.add
                          (Affine.add (Affine.add (Affine.add (Affine.add
                            (affine_fieldFromBitsExpr _ h_d) (affine_fieldFromBitsExpr _ h_h))
                            (affine_fieldFromBitsExpr _ h_sig1t)) (affine_fieldFromBitsExpr _ h_k0))
                            (affine_fieldFromBitsExpr _ h_w0))
                          (affine_fieldFromBitsExpr _ h_z))
                        (Affine.fconst_mul _ (Affine.add (Affine.add (Affine.add (Affine.add
                          (affine_fieldFromBitsExpr _ h_c) (affine_fieldFromBitsExpr _ h_g))
                          (affine_fieldFromBitsExpr _ h_sig1tp)) (affine_fieldFromBitsExpr _ h_k1))
                          (affine_fieldFromBitsExpr _ h_w1))))
                      (affine_fieldFromBitsExpr _ h_newE))
                    (Affine.fconst_mul _ (Affine.add (affine_fieldFromBitsExpr _ h_newEp)
                      (Affine.fconst_mul _ (affine_carryE _ (affineW_witnessVector_output 3 _ ncetp)))))))
                (Affine.fconst_mul _ (affineW_witnessVector_output 2 _ ncet 0 (by norm_num))))
              (Affine.fconst_mul _ (affineW_witnessVector_output 2 _ ncet 1 (by norm_num))))
            (Affine.const 1)))) fun _ =>
    IsR1CSCirc.pure _

theorem r1cs_sub_fusedEAdder (b : Var FusedEAdder.Inputs (F circomPrime))
    (h_newE : AffineW b.newE) (h_newEp : AffineW b.newEp) (h_z : AffineW b.z)
    (h_e : AffineW b.e) (h_f : AffineW b.f) (h_g : AffineW b.g)
    (h_sig1t : AffineW b.sig1t) (h_sig1tp : AffineW b.sig1tp)
    (h_d : AffineW b.d) (h_h : AffineW b.h) (h_k0 : AffineW b.k0) (h_w0 : AffineW b.w0)
    (h_c : AffineW b.c) (h_k1 : AffineW b.k1) (h_w1 : AffineW b.w1) :
    IsR1CSCirc (assertion FusedEAdder.circuit b) :=
  IsR1CSCirc.assertion (fun n => r1cs_fusedEAdder b h_newE h_newEp h_z h_e h_f h_g h_sig1t h_sig1tp
    h_d h_h h_k0 h_w0 h_c h_k1 h_w1 n)

set_option maxHeartbeats 1200000 in
theorem r1cs_fusedAAdder (inp : Var FusedAAdder.Inputs (F circomPrime))
    (h_newA : AffineW inp.newA) (h_newAp : AffineW inp.newAp)
    (h_newE : AffineW inp.newE) (h_newEp : AffineW inp.newEp)
    (h_sig0t : AffineW inp.sig0t) (h_sig0tp : AffineW inp.sig0tp)
    (h_z : AffineW inp.z) (h_d : AffineW inp.d) (h_c : AffineW inp.c) :
    IsR1CSCirc (FusedAAdder.main inp) := by
  unfold FusedAAdder.main FusedAAdder.lowCarry
  exact
    IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 1 _) fun ncat =>
    IsR1CSCirc.bind_out
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_mul (affineW_witnessVector_output 1 _ ncat j.val j.isLt)
            (Affine.sub (affineW_witnessVector_output 1 _ ncat j.val j.isLt) (Affine.const 1))) m) fun _ =>
    IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 2 _) fun ncatp =>
    IsR1CSCirc.bind_out
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_mul (affineW_witnessVector_output 2 _ ncatp j.val j.isLt)
            (Affine.sub (affineW_witnessVector_output 2 _ ncatp j.val j.isLt) (Affine.const 1))) m) fun _ =>
    IsR1CSCirc.bind_out
      (IsR1CSCirc.assertZero
        (isR1CSRow_mul
          (Affine.sub
            (Affine.fconst_mul _
              (Affine.sub
                (Affine.sub
                  (Affine.add
                    (Affine.add
                      (Affine.add (Affine.add (Affine.add
                        (affine_fieldFromBitsExpr _ h_newE) (affine_fieldFromBitsExpr _ h_sig0t))
                        (affine_fieldFromBitsExpr _ (affineW_not32 h_d)))
                        (Affine.const 1))
                      (affine_fieldFromBitsExpr _ h_z))
                    (Affine.fconst_mul _ (Affine.add (Affine.add (Affine.add
                      (affine_fieldFromBitsExpr _ h_newEp) (affine_fieldFromBitsExpr _ h_sig0tp))
                      (affine_fieldFromBitsExpr _ (affineW_not32 h_c)))
                      (Affine.const 1))))
                  (affine_fieldFromBitsExpr _ h_newA))
                (Affine.fconst_mul _ (Affine.add (affine_fieldFromBitsExpr _ h_newAp)
                  (Affine.fconst_mul _ (affine_carryE2 _ (affineW_witnessVector_output 2 _ ncatp)))))))
            (Affine.fconst_mul _ (affineW_witnessVector_output 1 _ ncat 0 (by norm_num))))
          (Affine.sub
            (Affine.sub
              (Affine.fconst_mul _
                (Affine.sub
                  (Affine.sub
                    (Affine.add
                      (Affine.add
                        (Affine.add (Affine.add (Affine.add
                          (affine_fieldFromBitsExpr _ h_newE) (affine_fieldFromBitsExpr _ h_sig0t))
                          (affine_fieldFromBitsExpr _ (affineW_not32 h_d)))
                          (Affine.const 1))
                        (affine_fieldFromBitsExpr _ h_z))
                      (Affine.fconst_mul _ (Affine.add (Affine.add (Affine.add
                        (affine_fieldFromBitsExpr _ h_newEp) (affine_fieldFromBitsExpr _ h_sig0tp))
                        (affine_fieldFromBitsExpr _ (affineW_not32 h_c)))
                        (Affine.const 1))))
                    (affine_fieldFromBitsExpr _ h_newA))
                  (Affine.fconst_mul _ (Affine.add (affine_fieldFromBitsExpr _ h_newAp)
                    (Affine.fconst_mul _ (affine_carryE2 _ (affineW_witnessVector_output 2 _ ncatp)))))))
              (Affine.fconst_mul _ (affineW_witnessVector_output 1 _ ncat 0 (by norm_num))))
            (Affine.const 1)))) fun _ =>
    IsR1CSCirc.pure _

theorem r1cs_sub_fusedAAdder (b : Var FusedAAdder.Inputs (F circomPrime))
    (h_newA : AffineW b.newA) (h_newAp : AffineW b.newAp)
    (h_newE : AffineW b.newE) (h_newEp : AffineW b.newEp)
    (h_sig0t : AffineW b.sig0t) (h_sig0tp : AffineW b.sig0tp)
    (h_z : AffineW b.z) (h_d : AffineW b.d) (h_c : AffineW b.c) :
    IsR1CSCirc (assertion FusedAAdder.circuit b) :=
  IsR1CSCirc.assertion (fun n => r1cs_fusedAAdder b h_newA h_newAp h_newE h_newEp
    h_sig0t h_sig0tp h_z h_d h_c n)

/-- Every word of `stateVarPaired` is affine when the input state is. -/
theorem affineW_stateVarPaired (i₀ : ℕ) (s : Var SHA256State (F circomPrime))
    (hs : ∀ j (hj : j < 8), AffineW s[j]) :
    ∀ (m j : ℕ) (hj : j < 8), AffineW ((SHA256Rounds63.stateVarPaired i₀ s m)[j]) := by
  intro m
  induction m with
  | zero => intro j hj; exact hs j hj
  | succ p ih =>
      intro j hj
      rw [SHA256Rounds63.stateVarPaired]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact affineW_mapRange_var _
      · exact affineW_mapRange_var _
      · exact ih 0 (by omega)
      · exact ih 1 (by omega)
      · exact affineW_mapRange_var _
      · exact affineW_mapRange_var _
      · exact ih 4 (by omega)
      · exact ih 5 (by omega)

set_option maxHeartbeats 2000000 in
theorem r1cs_sha256RoundPair (input : Var SHA256RoundPair.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW input.state[j])
    (hk0 : AffineW input.k0) (hw0 : AffineW input.w0)
    (hk1 : AffineW input.k1) (hw1 : AffineW input.w1) :
    IsR1CSCirc (SHA256RoundPair.main input) := by
  unfold SHA256RoundPair.main
  exact
    IsR1CSCirc.bind_out (r1cs_sub_upperSigma1 _ (hstate 4 (by omega))) fun n1 =>
    IsR1CSCirc.bind_out (r1cs_sub_upperSigma0 _ (hstate 0 (by omega))) fun n2 =>
    IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun n4 =>
    IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun n5 =>
    IsR1CSCirc.bind_out (r1cs_sub_boolVec32 _ (affineW_varFromOffset 32 n4)) fun _ =>
    IsR1CSCirc.bind_out (r1cs_sub_boolVec32 _ (affineW_varFromOffset 32 n5)) fun _ =>
    IsR1CSCirc.bind_out (r1cs_sub_upperSigma1 _ (affineW_varFromOffset 32 n4)) fun n8 =>
    IsR1CSCirc.bind_out (r1cs_sub_upperSigma0 _ (affineW_varFromOffset 32 n5)) fun n9 =>
    IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun n11 =>
    IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun n12 =>
    IsR1CSCirc.bind_out (r1cs_sub_boolVec32 _ (affineW_varFromOffset 32 n11)) fun _ =>
    IsR1CSCirc.bind_out (r1cs_sub_boolVec32 _ (affineW_varFromOffset 32 n12)) fun _ =>
    IsR1CSCirc.bind_out (r1cs_sub_packedCh _ (hstate 4 (by omega)) (hstate 5 (by omega))
      (hstate 6 (by omega)) (affineW_varFromOffset 32 n4)) fun n15 =>
    IsR1CSCirc.bind_out (r1cs_sub_packedMaj _ (hstate 0 (by omega)) (hstate 1 (by omega))
      (hstate 2 (by omega)) (affineW_varFromOffset 32 n5)) fun n16 =>
    IsR1CSCirc.bind_out (r1cs_sub_fusedEAdder _
      (affineW_varFromOffset 32 n4) (affineW_varFromOffset 32 n11)
      (affineW_subOut_packedCh _ n15) (hstate 4 (by omega)) (hstate 5 (by omega))
      (hstate 6 (by omega)) (affineW_subOut_upperSigma1 _ n1) (affineW_subOut_upperSigma1 _ n8)
      (hstate 3 (by omega)) (hstate 7 (by omega)) hk0 hw0 (hstate 2 (by omega)) hk1 hw1) fun _ =>
    IsR1CSCirc.bind_out (r1cs_sub_fusedAAdder _
      (affineW_varFromOffset 32 n5) (affineW_varFromOffset 32 n12)
      (affineW_varFromOffset 32 n4) (affineW_varFromOffset 32 n11)
      (affineW_subOut_upperSigma0 _ n2) (affineW_subOut_upperSigma0 _ n9)
      (affineW_subOut_packedMaj _ n16)
      (hstate 3 (by omega)) (hstate 2 (by omega))) fun _ =>
    IsR1CSCirc.pure _

theorem r1cs_sub_sha256RoundPair (b : Var SHA256RoundPair.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW b.state[j])
    (hk0 : AffineW b.k0) (hw0 : AffineW b.w0) (hk1 : AffineW b.k1) (hw1 : AffineW b.w1) :
    IsR1CSCirc (subcircuit SHA256RoundPair.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_sha256RoundPair _ hstate hk0 hw0 hk1 hw1)

set_option maxHeartbeats 800000 in
theorem affineW_subOut_sha256RoundPair (b : Var SHA256RoundPair.Inputs (F circomPrime)) (n : ℕ)
    (hb : ∀ j (hj : j < 8), AffineW b.state[j]) :
    ∀ j (hj : j < 8), AffineW (((subcircuit SHA256RoundPair.circuit b).output n)[j]) := by
  intro j hj
  have heq : (subcircuit SHA256RoundPair.circuit b).output n
      = SHA256Rounds63.stateVarPaired n b.state 1 := by
    simp only [circuit_norm, subcircuit, SHA256RoundPair.circuit, SHA256RoundPair.elaborated,
      SHA256Rounds63.stateVarPaired]
  rw [heq]; exact affineW_stateVarPaired n b.state hb 1 j hj

theorem r1cs_sha256Rounds62_paired (input : Var SHA256Rounds63.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW input.state[j])
    (hsched : ∀ k (hk : k < 64), AffineW input.schedule[k]) :
    IsR1CSCirc (SHA256Rounds63.main62_paired input) := by
  refine IsR1CSCirc.foldlRange_inv (fun s => ∀ j (hj : j < 8), AffineW s[j]) hstate ?_ ?_
  · intro s i hs
    exact r1cs_sub_sha256RoundPair _ hs (affineW_constWord32 _) (hsched _ (by omega))
      (affineW_constWord32 _) (hsched _ (by omega))
  · intro s i n hs
    exact affineW_subOut_sha256RoundPair _ n hs

theorem r1cs_sub_sha256Rounds62_paired (b : Var SHA256Rounds63.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW b.state[j])
    (hsched : ∀ k (hk : k < 64), AffineW b.schedule[k]) :
    IsR1CSCirc (subcircuit SHA256Rounds63.circuit62_paired b) :=
  IsR1CSCirc.subcircuit (r1cs_sha256Rounds62_paired _ hstate hsched)

set_option maxHeartbeats 800000 in
theorem affineW_subOut_sha256Rounds62_paired (b : Var SHA256Rounds63.Inputs (F circomPrime)) (n : ℕ)
    (hb : ∀ j (hj : j < 8), AffineW b.state[j]) :
    ∀ j (hj : j < 8), AffineW (((subcircuit SHA256Rounds63.circuit62_paired b).output n)[j]) := by
  intro j hj
  have heq : (subcircuit SHA256Rounds63.circuit62_paired b).output n
      = SHA256Rounds63.stateVarPaired n b.state 31 := by
    simp only [circuit_norm, subcircuit, SHA256Rounds63.circuit62_paired,
      SHA256Rounds63.elaborated62_paired]
  rw [heq]; exact affineW_stateVarPaired n b.state hb 31 j hj

/-! ### Fused-compression R1CS via `circuit63_paired`

`circuit63_paired`'s output is a `SHA256Round` output on top of `circuit62_paired`:
words 0/4 are fresh witness rows (affine), words 1/2/3/5/6/7 pass through the
paired state (affine by `affineW_stateVarPaired`). These lemmas rebuild
`r1cs_sha256Rounds` (and the `CompressBlock`/`CompressBlock5` R1CS) on top of the
paired-gadget R1CS machinery above. -/

set_option maxHeartbeats 800000 in
theorem affineW_subOut_circuit63_paired (b : Var SHA256Rounds63.Inputs (F circomPrime)) (n : ℕ)
    (hb : ∀ j (hj : j < 8), AffineW b.state[j]) :
    ∀ j (hj : j < 8), AffineW (((subcircuit SHA256Rounds63.circuit63_paired b).output n)[j]) := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [circuit_norm, subcircuit, SHA256Rounds63.circuit63_paired,
      SHA256Rounds63.elaborated63_paired, SHA256Rounds63.circuit62_paired,
      SHA256Rounds63.elaborated62_paired]
  · exact affineW_mapRange_var _
  · exact affineW_stateVarPaired _ _ hb 31 0 (by omega)
  · exact affineW_stateVarPaired _ _ hb 31 1 (by omega)
  · exact affineW_stateVarPaired _ _ hb 31 2 (by omega)
  · exact affineW_mapRange_var _
  · exact affineW_stateVarPaired _ _ hb 31 4 (by omega)
  · exact affineW_stateVarPaired _ _ hb 31 5 (by omega)
  · exact affineW_stateVarPaired _ _ hb 31 6 (by omega)

theorem r1cs_circuit63_paired (input : Var SHA256Rounds63.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW input.state[j])
    (hsched : ∀ k (hk : k < 64), AffineW input.schedule[k]) :
    IsR1CSCirc (SHA256Rounds63.main63_paired input) :=
  IsR1CSCirc.bind_out (r1cs_sub_sha256Rounds62_paired _ hstate hsched) fun _ =>
    IsR1CSCirc.subcircuit (r1cs_sha256Round _ _ _
      (affineW_subOut_sha256Rounds62_paired _ _ hstate)
      (affineW_constWord32 _) (hsched 62 (by omega)))

theorem r1cs_sub_circuit63_paired (b : Var SHA256Rounds63.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW b.state[j])
    (hsched : ∀ k (hk : k < 64), AffineW b.schedule[k]) :
    IsR1CSCirc (subcircuit SHA256Rounds63.circuit63_paired b) :=
  IsR1CSCirc.subcircuit (r1cs_circuit63_paired _ hstate hsched)

theorem r1cs_sha256Rounds (input : Var SHA256Rounds.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW input.state[j])
    (hsched : ∀ k (hk : k < 64), AffineW input.schedule[k]) :
    IsR1CSCirc (SHA256Rounds.main input) :=
  IsR1CSCirc.bind_out (r1cs_sub_circuit63_paired _ hstate hsched) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_upperSigma1 _
    (affineW_subOut_circuit63_paired _ _ hstate 4 (by omega))) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_ch32 _
    (affineW_subOut_circuit63_paired _ _ hstate 4 (by omega))
    (affineW_subOut_circuit63_paired _ _ hstate 5 (by omega))
    (affineW_subOut_circuit63_paired _ _ hstate 6 (by omega))) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_upperSigma0 _
    (affineW_subOut_circuit63_paired _ _ hstate 0 (by omega))) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_maj32 _
    (affineW_subOut_circuit63_paired _ _ hstate 0 (by omega))
    (affineW_subOut_circuit63_paired _ _ hstate 1 (by omega))
    (affineW_subOut_circuit63_paired _ _ hstate 2 (by omega))) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_addMany (n := 8) (by norm_num) _ (affineW_vec8
    (hstate 0 (by omega))
    (affineW_subOut_circuit63_paired _ _ hstate 7 (by omega))
    (affineW_subOut_upperSigma1 _ _) (affineW_subOut_ch32 _ _)
    (affineW_constWord32 _) (hsched 63 (by omega))
    (affineW_subOut_upperSigma0 _ _) (affineW_subOut_maj32 _ _))) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_addMany (n := 7) (by norm_num) _ (affineW_vec7
    (hstate 4 (by omega))
    (affineW_subOut_circuit63_paired _ _ hstate 3 (by omega))
    (affineW_subOut_circuit63_paired _ _ hstate 7 (by omega))
    (affineW_subOut_upperSigma1 _ _) (affineW_subOut_ch32 _ _)
    (affineW_constWord32 _) (hsched 63 (by omega)))) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_add32 _ (hstate 1 (by omega))
    (affineW_subOut_circuit63_paired _ _ hstate 0 (by omega))) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_add32 _ (hstate 2 (by omega))
    (affineW_subOut_circuit63_paired _ _ hstate 1 (by omega))) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_add32 _ (hstate 3 (by omega))
    (affineW_subOut_circuit63_paired _ _ hstate 2 (by omega))) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_add32 _ (hstate 5 (by omega))
    (affineW_subOut_circuit63_paired _ _ hstate 4 (by omega))) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_add32 _ (hstate 6 (by omega))
    (affineW_subOut_circuit63_paired _ _ hstate 5 (by omega))) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_add32 _ (hstate 7 (by omega))
    (affineW_subOut_circuit63_paired _ _ hstate 6 (by omega))) fun _ =>
  IsR1CSCirc.pure _

/-- Every word of `varSchedule` is affine when the input block is. -/
theorem affineW_varSchedule (i₀ : ℕ) (block : SHA256Block (Expression (F circomPrime)))
    (hblock : ∀ k (hk : k < 16), AffineW block[k]) :
    ∀ (m k : ℕ) (hk : k < 64), AffineW ((MessageSchedule.varSchedule i₀ block m)[k]) := by
  intro m
  induction m with
  | zero =>
      intro k hk
      rw [MessageSchedule.varSchedule]
      show AffineW ((block ++ Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F circomPrime))))[k])
      rw [Vector.getElem_append]
      split
      · exact hblock _ _
      · rw [Vector.getElem_replicate]
        intro j hj; rw [Vector.getElem_replicate]; exact Affine.zero (F := F circomPrime)
  | succ p ih =>
      intro k hk
      rw [MessageSchedule.varSchedule]
      split
      · rw [Vector.getElem_set]
        split
        · exact affineW_varFromOffset _ _
        · exact ih k hk
      · exact ih k hk

theorem affineW_subOut_messageSchedule (b : SHA256Block (Expression (F circomPrime))) (n : ℕ)
    (hb : ∀ k (hk : k < 16), AffineW b[k]) :
    ∀ k (hk : k < 64), AffineW (((subcircuit MessageSchedule.circuit b).output n)[k]) := by
  intro k hk
  have heq : (subcircuit MessageSchedule.circuit b).output n = MessageSchedule.varSchedule n b 48 := by
    simp only [circuit_norm, subcircuit, MessageSchedule.circuit, MessageSchedule.elaborated]
  rw [heq]; exact affineW_varSchedule n b hb 48 k hk

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
/-- The fused compression's output words are the `AddMany`/`Add32` subcircuit
outputs, i.e. fresh `mapRange` witness vectors — affine unconditionally. -/
theorem affineW_subOut_sha256Rounds (b : Var SHA256Rounds.Inputs (F circomPrime)) (n : ℕ) :
    ∀ j (hj : j < 8), AffineW (((subcircuit SHA256Rounds.circuit b).output n)[j]) := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [circuit_norm, subcircuit, SHA256Rounds.circuit, SHA256Rounds.elaborated];
      exact affineW_mapRange_var _)

theorem messageSchedule_isR1CS :
    isR1CS (Input := SHA256Block) (Output := SHA256Schedule) (F := F circomPrime)
      MessageSchedule.main :=
  isR1CS_of_IsR1CSCirc
    (fun input hinput => r1cs_messageSchedule input (affineW_of_affineProvable_pvec input hinput))
    (fun input hinput n =>
      affineProvable_pvec_of_affineW ((MessageSchedule.main input).output n)
        (by
          intro k hk
          have heq : (MessageSchedule.main input).output n =
              MessageSchedule.varSchedule n input 48 := by
            simp only [MessageSchedule.main, circuit_norm, ScheduleStep.circuit,
              ScheduleStep.elaborated]
            exact MessageSchedule.finFoldl_eq_varSchedule_48 _ _
          rw [heq]
          exact affineW_varSchedule n input (affineW_of_affineProvable_pvec input hinput) 48 k hk))

theorem r1cs_sub_messageSchedule (b : SHA256Block (Expression (F circomPrime)))
    (hb : ∀ k (hk : k < 16), AffineW b[k]) : IsR1CSCirc (subcircuit MessageSchedule.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_messageSchedule _ hb)

theorem r1cs_sub_sha256Rounds (b : Var SHA256Rounds.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW b.state[j])
    (hsched : ∀ k (hk : k < 64), AffineW b.schedule[k]) :
    IsR1CSCirc (subcircuit SHA256Rounds.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_sha256Rounds _ hstate hsched)

theorem affine_block5ScheduleBit (flags : Var (fields inputBufferLen) (F circomPrime))
    (hflags : AffineW flags) (word : Fin 64) (bit : Fin 32) :
    Affine (block5ScheduleBit flags word bit) := by
  unfold block5ScheduleBit
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc len hacc
    exact Affine.add hacc (Affine.mul_deg0 (hflags _ len.isLt) (degree_const _))

/-- Every word of the block-5 schedule is affine when the length flags are. -/
theorem affineW_block5Schedule (flags : Var (fields inputBufferLen) (F circomPrime))
    (hflags : AffineW flags) (k : ℕ) (hk : k < 64) :
    AffineW ((block5Schedule flags)[k]'hk) := by
  intro bit hbit
  unfold block5Schedule
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  exact affine_block5ScheduleBit flags hflags ⟨k, hk⟩ ⟨bit, hbit⟩

attribute [local irreducible] block5Schedule

theorem r1cs_compressBlock (input : Var CompressBlock.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW input.state[j])
    (hblock : ∀ k (hk : k < 16), AffineW input.block[k]) :
    IsR1CSCirc (CompressBlock.main input) :=
  IsR1CSCirc.bind_out (r1cs_sub_messageSchedule _ hblock) fun _ =>
    r1cs_sub_sha256Rounds _ hstate (affineW_subOut_messageSchedule _ _ hblock)

theorem r1cs_compressBlock5 (input : Var CompressBlock5.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW input.state[j])
    (hflags : AffineW input.lenFlags) :
    IsR1CSCirc (CompressBlock5.main input) :=
  r1cs_sub_sha256Rounds ⟨input.state, block5Schedule input.lenFlags⟩ hstate
    (affineW_block5Schedule input.lenFlags hflags)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
theorem affineW_subOut_compressBlock (input : Var CompressBlock.Inputs (F circomPrime)) (n : ℕ) :
    ∀ j (hj : j < 8), AffineW (((subcircuit CompressBlock.circuit input).output n)[j]) := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [circuit_norm, subcircuit, CompressBlock.circuit, CompressBlock.elaborated,
      SHA256Rounds.circuit, SHA256Rounds.elaborated];
      exact affineW_mapRange_var _)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1600000 in
theorem affineW_subOut_compressBlock5 (input : Var CompressBlock5.Inputs (F circomPrime)) (n : ℕ) :
    ∀ j (hj : j < 8), AffineW (((subcircuit CompressBlock5.circuit input).output n)[j]) := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [circuit_norm, subcircuit, CompressBlock5.circuit, CompressBlock5.elaborated,
      SHA256Rounds.circuit, SHA256Rounds.elaborated];
      exact affineW_mapRange_var _)

/-! ## Structural cost / R1CS certificates for the padding gadgets and `main`

These mirror the cost lemmas above for the padding/digest gadgets, and add the
matching `IsR1CSCirc` certificates, all without native evaluation or `decide`.

Two performance points make the deep `do`-blocks here elaborate cheaply:

* the `BitsBool` over `paddedBitsLen` bits is certified through a **size-generic**
  wrapper (`*_sub_bitsBool`) and only then instantiated, so the unifier never
  materialises the 2560-element flat operation list at a concrete size; and
* `byteFromWord`/`expectedPaddedByte`/`paddedWord`/`paddedBit`/`paddedBlock` are
  made `local irreducible` before the composite proofs, so unification against
  `CheckPad.main` stays syntactic instead of unfolding the 256-deep `Fin.foldl`
  expressions. The composite proofs supply `circuit`/`b` explicitly for the same
  reason (no inference from the now-opaque goal is required).
-/

/-! ### Affineness of `byteFromWord` and the single-row certificate for the
padding-byte constraint

`expectedPaddedByte` is written in factored form `constPart + message[j] · coefSum`,
so the asserted `byteFromWord word b - expectedPaddedByte …` is `L - (C + A·B)`
with `L, C, A, B` all affine — a single R1CS row. (The naive sum-of-products form
would be rank-2+ once `message` is a vector of input variables.) -/

/-- `L - (C + A*B)` with all of `L, C, A, B` affine is a single R1CS row. -/
theorem isR1CSRow_sub_add_mul {L C A B : Expression (F circomPrime)}
    (hL : Affine L) (hC : Affine C) (hA : Affine A) (hB : Affine B) :
    isR1CSRow (L - (C + A * B)) := by
  rcases r1csProducts_mul_affine hA hB with h | h
  · exact isR1CSRow_of_r1csProducts (k := 0)
      (by show r1csProducts (L + -(C + A * B)) = some 0
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_add,
            r1csProducts_of_affine hL, r1csProducts_of_affine hC, h]) (by omega)
  · exact isR1CSRow_of_r1csProducts (k := 1)
      (by show r1csProducts (L + -(C + A * B)) = some 1
          rw [r1csProducts_add, r1csProducts_neg, r1csProducts_add,
            r1csProducts_of_affine hL, r1csProducts_of_affine hC, h]) (by omega)

theorem affine_byteFromWord (word : Var (fields 32) (F circomPrime)) (b : Fin 4)
    (hw : AffineW word) : Affine (byteFromWord word b) := by
  unfold byteFromWord
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc bit hacc
    exact Affine.add hacc (Affine.mul_deg0 (hw _ (by omega)) (degree_const _))

/-- The padding-byte constraint is a single R1CS row when the witnessed word and
the (now symbolic) message and length flags are affine. -/
theorem r1csRow_checkPaddedByte (word : Var (fields 32) (F circomPrime)) (b : Fin 4)
    (message lenFlags : Var (fields inputBufferLen) (F circomPrime)) (j : Fin paddedBytesLen)
    (hword : AffineW word) (hmsg : AffineW message) (hflags : AffineW lenFlags) :
    isR1CSRow (byteFromWord word b - expectedPaddedByte message lenFlags j) := by
  rw [expectedPaddedByte]
  refine isR1CSRow_sub_add_mul (affine_byteFromWord _ _ hword) ?_ ?_ ?_
  · -- constant part: ∑ lenFlags[len] · (padding const)
    apply affine_finFoldl'
    · exact Affine.zero
    · intro acc len hacc
      exact Affine.add hacc (Affine.mul_deg0 (hflags _ len.isLt) (degree_const _))
  · -- message term: message[j] (or 0 past the buffer), affine
    split
    · exact hmsg _ _
    · exact Affine.zero
  · -- coefficient mass: ∑_{len > j} lenFlags[len], affine
    apply affine_finFoldl'
    · exact Affine.zero
    · intro acc len hacc
      refine Affine.add hacc ?_
      split
      · exact hflags _ len.isLt
      · exact Affine.zero

/-! ### Affineness of `paddedWord` / `paddedBlock` slices of an affine bit-vector -/

theorem affineW_paddedWord (padded : Var SHA256PaddedBits (F circomPrime))
    (hp : AffineW padded) (j : Fin paddedBytesLen) : AffineW (paddedWord padded j) := by
  intro bit hbit
  rw [paddedWord, Vector.getElem_ofFn]
  exact hp _ _

theorem affineW_paddedBlock (padded : Var SHA256PaddedBits (F circomPrime))
    (hp : AffineW padded) (block : Fin witnessedBlocksLen) :
    ∀ k (hk : k < 16), AffineW ((paddedBlock padded block)[k]'hk) := by
  intro k hk bit hbit
  rw [paddedBlock, Vector.getElem_ofFn, Vector.getElem_ofFn, paddedBit]
  exact hp _ _

/-! ### Per-gadget cost leaves for the padding gadgets -/

theorem costIs_checkLenFlags (b : Var CheckLenFlags.Inputs (F circomPrime)) :
    CostIs (CheckLenFlags.main b) ⟨0, 258⟩ :=
  CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ => CostIs.assertZero _

theorem costIs_bitsBool (n : ℕ) [NeZero n] (input : Var (fields n) (F circomPrime)) :
    CostIs (BitsBool.main n input) ⟨0, n⟩ := by
  have h : CostIs (BitsBool.main n input) ⟨n * 0, n * 1⟩ :=
    CostIs.forEach fun _ => CostIs.assertZero _
  rw [Nat.mul_zero, Nat.mul_one] at h
  exact h

theorem costIs_checkPaddedByte (j : Fin paddedBytesLen)
    (input : Var CheckPaddedByte.Inputs (F circomPrime)) :
    CostIs (CheckPaddedByte.main j input) ⟨0, 1⟩ :=
  CostIs.assertZero _

/-! ### R1CS certificates for the padding gadgets -/

theorem r1cs_checkLenFlags (b : Var CheckLenFlags.Inputs (F circomPrime))
    (hmsg : Affine b.messageLen) (hflags : AffineW b.lenFlags) :
    IsR1CSCirc (CheckLenFlags.main b) :=
  IsR1CSCirc.bind
    (IsR1CSCirc.forEach fun i m =>
      IsR1CSCirc.assertZero
        (isR1CSRow_mul (hflags i.val i.isLt)
          (Affine.sub (hflags i.val i.isLt) (Affine.const 1))) m)
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_of_affine
        (Affine.sub
          (affine_finFoldl' (fun acc i => acc + b.lenFlags[i]) 0 Affine.zero
            (fun acc i h => Affine.add h (hflags i.val i.isLt)))
          (Affine.const 1))))
    fun _ =>
  IsR1CSCirc.assertZero
    (isR1CSRow_of_affine
      (Affine.sub hmsg
        (affine_finFoldl'
          (fun acc i => acc + b.lenFlags[i] * (((i.val : ℕ) : F circomPrime) : Expression (F circomPrime)))
          0 Affine.zero
          (fun acc i h => Affine.add h (Affine.mul_deg0 (hflags i.val i.isLt) (degree_const _))))))

theorem r1cs_bitsBool (n : ℕ) [NeZero n] (input : Var (fields n) (F circomPrime))
    (hin : AffineW input) : IsR1CSCirc (BitsBool.main n input) :=
  IsR1CSCirc.forEach fun i m =>
    IsR1CSCirc.assertZero
      (isR1CSRow_mul (hin i.val i.isLt)
        (Affine.sub (hin i.val i.isLt) (Affine.const 1))) m

theorem r1cs_checkPaddedByte (j : Fin paddedBytesLen)
    (input : Var CheckPaddedByte.Inputs (F circomPrime))
    (hword : AffineW input.word) (hmsg : AffineW input.message) (hflags : AffineW input.lenFlags) :
    IsR1CSCirc (CheckPaddedByte.main j input) :=
  IsR1CSCirc.assertZero (r1csRow_checkPaddedByte _ _ _ _ j hword hmsg hflags)

/-! ### Size-generic subcircuit wrappers for `BitsBool`

Proving the `assertion` wrapper at *generic* `n` keeps the unifier from
materialising the concrete `n`-element operation list; instantiating afterwards
is pure substitution. -/

theorem costIs_sub_checkLenFlags (b : Var CheckLenFlags.Inputs (F circomPrime)) :
    CostIs (assertion CheckLenFlags.circuit b) ⟨0, 258⟩ :=
  CostIs.assertion (costIs_checkLenFlags b)

theorem r1cs_sub_checkLenFlags (b : Var CheckLenFlags.Inputs (F circomPrime))
    (hmsg : Affine b.messageLen) (hflags : AffineW b.lenFlags) :
    IsR1CSCirc (assertion CheckLenFlags.circuit b) :=
  IsR1CSCirc.assertion (r1cs_checkLenFlags b hmsg hflags)

theorem costIs_sub_bitsBool (n : ℕ) [NeZero n] (input : Var (fields n) (F circomPrime)) :
    CostIs (assertion (BitsBool.circuit n) input) ⟨0, n⟩ :=
  CostIs.assertion (costIs_bitsBool n input)

theorem r1cs_sub_bitsBool (n : ℕ) [NeZero n] (input : Var (fields n) (F circomPrime))
    (hp : AffineW input) : IsR1CSCirc (assertion (BitsBool.circuit n) input) :=
  IsR1CSCirc.assertion (r1cs_bitsBool n input hp)

-- Keep the deep `Fin.foldl`/`ofFn` expressions folded during the composite
-- proofs below: unification against `CheckPad.main` stays syntactic.
attribute [local irreducible] byteFromWord expectedPaddedByte paddedWord paddedBit paddedBlock

theorem costIs_checkPad (input : Var CheckPad.Inputs (F circomPrime)) :
    CostIs (CheckPad.main input) ⟨0, 2562⟩ :=
  CostIs.bind (costIs_sub_checkLenFlags _) fun _ =>
  CostIs.bind (costIs_sub_bitsBool paddedBitsLen _) fun _ =>
  CostIs.forEach (fun j m =>
    CostIs.assertion (circuit := CheckPaddedByte.circuit j)
      (b := ⟨input.messageLen, input.message, input.lenFlags, paddedWord input.padded j⟩)
      (costIs_checkPaddedByte j _) m)

theorem r1cs_checkPad (input : Var CheckPad.Inputs (F circomPrime))
    (hmsglen : Affine input.messageLen) (hmsg : AffineW input.message)
    (hflags : AffineW input.lenFlags) (hpadded : AffineW input.padded) :
    IsR1CSCirc (CheckPad.main input) :=
  IsR1CSCirc.bind (r1cs_sub_checkLenFlags _ hmsglen hflags) fun _ =>
  IsR1CSCirc.bind (r1cs_sub_bitsBool paddedBitsLen _ hpadded) fun _ =>
  IsR1CSCirc.forEach (fun j m =>
    IsR1CSCirc.assertion (circuit := CheckPaddedByte.circuit j)
      (b := ⟨input.messageLen, input.message, input.lenFlags, paddedWord input.padded j⟩)
      (r1cs_checkPaddedByte j _ (affineW_paddedWord _ hpadded j) hmsg hflags) m)

/-! ### Subcircuit wrappers for `CheckPad`, compress blocks, digest -/

theorem costIs_sub_checkPad (b : Var CheckPad.Inputs (F circomPrime)) :
    CostIs (assertion CheckPad.circuit b) ⟨0, 2562⟩ :=
  CostIs.assertion (costIs_checkPad b)

theorem r1cs_sub_checkPad (b : Var CheckPad.Inputs (F circomPrime))
    (hmsglen : Affine b.messageLen) (hmsg : AffineW b.message)
    (hflags : AffineW b.lenFlags) (hpadded : AffineW b.padded) :
    IsR1CSCirc (assertion CheckPad.circuit b) :=
  IsR1CSCirc.assertion (r1cs_checkPad b hmsglen hmsg hflags hpadded)

theorem costIs_selectDigest (input : Var SelectDigest.Inputs (F circomPrime)) :
    CostIs (SelectDigest.main input) selectDigestCost :=
  CostIs.bind (CostIs.witnessVector 8 _) fun z =>
  CostIs.bind
    (CostIs.forEach fun _len =>
      CostIs.forEach fun _w => CostIs.assertZero _) fun _ =>
  CostIs.pure z

theorem costIs_sub_selectDigest (input : Var SelectDigest.Inputs (F circomPrime)) :
    CostIs (subcircuit SelectDigest.circuit input) selectDigestCost :=
  CostIs.subcircuit (costIs_selectDigest _)

/-- The aggregated flag sum of a candidate group is affine when the flags are:
a fold of affine additions with no products. -/
theorem affine_groupFlagSum (lenFlags : Var (fields inputBufferLen) (F circomPrime))
    (hflags : AffineW lenFlags) (g : Fin paddedBlocksLen) :
    Affine (SelectDigest.groupFlagSum lenFlags g) := by
  unfold SelectDigest.groupFlagSum
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc len hacc
    refine Affine.add hacc ?_
    split
    · exact hflags _ len.isLt
    · exact Affine.zero

/-- Each assert of the digest multiplexer is `A · B` with `A = groupFlagSum g`
affine and `B = word_g[w] − digest[w]` affine — a single R1CS row. -/
theorem r1cs_selectDigest_main (b : Var SelectDigest.Inputs (F circomPrime))
    (hflags : AffineW b.lenFlags)
    (hstates : ∀ k (hk : k < paddedBlocksLen), ∀ j (hj : j < 8),
      AffineW ((SelectDigest.statesVec b)[k]'hk)[j]) :
    IsR1CSCirc (SelectDigest.main b) := by
  unfold SelectDigest.main
  refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 8 _) fun n => ?_
  refine IsR1CSCirc.bind (IsR1CSCirc.forEach fun g m => ?_) fun _ => IsR1CSCirc.pure _
  refine IsR1CSCirc.forEach (fun w m' => ?_) m
  refine IsR1CSCirc.assertZero ?_ m'
  exact isR1CSRow_mul (affine_groupFlagSum _ hflags g)
    (Affine.sub
      (affine_fieldFromBitsExpr _ (hstates g.val g.isLt w.val w.isLt))
      (affineW_witnessVector_output 8 _ n w.val w.isLt))

theorem r1cs_selectDigest (b : Var SelectDigest.Inputs (F circomPrime))
    (hflags : AffineW b.lenFlags)
    (hstates : ∀ k (hk : k < paddedBlocksLen), ∀ j (hj : j < 8),
      AffineW ((SelectDigest.statesVec b)[k]'hk)[j]) :
    IsR1CSCirc (subcircuit SelectDigest.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_selectDigest_main b hflags hstates)

/-- The digest multiplexer's output is its witness row, hence affine. -/
theorem affineW_subOut_selectDigest (b : Var SelectDigest.Inputs (F circomPrime)) (n : ℕ) :
    AffineW ((subcircuit SelectDigest.circuit b).output n) := by
  intro i hi
  simp only [circuit_norm, subcircuit, SelectDigest.circuit, SelectDigest.elaborated]
  exact Affine.var _

theorem costIs_sub_compressBlock (b : Var CompressBlock.Inputs (F circomPrime)) :
    CostIs (subcircuit CompressBlock.circuit b) compressBlockCost :=
  CostIs.subcircuit (costIs_compressBlock _)

theorem r1cs_sub_compressBlock (b : Var CompressBlock.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW b.state[j])
    (hblock : ∀ k (hk : k < 16), AffineW b.block[k]) :
    IsR1CSCirc (subcircuit CompressBlock.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_compressBlock _ hstate hblock)

theorem costIs_sub_compressBlock5 (b : Var CompressBlock5.Inputs (F circomPrime)) :
    CostIs (subcircuit CompressBlock5.circuit b) compressBlock5Cost :=
  CostIs.subcircuit (costIs_compressBlock5 _)

theorem r1cs_sub_compressBlock5 (b : Var CompressBlock5.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW b.state[j])
    (hflags : AffineW b.lenFlags) :
    IsR1CSCirc (subcircuit CompressBlock5.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_compressBlock5 _ hstate hflags)

/-- The fixed initial state `H0` is a vector of constant words, hence affine. -/
theorem affineW_state0 (j : ℕ) (hj : j < 8) :
    AffineW ((Vector.ofFn fun i => constWord32 Specs.SHA256.H0[i] :
      Var SHA256State (F circomPrime))[j]'hj) := by
  rw [Vector.getElem_ofFn]
  exact affineW_constWord32 _

/-! ### Symbolic top-level input atoms

The challenge's `isR1CS main` now ranges over any affine symbolic input, so the
message bytes and length are obtained by projecting the generic `AffineProvable`
hypothesis. -/

theorem affineW_input_message (input : Var Input (F circomPrime)) (hinput : AffineProvable input) :
    AffineW input.message := by
  intro i hi
  have hsz : size Input = inputBufferLen + 1 := rfl
  have hi' : i < size Input := by omega
  simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz, hi] using hinput i hi'

theorem affine_input_messageLen (input : Var Input (F circomPrime)) (hinput : AffineProvable input) :
    Affine input.messageLen := by
  have hsz : size Input = inputBufferLen + 1 := rfl
  simpa [AffineProvable, circuit_norm, explicit_provable_type, hsz] using
    hinput inputBufferLen (by omega)

/-- The `sumExpr` linear-combination of an affine word vector is affine. -/
theorem affine_sumExpr {n : ℕ} (words : Var (ProvableVector (fields 32) n) (F circomPrime))
    (hwords : ∀ i : Fin n, AffineW words[i]) : Affine (AddMany.sumExpr words) := by
  unfold AddMany.sumExpr
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    exact Affine.add hacc (affine_fieldFromBitsExpr _ (hwords i))

/-- The `highExpr` weighted high-carry combination of an affine bit vector is affine. -/
theorem affine_highExpr {m : ℕ} (cv : Var (fields m) (F circomPrime))
    (hcv : AffineW cv) : Affine (AddMany.highExpr cv) := by
  unfold AddMany.highExpr
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc j hacc
    exact Affine.add hacc (Affine.mul_deg0 (hcv j.val j.isLt) (degree_const _))

/-! ## w62/w63 wide-absorption cost/R1CS certificates (blocks 1-4)

Ported from bufferhe4d's 166,935 submission
(`/Users/simon/Documents/dev/Projects/zk.golf/solutions/sha-bufferhe4d-166935/Cost.lean`),
credit to bufferhe4d. Covers `CompressBlockWide` (used for blocks 1-4 in
`Main.lean`); `CompressBlock`/`CompressBlock5`'s existing cost/R1CS lemmas above
are untouched. -/

/-- The 46-step message schedule (last two words are consumed by
`ScheduleStepLast`, so the fold stops at 46). -/
def messageScheduleCost46 : Count :=
  ⟨46 * scheduleStepCost.allocations, 46 * scheduleStepCost.constraints⟩

/-- The peeled 62-round loop (rounds 0..61), for the wide-round tail. -/
def sha256Rounds62Cost : Count :=
  ⟨62 * sha256RoundCost.allocations, 62 * sha256RoundCost.constraints⟩

/-- `ScheduleStepLast` outputs an affine expression (no output decomposition):
58 witnesses, 58 rows. -/
def scheduleStepLastCost : Count := ⟨58, 58⟩
/-- Round 62 with a wide schedule addend: 4×(32,32) + AddManyWide (35,36) +
AddMany2c (33,34). -/
def round62WideCost : Count := ⟨196, 198⟩
/-- Round 63 + Davies-Meyer with two wide adders: 4×(32,32) + 2×AddManyWide. -/
def round63DMWideCost : Count := ⟨198, 200⟩

/-- Wide-absorption (blocks 1-4) per-block cost: 46-step schedule + 2
`ScheduleStepLast` + 62 rounds + `Round62Wide` + `Round63DMWide` + 6 `Add32`. -/
def compressBlockWideCost : Count :=
  ⟨messageScheduleCost46.allocations + 2 * scheduleStepLastCost.allocations +
      sha256Rounds62_pairedCost.allocations + round62WideCost.allocations +
      round63DMWideCost.allocations + 6 * add32Cost.allocations,
   messageScheduleCost46.constraints + 2 * scheduleStepLastCost.constraints +
      sha256Rounds62_pairedCost.constraints + round62WideCost.constraints +
      round63DMWideCost.constraints + 6 * add32Cost.constraints⟩

theorem costIs_messageSchedule46 (block : SHA256Block (Expression (F circomPrime))) :
    CostIs (MessageSchedule.main46 block) messageScheduleCost46 :=
  CostIs.foldlRange (constant := MessageSchedule.constantLength46) (fun _ _ n =>
    (CostIs.bind (costIs_sub_scheduleStep _) fun _ => CostIs.pure _) n)

theorem costIs_sub_messageSchedule46 (b : Var SHA256Block (F circomPrime)) :
    CostIs (subcircuit MessageSchedule.circuit46 b) messageScheduleCost46 :=
  CostIs.subcircuit (costIs_messageSchedule46 _)

theorem costIs_sha256Rounds62 (input : Var SHA256Rounds63.Inputs (F circomPrime)) :
    CostIs (SHA256Rounds63.main62 input) sha256Rounds62Cost :=
  CostIs.foldlRange (fun _ _ n => costIs_sub_sha256Round _ n)

theorem costIs_sub_sha256Rounds62 (b : Var SHA256Rounds63.Inputs (F circomPrime)) :
    CostIs (subcircuit SHA256Rounds63.circuit62 b) sha256Rounds62Cost :=
  CostIs.subcircuit (costIs_sha256Rounds62 _)

theorem costIs_sub_scheduleStepLast (b : Var ScheduleStep.Inputs (F circomPrime)) :
    CostIs (subcircuit ScheduleStepLast.circuit b) scheduleStepLastCost :=
  CostIs.subcircuit (ScheduleStepLast.costIs_main _)

theorem costIs_sub_round62Wide (b : Var Round62Wide.Inputs (F circomPrime)) :
    CostIs (subcircuit Round62Wide.circuit b) round62WideCost :=
  CostIs.subcircuit (Round62Wide.costIs_main _)

theorem costIs_sub_round63DMWide (b : Var Round63DMWide.Inputs (F circomPrime)) :
    CostIs (subcircuit Round63DMWide.circuit b) round63DMWideCost :=
  CostIs.subcircuit (Round63DMWide.costIs_main _)

theorem costIs_compressBlockWide (input : Var CompressBlockWide.Inputs (F circomPrime)) :
    CostIs (CompressBlockWide.main input) compressBlockWideCost :=
  CostIs.bind (costIs_sub_messageSchedule46 _) fun _ =>
  CostIs.bind (costIs_sub_scheduleStepLast _) fun _ =>
  CostIs.bind (costIs_sub_scheduleStepLast _) fun _ =>
  CostIs.bind (costIs_sub_sha256Rounds62_paired _) fun _ =>
  CostIs.bind (costIs_sub_round62Wide _) fun _ =>
  CostIs.bind (costIs_sub_round63DMWide _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ => CostIs.pure _

theorem costIs_sub_compressBlockWide (b : Var CompressBlockWide.Inputs (F circomPrime)) :
    CostIs (subcircuit CompressBlockWide.circuit b) compressBlockWideCost :=
  CostIs.subcircuit (costIs_compressBlockWide _)

theorem affineW_vec5 {a0 a1 a2 a3 a4 : Var (fields 32) (F circomPrime)}
    (h0 : AffineW a0) (h1 : AffineW a1) (h2 : AffineW a2) (h3 : AffineW a3)
    (h4 : AffineW a4) :
    ∀ k : Fin 5,
      AffineW ((#v[a0, a1, a2, a3, a4] :
        Var (ProvableVector (fields 32) 5) (F circomPrime))[k]) := by
  intro k
  fin_cases k
  exacts [h0, h1, h2, h3, h4]

/-- The fused wide adder: 32 output-bit booleanity rows + 3 high-carry booleanity
rows + 1 fused affine low-carry row, all single R1CS rows given affine words and
an affine wide addend. -/
theorem r1cs_addManyWide {n : ℕ} (hn : n ≤ 7)
    (words : Var (ProvableVector (fields 32) n) (F circomPrime)) (wide : Var field (F circomPrime))
    (hwords : ∀ i : Fin n, AffineW words[i]) (hwide : Affine wide) :
    IsR1CSCirc (AddManyWide.addManyWide hn words wide) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun nz =>
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 3 _) fun nc =>
  IsR1CSCirc.bind
    (IsR1CSCirc.forEach fun j m =>
      IsR1CSCirc.assertZero
        (isR1CSRow_mul (affineW_witnessVector_output 32 _ nz j.val j.isLt)
          (Affine.sub (affineW_witnessVector_output 32 _ nz j.val j.isLt) (Affine.const 1))) m)
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.forEach fun j m =>
      IsR1CSCirc.assertZero
        (isR1CSRow_mul (affineW_witnessVector_output 3 _ nc j.val j.isLt)
          (Affine.sub (affineW_witnessVector_output 3 _ nc j.val j.isLt) (Affine.const 1))) m)
    fun _ =>
  let he0 : Affine (((2^32 : F circomPrime)⁻¹ : F circomPrime) *
      (AddMany.sumExpr words + wide - fromBitsExpr ((Circuit.witnessVector 32 fun env =>
        let s := AddManyWide.sumEvalNat env words wide
        Vector.ofFn fun (i : Fin 32) =>
          ((s % 2^32 / 2^i.val % 2 : ℕ) : F circomPrime)).output nz)) -
      AddMany.highExpr ((Circuit.witnessVector 3 fun env =>
        let s := AddManyWide.sumEvalNat env words wide
        Vector.ofFn fun (j : Fin 3) =>
          ((s / 2^32 / 2^(j.val+1) % 2 : ℕ) : F circomPrime)).output nc)) :=
    Affine.sub
      (Affine.fconst_mul _ (Affine.sub
        (Affine.add (affine_sumExpr words hwords) hwide)
        (affine_fieldFromBitsExpr _ (affineW_witnessVector_output 32 _ nz))))
      (affine_highExpr _ (affineW_witnessVector_output 3 _ nc))
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero (isR1CSRow_mul he0 (Affine.sub he0 (Affine.const 1))))
    fun _ => IsR1CSCirc.pure _

theorem affineW_subOut_addManyWide {n : ℕ} (hn : n ≤ 7)
    (b : Var (AddManyWide.Inputs n) (F circomPrime)) (m : ℕ) :
    AffineW ((subcircuit (AddManyWide.circuit hn) b).output m) := by
  intro i hi
  simp only [circuit_norm, subcircuit, AddManyWide.circuit, AddManyWide.elaborated]
  exact Affine.var _

theorem r1cs_sub_addManyWide {n : ℕ} {b : Var (AddManyWide.Inputs n) (F circomPrime)}
    (hn : n ≤ 7) (hwords : ∀ i : Fin n, AffineW b.words[i]) (hwide : Affine b.wide) :
    IsR1CSCirc (subcircuit (AddManyWide.circuit hn) b) :=
  IsR1CSCirc.subcircuit (r1cs_addManyWide hn b.words b.wide hwords hwide)

/-- Round 62 with a wide schedule addend: 4 bitwise gadgets + `AddManyWide` (n=5)
+ `AddMany2c` (n=4). -/
theorem r1cs_round62Wide (b : Var Round62Wide.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW b.state[j]) (hwide : Affine b.wide) :
    IsR1CSCirc (Round62Wide.main b) :=
  IsR1CSCirc.bind_out (r1cs_sub_upperSigma1 _ (hstate 4 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_ch32 _ (hstate 4 (by omega)) (hstate 5 (by omega)) (hstate 6 (by omega))) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_upperSigma0 _ (hstate 0 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_maj32 _ (hstate 0 (by omega)) (hstate 1 (by omega)) (hstate 2 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_addManyWide (by norm_num) (affineW_vec5 (hstate 3 (by omega)) (hstate 7 (by omega))
      (affineW_subOut_upperSigma1 _ _) (affineW_subOut_ch32 _ _) (affineW_constWord32 _)) hwide) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_addMany2c (by norm_num) _ (affineW_vec4
    (affineW_subOut_addManyWide (by norm_num) _ _)
    (affineW_subOut_upperSigma0 _ _) (affineW_subOut_maj32 _ _)
    (affineW_not32 (hstate 3 (by omega))))) fun _ =>
  IsR1CSCirc.pure _

theorem r1cs_round63DMWide (b : Var Round63DMWide.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW b.state[j]) (hwide : Affine b.wide)
    (hs0 : AffineW b.s0) (hs4 : AffineW b.s4) :
    IsR1CSCirc (Round63DMWide.main b) :=
  IsR1CSCirc.bind_out (r1cs_sub_upperSigma1 _ (hstate 4 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_ch32 _ (hstate 4 (by omega)) (hstate 5 (by omega)) (hstate 6 (by omega))) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_upperSigma0 _ (hstate 0 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_maj32 _ (hstate 0 (by omega)) (hstate 1 (by omega)) (hstate 2 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_addManyWide (by norm_num) (affineW_vec6 hs4 (hstate 3 (by omega)) (hstate 7 (by omega))
      (affineW_subOut_upperSigma1 _ _) (affineW_subOut_ch32 _ _) (affineW_constWord32 _)) hwide) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_addManyWide (by norm_num) (affineW_vec7 hs0 (hstate 7 (by omega))
      (affineW_subOut_upperSigma1 _ _) (affineW_subOut_ch32 _ _)
      (affineW_constWord32 _) (affineW_subOut_upperSigma0 _ _)
      (affineW_subOut_maj32 _ _)) hwide) fun _ =>
  IsR1CSCirc.pure _

theorem affineW_subOut_round62Wide (b : Var Round62Wide.Inputs (F circomPrime)) (n : ℕ)
    (hstate : ∀ j (hj : j < 8), AffineW b.state[j]) :
    ∀ j (hj : j < 8), AffineW (((subcircuit Round62Wide.circuit b).output n)[j]) := by
  intro j hj
  simp only [circuit_norm, subcircuit, Round62Wide.circuit, Round62Wide.elaborated]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
  · exact affineW_mapRange_var _
  · exact hstate 0 (by omega)
  · exact hstate 1 (by omega)
  · exact hstate 2 (by omega)
  · exact affineW_mapRange_var _
  · exact hstate 4 (by omega)
  · exact hstate 5 (by omega)
  · exact hstate 6 (by omega)

theorem r1cs_sub_round62Wide (b : Var Round62Wide.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW b.state[j]) (hwide : Affine b.wide) :
    IsR1CSCirc (subcircuit Round62Wide.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_round62Wide _ hstate hwide)

theorem r1cs_sub_round63DMWide (b : Var Round63DMWide.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW b.state[j]) (hwide : Affine b.wide)
    (hs0 : AffineW b.s0) (hs4 : AffineW b.s4) :
    IsR1CSCirc (subcircuit Round63DMWide.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_round63DMWide _ hstate hwide hs0 hs4)

-- `ScheduleStepLast`: the σ-lane rows only (no output decomposition). Same rows
-- as `ScheduleStep` minus the output-bit / carry / fused-adder rows.
set_option maxHeartbeats 1600000 in
theorem r1cs_scheduleStepLast (input : Var ScheduleStep.Inputs (F circomPrime))
    (h2 : AffineW input.wm2) (h7 : AffineW input.wm7)
    (h15 : AffineW input.wm15) (h16 : AffineW input.wm16) :
    IsR1CSCirc (ScheduleStepLast.main input) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 29 _) fun ns0 =>
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 22 _) fun ns1 =>
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 6 _) fun nu =>
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun nv =>
  IsR1CSCirc.bind
    (IsR1CSCirc.forEach fun j m =>
      IsR1CSCirc.assertZero
        (isR1CSRow_sub_mul
          (Affine.sub (Affine.add
              (Affine.fconst_mul _ (affineW_rotr32 h15 j.val (by omega)))
              (Affine.fconst_mul _ (affineW_rotr32 h15 j.val (by omega))))
            (Affine.fconst_mul _ (h15 (j.val + 3) (by omega))))
          (Affine.add (Affine.add
            (Affine.add (affineW_witnessVector_output 29 _ ns0 j.val (by omega))
              (Affine.fconst_mul _ (affineW_rotr32 h15 j.val (by omega))))
            (Affine.fconst_mul _ (affineW_rotr32 h15 j.val (by omega))))
            (Affine.fconst_mul _ (h15 (j.val + 3) (by omega))))
          (Affine.add (Affine.sub (Affine.add (affineW_rotr32 h15 j.val (by omega))
            (affineW_rotr32 h15 j.val (by omega)))
            (Affine.fconst_mul _ (h15 (j.val + 3) (by omega)))) (Affine.const 1))) m)
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.forEach fun j m =>
      IsR1CSCirc.assertZero
        (isR1CSRow_sub_mul
          (Affine.sub (Affine.add
              (Affine.fconst_mul _ (affineW_rotr32 h2 j.val (by omega)))
              (Affine.fconst_mul _ (affineW_rotr32 h2 j.val (by omega))))
            (Affine.fconst_mul _ (h2 (j.val + 10) (by omega))))
          (Affine.add (Affine.add
            (Affine.add (affineW_witnessVector_output 22 _ ns1 j.val (by omega))
              (Affine.fconst_mul _ (affineW_rotr32 h2 j.val (by omega))))
            (Affine.fconst_mul _ (affineW_rotr32 h2 j.val (by omega))))
            (Affine.fconst_mul _ (h2 (j.val + 10) (by omega))))
          (Affine.add (Affine.sub (Affine.add (affineW_rotr32 h2 j.val (by omega))
            (affineW_rotr32 h2 j.val (by omega)))
            (Affine.fconst_mul _ (h2 (j.val + 10) (by omega)))) (Affine.const 1))) m)
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_sub_mul
        (Affine.sub (Affine.sub (Affine.add
            (Affine.sub (Affine.fconst_mul _ (affineW_rotr32 h2 22 (by norm_num)))
              (Affine.fconst_mul _ (affineW_rotr32 h2 22 (by norm_num))))
            (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 24 (by norm_num))
              (affineW_rotr32 h2 24 (by norm_num)))))
          (Affine.const 1)) (affineW_witnessVector_output 6 _ nu 0 (by norm_num)))
        (Affine.sub (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 24 (by norm_num))
            (affineW_rotr32 h2 24 (by norm_num))))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 22 (by norm_num)))
            (affineW_rotr32 h2 22 (by norm_num))))
        (Affine.add (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 24 (by norm_num))
            (affineW_rotr32 h2 24 (by norm_num))))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 22 (by norm_num)))
            (affineW_rotr32 h2 22 (by norm_num))))))
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_sub_mul
        (Affine.sub (Affine.sub (Affine.add
            (Affine.sub (Affine.fconst_mul _ (affineW_rotr32 h2 23 (by norm_num)))
              (Affine.fconst_mul _ (affineW_rotr32 h2 23 (by norm_num))))
            (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 25 (by norm_num))
              (affineW_rotr32 h2 25 (by norm_num)))))
          (Affine.const 1)) (affineW_witnessVector_output 6 _ nu 1 (by norm_num)))
        (Affine.sub (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 25 (by norm_num))
            (affineW_rotr32 h2 25 (by norm_num))))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 23 (by norm_num)))
            (affineW_rotr32 h2 23 (by norm_num))))
        (Affine.add (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 25 (by norm_num))
            (affineW_rotr32 h2 25 (by norm_num))))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 23 (by norm_num)))
            (affineW_rotr32 h2 23 (by norm_num))))))
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_sub_mul
        (Affine.sub (Affine.sub (Affine.add
            (Affine.sub (Affine.fconst_mul _ (affineW_rotr32 h2 26 (by norm_num)))
              (Affine.fconst_mul _ (affineW_rotr32 h2 26 (by norm_num))))
            (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 28 (by norm_num))
              (affineW_rotr32 h2 28 (by norm_num)))))
          (Affine.const 1)) (affineW_witnessVector_output 6 _ nu 2 (by norm_num)))
        (Affine.sub (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 28 (by norm_num))
            (affineW_rotr32 h2 28 (by norm_num))))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 26 (by norm_num)))
            (affineW_rotr32 h2 26 (by norm_num))))
        (Affine.add (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 28 (by norm_num))
            (affineW_rotr32 h2 28 (by norm_num))))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 26 (by norm_num)))
            (affineW_rotr32 h2 26 (by norm_num))))))
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_sub_mul
        (Affine.sub (Affine.sub (Affine.add
            (Affine.sub (Affine.fconst_mul _ (affineW_rotr32 h2 27 (by norm_num)))
              (Affine.fconst_mul _ (affineW_rotr32 h2 27 (by norm_num))))
            (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 29 (by norm_num))
              (affineW_rotr32 h2 29 (by norm_num)))))
          (Affine.const 1)) (affineW_witnessVector_output 6 _ nu 3 (by norm_num)))
        (Affine.sub (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 29 (by norm_num))
            (affineW_rotr32 h2 29 (by norm_num))))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 27 (by norm_num)))
            (affineW_rotr32 h2 27 (by norm_num))))
        (Affine.add (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h2 29 (by norm_num))
            (affineW_rotr32 h2 29 (by norm_num))))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 27 (by norm_num)))
            (affineW_rotr32 h2 27 (by norm_num))))))
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_sub_mul
        (Affine.sub (Affine.sub (Affine.add
            (Affine.sub (Affine.fconst_mul _ (affineW_rotr32 h2 30 (by norm_num)))
              (Affine.fconst_mul _ (affineW_rotr32 h2 30 (by norm_num))))
            (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h15 30 (by norm_num))
              (affineW_rotr32 h15 30 (by norm_num)))))
          (Affine.const 1)) (affineW_witnessVector_output 6 _ nu 4 (by norm_num)))
        (Affine.sub (Affine.add (affineW_rotr32 h15 30 (by norm_num))
            (affineW_rotr32 h15 30 (by norm_num)))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 30 (by norm_num)))
            (affineW_rotr32 h2 30 (by norm_num))))
        (Affine.add (Affine.add (affineW_rotr32 h15 30 (by norm_num))
            (affineW_rotr32 h15 30 (by norm_num)))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 30 (by norm_num)))
            (affineW_rotr32 h2 30 (by norm_num))))))
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_sub_mul
        (Affine.sub (Affine.sub (Affine.add
            (Affine.sub (Affine.fconst_mul _ (affineW_rotr32 h2 31 (by norm_num)))
              (Affine.fconst_mul _ (affineW_rotr32 h2 31 (by norm_num))))
            (Affine.fconst_mul _ (Affine.add (affineW_rotr32 h15 31 (by norm_num))
              (affineW_rotr32 h15 31 (by norm_num)))))
          (Affine.const 1)) (affineW_witnessVector_output 6 _ nu 5 (by norm_num)))
        (Affine.sub (Affine.add (affineW_rotr32 h15 31 (by norm_num))
            (affineW_rotr32 h15 31 (by norm_num)))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 31 (by norm_num)))
            (affineW_rotr32 h2 31 (by norm_num))))
        (Affine.add (Affine.add (affineW_rotr32 h15 31 (by norm_num))
            (affineW_rotr32 h15 31 (by norm_num)))
          (Affine.add (Affine.sub (Affine.const 1) (affineW_rotr32 h2 31 (by norm_num)))
            (affineW_rotr32 h2 31 (by norm_num))))))
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_add_mul
        (Affine.sub (Affine.sub (affine_witnessField_output _ nv)
          (affineW_rotr32 h15 29 (by norm_num))) (affineW_rotr32 h15 29 (by norm_num)))
        (Affine.fconst_mul _ (affineW_rotr32 h15 29 (by norm_num)))
        (affineW_rotr32 h15 29 (by norm_num))))
    fun _ => IsR1CSCirc.pure _

theorem affineW_subOut_scheduleStepLast (b : Var ScheduleStep.Inputs (F circomPrime)) (n : ℕ)
    (h7 : AffineW b.wm7) (h16 : AffineW b.wm16) :
    Affine ((subcircuit ScheduleStepLast.circuit b).output n) := by
  simp only [circuit_norm, subcircuit, ScheduleStepLast.circuit, ScheduleStepLast.elaborated]
  exact Affine.add (Affine.add (affine_fieldFromBitsExpr _ h7) (affine_fieldFromBitsExpr _ h16))
    (affine_fieldFromBitsExpr _ (affineW_tVec _ _ _ _
      (fun i hi => by rw [Vector.getElem_mapRange]; exact Affine.var _)
      (fun i hi => by rw [Vector.getElem_mapRange]; exact Affine.var _)
      (fun i hi => by rw [Vector.getElem_mapRange]; exact Affine.var _)
      (Affine.var _)))

theorem r1cs_sub_scheduleStepLast (b : Var ScheduleStep.Inputs (F circomPrime))
    (h2 : AffineW b.wm2) (h7 : AffineW b.wm7) (h15 : AffineW b.wm15) (h16 : AffineW b.wm16) :
    IsR1CSCirc (subcircuit ScheduleStepLast.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_scheduleStepLast b h2 h7 h15 h16)

theorem r1cs_sha256Rounds62 (input : Var SHA256Rounds63.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW input.state[j])
    (hsched : ∀ k (hk : k < 64), AffineW input.schedule[k]) :
    IsR1CSCirc (SHA256Rounds63.main62 input) := by
  refine IsR1CSCirc.foldlRange_inv (fun s => ∀ j (hj : j < 8), AffineW s[j]) hstate ?_ ?_
  · intro s i hs
    exact IsR1CSCirc.subcircuit
      (r1cs_sha256Round _ _ _ hs (affineW_constWord32 _) (hsched _ (by omega)))
  · intro s i n hs
    exact affineW_sha256Round_output _ n hs

theorem r1cs_sub_sha256Rounds62 (b : Var SHA256Rounds63.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW b.state[j])
    (hsched : ∀ k (hk : k < 64), AffineW b.schedule[k]) :
    IsR1CSCirc (subcircuit SHA256Rounds63.circuit62 b) :=
  IsR1CSCirc.subcircuit (r1cs_sha256Rounds62 _ hstate hsched)

theorem affineW_subOut_sha256Rounds62 (b : Var SHA256Rounds63.Inputs (F circomPrime)) (n : ℕ)
    (hb : ∀ j (hj : j < 8), AffineW b.state[j]) :
    ∀ j (hj : j < 8), AffineW (((subcircuit SHA256Rounds63.circuit62 b).output n)[j]) := by
  intro j hj
  have heq : (subcircuit SHA256Rounds63.circuit62 b).output n
      = SHA256Rounds.stateVar n b.state 62 := by
    simp only [circuit_norm, subcircuit, SHA256Rounds63.circuit62, SHA256Rounds63.elaborated62]
  rw [heq]; exact affineW_stateVar n b.state hb 62 j hj

theorem r1cs_messageSchedule46 (block : SHA256Block (Expression (F circomPrime)))
    (hblock : ∀ k (hk : k < 16), AffineW block[k]) :
    IsR1CSCirc (MessageSchedule.main46 block) := by
  refine IsR1CSCirc.foldlRange_inv (constant := MessageSchedule.constantLength46)
    (fun w => ∀ k (hk : k < 64), AffineW w[k]) ?_ ?_ ?_
  · intro k hk
    show AffineW ((block ++ Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F circomPrime))))[k])
    rw [Vector.getElem_append]
    split
    · exact hblock _ _
    · rw [Vector.getElem_replicate]
      intro j hj
      rw [Vector.getElem_replicate]
      exact Affine.zero (F := F circomPrime)
  · intro w i hw
    exact IsR1CSCirc.bind_out
      (r1cs_sub_scheduleStep _ (hw _ (by omega)) (hw _ (by omega)) (hw _ (by omega)) (hw _ (by omega)))
      (fun _ => IsR1CSCirc.pure _)
  · intro w i n hw k hk
    simp only [circuit_norm, Vector.getElem_set]
    split
    · exact affineW_varFromOffset _ _
    · exact hw _ _

theorem affineW_subOut_messageSchedule46 (b : SHA256Block (Expression (F circomPrime))) (n : ℕ)
    (hb : ∀ k (hk : k < 16), AffineW b[k]) :
    ∀ k (hk : k < 64), AffineW (((subcircuit MessageSchedule.circuit46 b).output n)[k]) := by
  intro k hk
  have heq : (subcircuit MessageSchedule.circuit46 b).output n = MessageSchedule.varSchedule n b 46 := by
    simp only [circuit_norm, subcircuit, MessageSchedule.circuit46, MessageSchedule.elaborated46]
  rw [heq]; exact affineW_varSchedule n b hb 46 k hk

theorem r1cs_sub_messageSchedule46 (b : SHA256Block (Expression (F circomPrime)))
    (hb : ∀ k (hk : k < 16), AffineW b[k]) : IsR1CSCirc (subcircuit MessageSchedule.circuit46 b) :=
  IsR1CSCirc.subcircuit (r1cs_messageSchedule46 _ hb)

set_option maxHeartbeats 1600000 in
theorem r1cs_compressBlockWide (input : Var CompressBlockWide.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW input.state[j])
    (hblock : ∀ k (hk : k < 16), AffineW input.block[k]) :
    IsR1CSCirc (CompressBlockWide.main input) :=
  IsR1CSCirc.bind_out (r1cs_sub_messageSchedule46 _ hblock) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_scheduleStepLast _
      (affineW_subOut_messageSchedule46 _ _ hblock 60 (by norm_num))
      (affineW_subOut_messageSchedule46 _ _ hblock 55 (by norm_num))
      (affineW_subOut_messageSchedule46 _ _ hblock 47 (by norm_num))
      (affineW_subOut_messageSchedule46 _ _ hblock 46 (by norm_num))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_scheduleStepLast _
      (affineW_subOut_messageSchedule46 _ _ hblock 61 (by norm_num))
      (affineW_subOut_messageSchedule46 _ _ hblock 56 (by norm_num))
      (affineW_subOut_messageSchedule46 _ _ hblock 48 (by norm_num))
      (affineW_subOut_messageSchedule46 _ _ hblock 47 (by norm_num))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_sha256Rounds62_paired _ hstate (affineW_subOut_messageSchedule46 _ _ hblock)) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_round62Wide _ (affineW_subOut_sha256Rounds62_paired _ _ hstate)
      (affineW_subOut_scheduleStepLast _ _
        (affineW_subOut_messageSchedule46 _ _ hblock 55 (by norm_num))
        (affineW_subOut_messageSchedule46 _ _ hblock 46 (by norm_num)))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_round63DMWide _ (affineW_subOut_round62Wide _ _ (affineW_subOut_sha256Rounds62_paired _ _ hstate))
      (affineW_subOut_scheduleStepLast _ _
        (affineW_subOut_messageSchedule46 _ _ hblock 56 (by norm_num))
        (affineW_subOut_messageSchedule46 _ _ hblock 47 (by norm_num)))
      (hstate 0 (by omega)) (hstate 4 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (hstate 1 (by omega))
      (affineW_subOut_round62Wide _ _ (affineW_subOut_sha256Rounds62_paired _ _ hstate) 0 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (hstate 2 (by omega))
      (affineW_subOut_round62Wide _ _ (affineW_subOut_sha256Rounds62_paired _ _ hstate) 1 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (hstate 3 (by omega))
      (affineW_subOut_round62Wide _ _ (affineW_subOut_sha256Rounds62_paired _ _ hstate) 2 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (hstate 5 (by omega))
      (affineW_subOut_round62Wide _ _ (affineW_subOut_sha256Rounds62_paired _ _ hstate) 4 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (hstate 6 (by omega))
      (affineW_subOut_round62Wide _ _ (affineW_subOut_sha256Rounds62_paired _ _ hstate) 5 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (hstate 7 (by omega))
      (affineW_subOut_round62Wide _ _ (affineW_subOut_sha256Rounds62_paired _ _ hstate) 6 (by omega))) fun _ =>
  IsR1CSCirc.pure _

/-- The `CompressBlockWide` output is a literal 8-vector whose entries are all
`mapRange` var vectors (two wide-adder outputs and six `Add32` outputs). -/
theorem affineW_subOut_compressBlockWide (input : Var CompressBlockWide.Inputs (F circomPrime)) (n : ℕ) :
    ∀ j (hj : j < 8), AffineW (((subcircuit CompressBlockWide.circuit input).output n)[j]) := by
  intro j hj
  simp only [circuit_norm, subcircuit, CompressBlockWide.circuit, CompressBlockWide.elaborated]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
      exact affineW_mapRange_var _

theorem r1cs_sub_compressBlockWide (b : Var CompressBlockWide.Inputs (F circomPrime))
    (hstate : ∀ j (hj : j < 8), AffineW b.state[j])
    (hblock : ∀ k (hk : k < 16), AffineW b.block[k]) :
    IsR1CSCirc (subcircuit CompressBlockWide.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_compressBlockWide _ hstate hblock)

/-! ### Block 1 (constant IV `H0`) — `CompressBlock1`

Block 1 starts from the constant IV `H0`. `Round0Block1` folds round 0's four
constant bit gadgets into `constWord32`s, leaving only the two fused adders
(`Add32` twice). `Round1Block1` affine-folds `Ch`/`Maj` (no witnesses). Rounds
2/3 (`RoundDHK`) fold the constant `d + h + k` into one addend but keep the same
cost as a generic round in this tree. `circuit62_block1` runs rounds 4..61
uniformly. -/

def round0Block1Cost : Count :=
  ⟨2 * add32Cost.allocations, 2 * add32Cost.constraints⟩

def round1Block1Cost : Count :=
  ⟨2 * sigmaCost.allocations + 2 * addMany2cCost.allocations,
   2 * sigmaCost.constraints + 2 * addMany2cCost.constraints⟩

def roundDHKCost : Count :=
  ⟨2 * sigmaCost.allocations + ch32Cost.allocations + maj32Cost.allocations +
      2 * addMany2cCost.allocations,
   2 * sigmaCost.constraints + ch32Cost.constraints + maj32Cost.constraints +
      2 * addMany2cCost.constraints⟩

def sha256Rounds62Block1Cost : Count :=
  ⟨round0Block1Cost.allocations + round1Block1Cost.allocations + 2 * roundDHKCost.allocations
      + 58 * sha256RoundCost.allocations,
   round0Block1Cost.constraints + round1Block1Cost.constraints + 2 * roundDHKCost.constraints
      + 58 * sha256RoundCost.constraints⟩

def sha256Rounds62Block1_pairedCost : Count :=
  ⟨round0Block1Cost.allocations + round1Block1Cost.allocations
      + 30 * sha256RoundPairCost.allocations,
   round0Block1Cost.constraints + round1Block1Cost.constraints
      + 30 * sha256RoundPairCost.constraints⟩

def compressBlock1Cost : Count :=
  ⟨messageScheduleCost46.allocations + 2 * scheduleStepLastCost.allocations +
      sha256Rounds62Block1_pairedCost.allocations + round62WideCost.allocations +
      round63DMWideCost.allocations + 6 * add32Cost.allocations,
   messageScheduleCost46.constraints + 2 * scheduleStepLastCost.constraints +
      sha256Rounds62Block1_pairedCost.constraints + round62WideCost.constraints +
      round63DMWideCost.constraints + 6 * add32Cost.constraints⟩

theorem costIs_round0Block1 (w : Var (fields 32) (F circomPrime)) :
    CostIs (Round0Block1.main w) round0Block1Cost :=
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ => CostIs.pure _

theorem costIs_sub_round0Block1 (b : Var (fields 32) (F circomPrime)) :
    CostIs (subcircuit Round0Block1.circuit b) round0Block1Cost :=
  CostIs.subcircuit (costIs_round0Block1 b)

theorem costIs_round1Block1 (input : Var Round1Block1.Inputs (F circomPrime)) :
    CostIs (Round1Block1.main input) round1Block1Cost :=
  CostIs.bind (costIs_sub_upperSigma1 _) fun _ =>
  CostIs.bind (costIs_sub_upperSigma0 _) fun _ =>
  CostIs.bind (costIs_sub_addMany2 (n := 4) (by norm_num) _) fun _ =>
  CostIs.bind (costIs_sub_addMany2c (n := 4) (by norm_num) _) fun _ => CostIs.pure _

theorem costIs_sub_round1Block1 (b : Var Round1Block1.Inputs (F circomPrime)) :
    CostIs (subcircuit Round1Block1.circuit b) round1Block1Cost :=
  CostIs.subcircuit (costIs_round1Block1 b)

theorem costIs_roundDHK (P : RoundDHK.Params) (input : Var RoundDHK.Inputs (F circomPrime)) :
    CostIs (RoundDHK.main P input) roundDHKCost :=
  CostIs.bind (costIs_sub_upperSigma1 _) fun _ =>
  CostIs.bind (costIs_sub_ch32 _) fun _ =>
  CostIs.bind (costIs_sub_upperSigma0 _) fun _ =>
  CostIs.bind (costIs_sub_maj32 _) fun _ =>
  CostIs.bind (costIs_sub_addMany2 (n := 4) (by norm_num) _) fun _ =>
  CostIs.bind (costIs_sub_addMany2c (n := 4) (by norm_num) _) fun _ => CostIs.pure _

theorem costIs_sub_roundDHK (P : RoundDHK.Params) (b : Var RoundDHK.Inputs (F circomPrime)) :
    CostIs (subcircuit (RoundDHK.circuit P) b) roundDHKCost :=
  CostIs.subcircuit (costIs_roundDHK P b)

theorem costIs_sha256Rounds62Block1 (input : Var SHA256Schedule (F circomPrime)) :
    CostIs (SHA256Rounds.main62_block1 input) sha256Rounds62Block1Cost :=
  CostIs.bind (costIs_sub_round0Block1 _) fun _ =>
  CostIs.bind (costIs_sub_round1Block1 _) fun _ =>
  CostIs.bind (costIs_sub_roundDHK RoundDHK.params2 _) fun _ =>
  CostIs.bind (costIs_sub_roundDHK RoundDHK.params3 _) fun _ =>
  CostIs.foldlRange (fun _ _ n => costIs_sub_sha256Round _ n)

theorem costIs_sub_sha256Rounds62Block1 (b : Var SHA256Schedule (F circomPrime)) :
    CostIs (subcircuit SHA256Rounds.circuit62_block1 b) sha256Rounds62Block1Cost :=
  CostIs.subcircuit (costIs_sha256Rounds62Block1 _)

theorem costIs_sha256Rounds62Block1_paired (input : Var SHA256Schedule (F circomPrime)) :
    CostIs (SHA256Rounds.main62_block1_paired input) sha256Rounds62Block1_pairedCost :=
  CostIs.bind (costIs_sub_round0Block1 _) fun _ =>
  CostIs.bind (costIs_sub_round1Block1 _) fun _ =>
  CostIs.foldlRange (fun _ _ n => costIs_sub_sha256RoundPair _ n)

theorem costIs_sub_sha256Rounds62Block1_paired (b : Var SHA256Schedule (F circomPrime)) :
    CostIs (subcircuit SHA256Rounds.circuit62_block1_paired b) sha256Rounds62Block1_pairedCost :=
  CostIs.subcircuit (costIs_sha256Rounds62Block1_paired _)

theorem costIs_compressBlock1 (input : Var SHA256Block (F circomPrime)) :
    CostIs (CompressBlock1.main input) compressBlock1Cost :=
  CostIs.bind (costIs_sub_messageSchedule46 _) fun _ =>
  CostIs.bind (costIs_sub_scheduleStepLast _) fun _ =>
  CostIs.bind (costIs_sub_scheduleStepLast _) fun _ =>
  CostIs.bind (costIs_sub_sha256Rounds62Block1_paired _) fun _ =>
  CostIs.bind (costIs_sub_round62Wide _) fun _ =>
  CostIs.bind (costIs_sub_round63DMWide _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ =>
  CostIs.bind (costIs_sub_add32 _) fun _ => CostIs.pure _

theorem costIs_sub_compressBlock1 (b : Var SHA256Block (F circomPrime)) :
    CostIs (subcircuit CompressBlock1.circuit b) compressBlock1Cost :=
  CostIs.subcircuit (costIs_compressBlock1 _)

/-! #### R1CS / affine leaves for block 1 -/

set_option maxHeartbeats 800000 in
theorem affineW_subOut_round0Block1 (b : Var (fields 32) (F circomPrime)) (n : ℕ) :
    ∀ j (hj : j < 8), AffineW (((subcircuit Round0Block1.circuit b).output n)[j]) := by
  intro j hj
  simp only [circuit_norm, subcircuit, Round0Block1.circuit, Round0Block1.elaborated]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
  · exact affineW_mapRange_var _
  · exact affineW_constWord32 _
  · exact affineW_constWord32 _
  · exact affineW_constWord32 _
  · exact affineW_mapRange_var _
  · exact affineW_constWord32 _
  · exact affineW_constWord32 _
  · exact affineW_constWord32 _

theorem degree_constWord32_getElem (m : ℕ) {i : ℕ} (hi : i < 32) :
    degree ((constWord32 m : Var (fields 32) (F circomPrime))[i]) = 0 := by
  unfold constWord32; rw [Vector.getElem_ofFn]; rfl

theorem affineW_chExpr {e : Var (fields 32) (F circomPrime)} (he : AffineW e) (fv gv : ℕ) :
    AffineW (Round1Block1.chExpr e (constWord32 fv) (constWord32 gv)) := by
  intro i hi
  simp only [Round1Block1.chExpr, Affine]
  rw [Vector.getElem_ofFn]
  simp only [Fin.getElem_fin, degree_add, degree_mul, degree_sub, degree_constWord32_getElem _ hi]
  have := he i hi; simp only [Affine] at this
  omega

theorem affineW_majExpr {a : Var (fields 32) (F circomPrime)} (ha : AffineW a) (bv cv : ℕ) :
    AffineW (Round1Block1.majExpr a (constWord32 bv) (constWord32 cv)) := by
  intro i hi
  simp only [Round1Block1.majExpr, Affine]
  rw [Vector.getElem_ofFn]
  simp only [Fin.getElem_fin, degree_add, degree_mul, degree_sub, degree_constWord32_getElem _ hi]
  have := ha i hi; simp only [Affine] at this
  have h2 : degree (2 : Expression (F circomPrime)) = 0 := rfl
  omega

theorem affineW_subOut_round1Block1 (b : Var Round1Block1.Inputs (F circomPrime)) (n : ℕ)
    (ha : AffineW b.a) (he : AffineW b.e) :
    ∀ j (hj : j < 8), AffineW (((subcircuit Round1Block1.circuit b).output n)[j]) := by
  intro j hj
  simp only [circuit_norm, subcircuit, Round1Block1.circuit, Round1Block1.elaborated]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
  · exact affineW_mapRange_var _
  · exact ha
  · exact affineW_constWord32 _
  · exact affineW_constWord32 _
  · exact affineW_mapRange_var _
  · exact he
  · exact affineW_constWord32 _
  · exact affineW_constWord32 _

theorem r1cs_round0Block1 (w : Var (fields 32) (F circomPrime)) (hw : AffineW w) :
    IsR1CSCirc (Round0Block1.main w) :=
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ hw (affineW_constWord32 _)) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (affineW_subOut_add32 _ _) (affineW_constWord32 _)) fun _ =>
  IsR1CSCirc.pure _

theorem r1cs_sub_round0Block1 (b : Var (fields 32) (F circomPrime)) (hb : AffineW b) :
    IsR1CSCirc (subcircuit Round0Block1.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_round0Block1 _ hb)

theorem r1cs_round1Block1 (input : Var Round1Block1.Inputs (F circomPrime))
    (ha : AffineW input.a) (he : AffineW input.e) (hw : AffineW input.w) :
    IsR1CSCirc (Round1Block1.main input) :=
  IsR1CSCirc.bind_out (r1cs_sub_upperSigma1 _ he) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_upperSigma0 _ ha) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_addMany2 (n := 4) (by norm_num) _ (affineW_vec4 (affineW_constWord32 _)
      (affineW_subOut_upperSigma1 _ _) (affineW_chExpr he _ _) hw)) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_addMany2c (n := 4) (by norm_num) _ (affineW_vec4
      (affineW_subOut_addMany2 (by norm_num) _ _)
      (affineW_subOut_upperSigma0 _ _) (affineW_majExpr ha _ _)
      (affineW_not32 (affineW_constWord32 _)))) fun _ =>
  IsR1CSCirc.pure _

theorem r1cs_sub_round1Block1 (b : Var Round1Block1.Inputs (F circomPrime))
    (ha : AffineW b.a) (he : AffineW b.e) (hw : AffineW b.w) :
    IsR1CSCirc (subcircuit Round1Block1.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_round1Block1 _ ha he hw)

theorem r1cs_roundDHK (P : RoundDHK.Params) (input : Var RoundDHK.Inputs (F circomPrime))
    (hstate : ∀ i (hi : i < 8), AffineW input.state[i]) (hw : AffineW input.w) :
    IsR1CSCirc (RoundDHK.main P input) :=
  IsR1CSCirc.bind_out (r1cs_sub_upperSigma1 _ (hstate 4 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_ch32 _ (hstate 4 (by omega)) (hstate 5 (by omega)) (hstate 6 (by omega))) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_upperSigma0 _ (hstate 0 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_maj32 _ (hstate 0 (by omega)) (hstate 1 (by omega)) (hstate 2 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_addMany2 (n := 4) (by norm_num) _ (affineW_vec4 (affineW_constWord32 _)
      (affineW_subOut_upperSigma1 _ _) (affineW_subOut_ch32 _ _) hw)) fun _ =>
  IsR1CSCirc.bind_out (r1cs_sub_addMany2c (n := 4) (by norm_num) _ (affineW_vec4
    (affineW_subOut_addMany2 (by norm_num) _ _)
    (affineW_subOut_upperSigma0 _ _) (affineW_subOut_maj32 _ _)
    (affineW_not32 (affineW_constWord32 _)))) fun _ =>
  IsR1CSCirc.pure _

theorem r1cs_sub_roundDHK (P : RoundDHK.Params) (b : Var RoundDHK.Inputs (F circomPrime))
    (hstate : ∀ i (hi : i < 8), AffineW b.state[i]) (hw : AffineW b.w) :
    IsR1CSCirc (subcircuit (RoundDHK.circuit P) b) :=
  IsR1CSCirc.subcircuit (r1cs_roundDHK P _ hstate hw)

theorem affineW_roundDHK_out_w0 (P : RoundDHK.Params) (input : Var RoundDHK.Inputs (F circomPrime)) (n : ℕ) :
    AffineW (((subcircuit (RoundDHK.circuit P) input).output n)[0]) := by
  simp only [circuit_norm, subcircuit, RoundDHK.circuit, RoundDHK.elaborated]
  exact affineW_mapRange_var _

theorem affineW_roundDHK_out_w4 (P : RoundDHK.Params) (input : Var RoundDHK.Inputs (F circomPrime)) (n : ℕ) :
    AffineW (((subcircuit (RoundDHK.circuit P) input).output n)[4]) := by
  simp only [circuit_norm, subcircuit, RoundDHK.circuit, RoundDHK.elaborated]
  exact affineW_mapRange_var _

theorem affineW_roundDHK_out_w1 (P : RoundDHK.Params) (input : Var RoundDHK.Inputs (F circomPrime)) (n : ℕ)
    (h : AffineW input.state[0]) :
    AffineW (((subcircuit (RoundDHK.circuit P) input).output n)[1]) := by
  simp only [circuit_norm, subcircuit, RoundDHK.circuit, RoundDHK.elaborated]; exact h

theorem affineW_roundDHK_out_w2 (P : RoundDHK.Params) (input : Var RoundDHK.Inputs (F circomPrime)) (n : ℕ)
    (h : AffineW input.state[1]) :
    AffineW (((subcircuit (RoundDHK.circuit P) input).output n)[2]) := by
  simp only [circuit_norm, subcircuit, RoundDHK.circuit, RoundDHK.elaborated]; exact h

theorem affineW_roundDHK_out_w3 (P : RoundDHK.Params) (input : Var RoundDHK.Inputs (F circomPrime)) (n : ℕ)
    (h : AffineW input.state[2]) :
    AffineW (((subcircuit (RoundDHK.circuit P) input).output n)[3]) := by
  simp only [circuit_norm, subcircuit, RoundDHK.circuit, RoundDHK.elaborated]; exact h

theorem affineW_roundDHK_out_w5 (P : RoundDHK.Params) (input : Var RoundDHK.Inputs (F circomPrime)) (n : ℕ)
    (h : AffineW input.state[4]) :
    AffineW (((subcircuit (RoundDHK.circuit P) input).output n)[5]) := by
  simp only [circuit_norm, subcircuit, RoundDHK.circuit, RoundDHK.elaborated]; exact h

theorem affineW_roundDHK_out_w6 (P : RoundDHK.Params) (input : Var RoundDHK.Inputs (F circomPrime)) (n : ℕ)
    (h : AffineW input.state[5]) :
    AffineW (((subcircuit (RoundDHK.circuit P) input).output n)[6]) := by
  simp only [circuit_norm, subcircuit, RoundDHK.circuit, RoundDHK.elaborated]; exact h

theorem affineW_roundDHK_out_w7 (P : RoundDHK.Params) (input : Var RoundDHK.Inputs (F circomPrime)) (n : ℕ)
    (h : AffineW input.state[6]) :
    AffineW (((subcircuit (RoundDHK.circuit P) input).output n)[7]) := by
  simp only [circuit_norm, subcircuit, RoundDHK.circuit, RoundDHK.elaborated]; exact h

theorem affineW_roundDHK_output (P : RoundDHK.Params) (input : Var RoundDHK.Inputs (F circomPrime)) (n : ℕ)
    (hstate : ∀ j (hj : j < 8), AffineW input.state[j]) :
    ∀ j (hj : j < 8), AffineW (((subcircuit (RoundDHK.circuit P) input).output n)[j]) := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact affineW_roundDHK_out_w0 _ _ _
  · exact affineW_roundDHK_out_w1 _ _ _ (hstate 0 (by omega))
  · exact affineW_roundDHK_out_w2 _ _ _ (hstate 1 (by omega))
  · exact affineW_roundDHK_out_w3 _ _ _ (hstate 2 (by omega))
  · exact affineW_roundDHK_out_w4 _ _ _
  · exact affineW_roundDHK_out_w5 _ _ _ (hstate 4 (by omega))
  · exact affineW_roundDHK_out_w6 _ _ _ (hstate 5 (by omega))
  · exact affineW_roundDHK_out_w7 _ _ _ (hstate 6 (by omega))

theorem r1cs_sha256Rounds62Block1 (input : Var SHA256Schedule (F circomPrime))
    (hsched : ∀ k (hk : k < 64), AffineW input[k]) :
    IsR1CSCirc (SHA256Rounds.main62_block1 input) := by
  refine IsR1CSCirc.bind_out (r1cs_sub_round0Block1 _ (hsched 0 (by omega))) fun n => ?_
  refine IsR1CSCirc.bind_out
    (r1cs_sub_round1Block1 _
      (affineW_subOut_round0Block1 _ n 0 (by omega))
      (affineW_subOut_round0Block1 _ n 4 (by omega))
      (hsched 1 (by omega))) fun n2 => ?_
  refine IsR1CSCirc.bind_out
    (r1cs_sub_roundDHK RoundDHK.params2 _
      (affineW_subOut_round1Block1 _ n2
        (affineW_subOut_round0Block1 _ n 0 (by omega))
        (affineW_subOut_round0Block1 _ n 4 (by omega)))
      (hsched 2 (by omega))) fun n3 => ?_
  refine IsR1CSCirc.bind_out
    (r1cs_sub_roundDHK RoundDHK.params3 _
      (affineW_roundDHK_output RoundDHK.params2 _ n3
        (affineW_subOut_round1Block1 _ n2
          (affineW_subOut_round0Block1 _ n 0 (by omega))
          (affineW_subOut_round0Block1 _ n 4 (by omega))))
      (hsched 3 (by omega))) fun n4 => ?_
  refine IsR1CSCirc.foldlRange_inv (fun s => ∀ j (hj : j < 8), AffineW s[j])
    (affineW_roundDHK_output RoundDHK.params3 _ n4
      (affineW_roundDHK_output RoundDHK.params2 _ n3
        (affineW_subOut_round1Block1 _ n2
          (affineW_subOut_round0Block1 _ n 0 (by omega))
          (affineW_subOut_round0Block1 _ n 4 (by omega))))) ?_ ?_
  · intro s i hs
    exact IsR1CSCirc.subcircuit
      (r1cs_sha256Round _ _ _ hs (affineW_constWord32 _) (hsched (i.val + 4) (by omega)))
  · intro s i n' hs
    exact affineW_sha256Round_output _ n' hs

theorem r1cs_sub_sha256Rounds62Block1 (b : Var SHA256Schedule (F circomPrime))
    (hsched : ∀ k (hk : k < 64), AffineW b[k]) :
    IsR1CSCirc (subcircuit SHA256Rounds.circuit62_block1 b) :=
  IsR1CSCirc.subcircuit (r1cs_sha256Rounds62Block1 _ hsched)

set_option maxHeartbeats 3200000 in
theorem affineW_subOut_sha256Rounds62Block1 (b : Var SHA256Schedule (F circomPrime)) (n : ℕ) :
    ∀ j (hj : j < 8), AffineW (((subcircuit SHA256Rounds.circuit62_block1 b).output n)[j]) := by
  intro j hj
  simp only [circuit_norm, subcircuit, SHA256Rounds.circuit62_block1,
    SHA256Rounds.elaborated62_block1, RoundDHK.circuit, RoundDHK.elaborated,
    Round1Block1.circuit, Round1Block1.elaborated,
    Round0Block1.circuit, Round0Block1.elaborated]
  refine affineW_stateVar (n + 64 + 130 + 194 + 194) _ ?_ 58 j hj
  intro j' hj'
  rcases (by omega : j' = 0 ∨ j' = 1 ∨ j' = 2 ∨ j' = 3 ∨ j' = 4 ∨ j' = 5 ∨ j' = 6 ∨ j' = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact affineW_mapRange_var _
theorem affineW_round0Block1_out (b : Var (fields 32) (F circomPrime)) (n : ℕ) :
    ∀ j (hj : j < 8), AffineW ((Round0Block1.circuit.output b n)[j]) := by
  intro j hj
  simp only [circuit_norm, Round0Block1.circuit, Round0Block1.elaborated]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
  · exact affineW_mapRange_var _
  · exact affineW_constWord32 _
  · exact affineW_constWord32 _
  · exact affineW_constWord32 _
  · exact affineW_mapRange_var _
  · exact affineW_constWord32 _
  · exact affineW_constWord32 _
  · exact affineW_constWord32 _

theorem affineW_round1Block1_out (b : Var Round1Block1.Inputs (F circomPrime)) (n : ℕ)
    (ha : AffineW b.a) (he : AffineW b.e) :
    ∀ j (hj : j < 8), AffineW ((Round1Block1.circuit.output b n)[j]) := by
  intro j hj
  simp only [circuit_norm, Round1Block1.circuit, Round1Block1.elaborated]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
  · exact affineW_mapRange_var _
  · exact ha
  · exact affineW_constWord32 _
  · exact affineW_constWord32 _
  · exact affineW_mapRange_var _
  · exact he
  · exact affineW_constWord32 _
  · exact affineW_constWord32 _

theorem r1cs_sha256Rounds62Block1_paired (input : Var SHA256Schedule (F circomPrime))
    (hsched : ∀ k (hk : k < 64), AffineW input[k]) :
    IsR1CSCirc (SHA256Rounds.main62_block1_paired input) := by
  refine IsR1CSCirc.bind_out (r1cs_sub_round0Block1 _ (hsched 0 (by omega))) fun n0 => ?_
  refine IsR1CSCirc.bind_out (r1cs_sub_round1Block1 _
    (affineW_subOut_round0Block1 _ n0 0 (by omega))
    (affineW_subOut_round0Block1 _ n0 4 (by omega))
    (hsched 1 (by omega))) fun n1 => ?_
  refine IsR1CSCirc.foldlRange_inv (fun s => ∀ j (hj : j < 8), AffineW s[j])
    (affineW_subOut_round1Block1 _ n1
      (affineW_subOut_round0Block1 _ n0 0 (by omega))
      (affineW_subOut_round0Block1 _ n0 4 (by omega))) ?_ ?_
  · intro s i hs
    exact r1cs_sub_sha256RoundPair _ hs (affineW_constWord32 _) (hsched (2*i.val+2) (by omega))
      (affineW_constWord32 _) (hsched (2*i.val+3) (by omega))
  · intro s i n' hs
    exact affineW_subOut_sha256RoundPair _ n' hs

theorem r1cs_sub_sha256Rounds62Block1_paired (b : Var SHA256Schedule (F circomPrime))
    (hsched : ∀ k (hk : k < 64), AffineW b[k]) :
    IsR1CSCirc (subcircuit SHA256Rounds.circuit62_block1_paired b) :=
  IsR1CSCirc.subcircuit (r1cs_sha256Rounds62Block1_paired _ hsched)

-- Keep the folded-round subcircuit bodies opaque so `circuit_norm` does not reduce
-- the nested `Round0`/`Round1` circuit outputs (which is a pathological `whnf`).
attribute [local irreducible] Round0Block1.circuit Round1Block1.circuit

set_option maxHeartbeats 800000 in
theorem affineW_subOut_sha256Rounds62Block1_paired (b : Var SHA256Schedule (F circomPrime)) (n : ℕ) :
    ∀ j (hj : j < 8), AffineW (((subcircuit SHA256Rounds.circuit62_block1_paired b).output n)[j]) := by
  intro j hj
  simp only [circuit_norm, subcircuit, SHA256Rounds.circuit62_block1_paired,
    SHA256Rounds.elaborated62_block1_paired]
  exact affineW_stateVarPaired (n + 64 + 130) _
    (affineW_round1Block1_out _ (n + 64)
      (affineW_round0Block1_out (b[0]'(by norm_num)) n 0 (by omega))
      (affineW_round0Block1_out (b[0]'(by norm_num)) n 4 (by omega))) 30 j hj


set_option maxHeartbeats 800000 in
theorem r1cs_compressBlock1 (input : Var SHA256Block (F circomPrime))
    (hblock : ∀ k (hk : k < 16), AffineW input[k]) :
    IsR1CSCirc (CompressBlock1.main input) :=
  IsR1CSCirc.bind_out (r1cs_sub_messageSchedule46 _ hblock) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_scheduleStepLast _
      (affineW_subOut_messageSchedule46 _ _ hblock 60 (by norm_num))
      (affineW_subOut_messageSchedule46 _ _ hblock 55 (by norm_num))
      (affineW_subOut_messageSchedule46 _ _ hblock 47 (by norm_num))
      (affineW_subOut_messageSchedule46 _ _ hblock 46 (by norm_num))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_scheduleStepLast _
      (affineW_subOut_messageSchedule46 _ _ hblock 61 (by norm_num))
      (affineW_subOut_messageSchedule46 _ _ hblock 56 (by norm_num))
      (affineW_subOut_messageSchedule46 _ _ hblock 48 (by norm_num))
      (affineW_subOut_messageSchedule46 _ _ hblock 47 (by norm_num))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_sha256Rounds62Block1_paired _ (affineW_subOut_messageSchedule46 _ _ hblock)) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_round62Wide _ (affineW_subOut_sha256Rounds62Block1_paired _ _)
      (affineW_subOut_scheduleStepLast _ _
        (affineW_subOut_messageSchedule46 _ _ hblock 55 (by norm_num))
        (affineW_subOut_messageSchedule46 _ _ hblock 46 (by norm_num)))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_round63DMWide _ (affineW_subOut_round62Wide _ _ (affineW_subOut_sha256Rounds62Block1_paired _ _))
      (affineW_subOut_scheduleStepLast _ _
        (affineW_subOut_messageSchedule46 _ _ hblock 56 (by norm_num))
        (affineW_subOut_messageSchedule46 _ _ hblock 47 (by norm_num)))
      (affineW_constWord32 _) (affineW_constWord32 _)) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (affineW_constWord32 _)
      (affineW_subOut_round62Wide _ _ (affineW_subOut_sha256Rounds62Block1_paired _ _) 0 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (affineW_constWord32 _)
      (affineW_subOut_round62Wide _ _ (affineW_subOut_sha256Rounds62Block1_paired _ _) 1 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (affineW_constWord32 _)
      (affineW_subOut_round62Wide _ _ (affineW_subOut_sha256Rounds62Block1_paired _ _) 2 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (affineW_constWord32 _)
      (affineW_subOut_round62Wide _ _ (affineW_subOut_sha256Rounds62Block1_paired _ _) 4 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (affineW_constWord32 _)
      (affineW_subOut_round62Wide _ _ (affineW_subOut_sha256Rounds62Block1_paired _ _) 5 (by omega))) fun _ =>
  IsR1CSCirc.bind_out
    (r1cs_sub_add32 _ (affineW_constWord32 _)
      (affineW_subOut_round62Wide _ _ (affineW_subOut_sha256Rounds62Block1_paired _ _) 6 (by omega))) fun _ =>
  IsR1CSCirc.pure _

theorem r1cs_sub_compressBlock1 (b : Var SHA256Block (F circomPrime))
    (hblock : ∀ k (hk : k < 16), AffineW b[k]) :
    IsR1CSCirc (subcircuit CompressBlock1.circuit b) :=
  IsR1CSCirc.subcircuit (r1cs_compressBlock1 _ hblock)

theorem affineW_subOut_compressBlock1 (input : Var SHA256Block (F circomPrime)) (n : ℕ) :
    ∀ j (hj : j < 8), AffineW (((subcircuit CompressBlock1.circuit input).output n)[j]) := by
  intro j hj
  simp only [circuit_norm, subcircuit, CompressBlock1.circuit, CompressBlock1.elaborated]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [List.getElem_cons_zero, List.getElem_cons_succ]
    exact affineW_mapRange_var _

end Cost

end Solution.SHA256
