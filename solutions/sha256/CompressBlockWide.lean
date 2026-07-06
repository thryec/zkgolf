import Solution.SHA256.SHA256Rounds
import Solution.SHA256.MessageSchedule
import Solution.SHA256.Add32
import Solution.SHA256.Round63DM
import Solution.SHA256.Round62Wide
import Solution.SHA256.Round63DMWide
import Solution.SHA256.ScheduleStepLast
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)] [Fact (p > 2^37)] [Fact (p > 2^76)]

namespace Solution.SHA256

/-!
# SHA-256 Full Block Compression with w62/w63 wide absorption (blocks 1-4)

Ported from bufferhe4d's 166,935 submission
(`/Users/simon/Documents/dev/Projects/zk.golf/solutions/sha-bufferhe4d-166935/CompressBlock.lean`),
credit to bufferhe4d for the w62/w63 wide-absorption design.

Composes the 46-step message schedule, two `ScheduleStepLast` gadgets producing
the *unreduced* schedule words 62/63, 62 uniform rounds, then the two fused wide
rounds (`Round62Wide` for round 62, `Round63DMWide` for round 63 + Davies-Meyer),
and six plain `Add32` feed-forward additions for the remaining words. Skipping the
w62/w63 bit-decompositions is the cost win over our existing `CompressBlock`
(which this module does not replace — kept as a separate module so
`CompressBlock`'s existing verified proofs are untouched; `Main.lean` switches
blocks 1-4 to this module's `circuit` and leaves block 5's `CompressBlock5` path
unchanged, since block 5 never calls `MessageSchedule` at all).

The `Inputs` / `Assumptions` / `Spec` shapes are IDENTICAL to `CompressBlock`.
-/

namespace CompressBlockWide

structure Inputs (F : Type) where
  state : SHA256State F
  block : SHA256Block F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) := do
  let w ← MessageSchedule.circuit46 input.block
  let E62 ← ScheduleStepLast.circuit ⟨w[60], w[55], w[47], w[46]⟩
  let E63 ← ScheduleStepLast.circuit ⟨w[61], w[56], w[48], w[47]⟩
  let st62 ← SHA256Rounds63.circuit62_paired ⟨input.state, w⟩
  let st63 ← Round62Wide.circuit ⟨st62, E62⟩
  let o ← Round63DMWide.circuit ⟨st63, E63, input.state[0], input.state[4]⟩
  let r1 ← Add32.circuit ⟨input.state[1], st63[0]⟩
  let r2 ← Add32.circuit ⟨input.state[2], st63[1]⟩
  let r3 ← Add32.circuit ⟨input.state[3], st63[2]⟩
  let r5 ← Add32.circuit ⟨input.state[5], st63[4]⟩
  let r6 ← Add32.circuit ⟨input.state[6], st63[5]⟩
  let r7 ← Add32.circuit ⟨input.state[7], st63[6]⟩
  return #v[o.out0, r1, r2, r3, o.out4, r5, r6, r7]

instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State main := by
  elaborate_circuit

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧
  (∀ i : Fin 16, Normalized input.block[i])

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    Specs.SHA256.compressBlock (input.state.map valueBits) (input.block.map valueBits)
  ∧ ∀ i : Fin 8, Normalized out[i]

set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [ScheduleStepLast.Spec, ScheduleStepLast.Assumptions,
    MessageSchedule.Spec46, MessageSchedule.Assumptions,
    SHA256Rounds63.Spec62, SHA256Rounds63.Assumptions62,
    Round62Wide.Spec, Round62Wide.Assumptions,
    Round63DMWide.Spec, Round63DMWide.Assumptions,
    Add32.circuit, Add32.Spec, Add32.Assumptions]
  obtain ⟨h_state_norm, h_block_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_block⟩ := h_input
  obtain ⟨h_sched, h_E62, h_E63, h_st62, h_st63, h_o, h_a1, h_a2, h_a3, h_a5, h_a6, h_a7⟩ := h_holds
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env V)[k]'hk = Vector.map (Expression.eval env) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env V k hk, CircuitType.eval_var_fields]
  have h_eval : ∀ (i : ℕ) (hi : i < 8),
      Vector.map (Expression.eval env) (input_var_state[i]'hi) = input_state[i]'hi := by
    intro i hi
    rw [← red 8 input_var_state i hi, h_input_state]
  have h_sched_full : MessageSchedule.Spec46 input_block (eval env (MessageSchedule.circuit46.output input_var_block i₀)) := h_sched h_block_norm
  simp only [MessageSchedule.Spec46] at h_sched_full
  have hval : ∀ (j : ℕ) (hj : j < 62),
      valueBits (Vector.map (Expression.eval env)
        ((MessageSchedule.circuit46.output input_var_block i₀)[j]'(by omega))) =
        (Specs.SHA256.messageSchedule (Vector.map valueBits input_block))[j]'(by omega) := by
    intro j hj
    rw [← red 64 (MessageSchedule.circuit46.output input_var_block i₀) j (by omega)]
    exact (h_sched_full ⟨j, by omega⟩ hj).1
  have hnorm : ∀ (j : ℕ) (hj : j < 62),
      Normalized (Vector.map (Expression.eval env)
        ((MessageSchedule.circuit46.output input_var_block i₀)[j]'(by omega))) := by
    intro j hj
    rw [← red 64 (MessageSchedule.circuit46.output input_var_block i₀) j (by omega)]
    exact (h_sched_full ⟨j, by omega⟩ hj).2
  obtain ⟨hE62_val, hE62_bound⟩ := h_E62 ⟨hnorm 60 (by norm_num), hnorm 55 (by norm_num),
    hnorm 47 (by norm_num), hnorm 46 (by norm_num)⟩
  obtain ⟨hE63_val, hE63_bound⟩ := h_E63 ⟨hnorm 61 (by norm_num), hnorm 56 (by norm_num),
    hnorm 48 (by norm_num), hnorm 47 (by norm_num)⟩
  obtain ⟨hst62_val, hst62_norm⟩ := h_st62 ⟨h_state_norm, fun i hi => (h_sched_full i hi).2⟩
  have hcong : SHA256Rounds.valStateAfterRound (Vector.map valueBits input_state)
        (Vector.map valueBits (eval env (MessageSchedule.circuit46.output input_var_block i₀))) 62 =
      SHA256Rounds.valStateAfterRound (Vector.map valueBits input_state)
        (Specs.SHA256.messageSchedule (Vector.map valueBits input_block)) 62 := by
    apply SHA256Rounds.valStateAfterRound_congr _ _ _ 62 (by norm_num)
    intro j hj hlt
    rw [Vector.getElem_map]
    exact (h_sched_full ⟨j, by omega⟩ hlt).1
  rw [hcong] at hst62_val
  obtain ⟨hst63_val, hst63_norm⟩ := h_st63 ⟨hst62_norm, hE62_bound⟩
  conv at hst63_val => rhs; rw [hst62_val]
  rw [hE62_val, hval 60 (by norm_num), hval 55 (by norm_num), hval 47 (by norm_num),
    hval 46 (by norm_num), ← MessageSchedule.messageSchedule_getElem_62 (Vector.map valueBits input_block)]
    at hst63_val
  have hs0n : Normalized (Vector.map (Expression.eval env) input_var_state[0]) := by
    rw [h_eval 0 (by norm_num)]; exact h_state_norm 0
  have hs4n : Normalized (Vector.map (Expression.eval env) input_var_state[4]) := by
    rw [h_eval 4 (by norm_num)]; exact h_state_norm 4
  obtain ⟨ho_v0, ho_v4, ho_n0, ho_n4⟩ := h_o ⟨hst63_norm, hs0n, hs4n, hE63_bound⟩
  rw [hst63_val] at ho_v0 ho_v4
  rw [hE63_val, hval 61 (by norm_num), hval 56 (by norm_num), hval 48 (by norm_num),
    hval 47 (by norm_num), ← MessageSchedule.messageSchedule_getElem_63 (Vector.map valueBits input_block),
    ← SHA256Rounds.sha256Compress_split_last2 (Vector.map valueBits input_state)
      (Specs.SHA256.messageSchedule (Vector.map valueBits input_block))] at ho_v0 ho_v4
  simp only [h_eval 0 (by norm_num)] at ho_v0
  simp only [h_eval 4 (by norm_num)] at ho_v4
  obtain ⟨ha1_val, ha1_norm⟩ := h_a1 ⟨by rw [h_eval 1 (by norm_num)]; exact h_state_norm 1,
    by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst63_norm ⟨0, by norm_num⟩⟩
  obtain ⟨ha2_val, ha2_norm⟩ := h_a2 ⟨by rw [h_eval 2 (by norm_num)]; exact h_state_norm 2,
    by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst63_norm ⟨1, by norm_num⟩⟩
  obtain ⟨ha3_val, ha3_norm⟩ := h_a3 ⟨by rw [h_eval 3 (by norm_num)]; exact h_state_norm 3,
    by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst63_norm ⟨2, by norm_num⟩⟩
  obtain ⟨ha5_val, ha5_norm⟩ := h_a5 ⟨by rw [h_eval 5 (by norm_num)]; exact h_state_norm 5,
    by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst63_norm ⟨4, by norm_num⟩⟩
  obtain ⟨ha6_val, ha6_norm⟩ := h_a6 ⟨by rw [h_eval 6 (by norm_num)]; exact h_state_norm 6,
    by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst63_norm ⟨5, by norm_num⟩⟩
  obtain ⟨ha7_val, ha7_norm⟩ := h_a7 ⟨by rw [h_eval 7 (by norm_num)]; exact h_state_norm 7,
    by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst63_norm ⟨6, by norm_num⟩⟩
  simp only [h_eval 1 (by norm_num)] at ha1_val
  simp only [h_eval 2 (by norm_num)] at ha2_val
  simp only [h_eval 3 (by norm_num)] at ha3_val
  simp only [h_eval 5 (by norm_num)] at ha5_val
  simp only [h_eval 6 (by norm_num)] at ha6_val
  simp only [h_eval 7 (by norm_num)] at ha7_val
  have hL46 : ∀ (b : SHA256Block (Expression (F p))),
      (MessageSchedule.circuit46).localLength b = 4186 := fun b => by
    simp only [circuit_norm, MessageSchedule.circuit46, MessageSchedule.elaborated46]
  have hL58 : ∀ (b : ScheduleStep.Inputs (Expression (F p))),
      ScheduleStepLast.circuit.localLength b = 58 := fun b => by
    simp only [circuit_norm, ScheduleStepLast.circuit, ScheduleStepLast.elaborated]
  have hL62 : ∀ (b : SHA256Rounds63.Inputs (Expression (F p))),
      SHA256Rounds63.circuit62_paired.localLength b = 10168 := fun b => by
    simp only [circuit_norm, SHA256Rounds63.circuit62_paired, SHA256Rounds63.elaborated62_paired]
  have hL196 : ∀ (b : Round62Wide.Inputs (Expression (F p))),
      Round62Wide.circuit.localLength b = 196 := fun b => by
    simp only [circuit_norm, Round62Wide.circuit, Round62Wide.elaborated]
  have hL198 : ∀ (b : Round63DMWide.Inputs (Expression (F p))),
      Round63DMWide.circuit.localLength b = 198 := fun b => by
    simp only [circuit_norm, Round63DMWide.circuit, Round63DMWide.elaborated]
  have hR63o0 : ∀ (a : Round63DMWide.Inputs (Expression (F p))) (n : ℕ),
      (Round63DMWide.circuit.output a n).out0 = Vector.mapRange 32 (fun i => var { index := n + 32 + 32 + 32 + 32 + 35 + i }) := fun a n => by
    simp only [circuit_norm, Round63DMWide.circuit, Round63DMWide.elaborated]
  have hR63o4 : ∀ (a : Round63DMWide.Inputs (Expression (F p))) (n : ℕ),
      (Round63DMWide.circuit.output a n).out4 = Vector.mapRange 32 (fun i => var { index := n + 32 + 32 + 32 + 32 + i }) := fun a n => by
    simp only [circuit_norm, Round63DMWide.circuit, Round63DMWide.elaborated]
  have hAdd32o : ∀ (a : Add32.Inputs (Expression (F p))) (n : ℕ),
      Add32.circuit.output a n = Vector.mapRange 32 (fun i => var { index := n + i }) := fun a n => by
    simp only [circuit_norm, Add32.circuit, Add32.elaborated]
  simp only [hL46, hL58, hL62, hL196, hL198, hR63o0, hR63o4, hAdd32o] at ho_v0 ho_v4 ha1_val ha2_val ha3_val ha5_val ha6_val ha7_val ho_n0 ho_n4 ha1_norm ha2_norm ha3_norm ha5_norm ha6_norm ha7_norm
  simp only [← CircuitType.eval_var_fields] at ho_v0 ho_v4 ha1_val ha2_val ha3_val ha5_val ha6_val ha7_val
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Vector.ext
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [SHA256Rounds.compressBlock_getElem _ _ 0 (by norm_num)]
      simp only [Vector.getElem_map, ← getElem_eval_vector,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
      exact ho_v0
    · rw [SHA256Rounds.compressBlock_getElem _ _ 1 (by norm_num),
        SHA256Rounds.sha256Compress_split_last2, Round63DM.sha256Round_eq, Round63DM.vec8_getElem1,
        ← hst63_val]
      simp only [Vector.getElem_map, ← getElem_eval_vector,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, _root_.add32]
      exact ha1_val
    · rw [SHA256Rounds.compressBlock_getElem _ _ 2 (by norm_num),
        SHA256Rounds.sha256Compress_split_last2, Round63DM.sha256Round_eq, Round63DM.vec8_getElem2,
        ← hst63_val]
      simp only [Vector.getElem_map, ← getElem_eval_vector,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, _root_.add32]
      exact ha2_val
    · rw [SHA256Rounds.compressBlock_getElem _ _ 3 (by norm_num),
        SHA256Rounds.sha256Compress_split_last2, Round63DM.sha256Round_eq, Round63DM.vec8_getElem3,
        ← hst63_val]
      simp only [Vector.getElem_map, ← getElem_eval_vector,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, _root_.add32]
      exact ha3_val
    · rw [SHA256Rounds.compressBlock_getElem _ _ 4 (by norm_num)]
      simp only [Vector.getElem_map, ← getElem_eval_vector,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
      exact ho_v4
    · rw [SHA256Rounds.compressBlock_getElem _ _ 5 (by norm_num),
        SHA256Rounds.sha256Compress_split_last2, Round63DM.sha256Round_eq, Round63DM.vec8_getElem5,
        ← hst63_val]
      simp only [Vector.getElem_map, ← getElem_eval_vector,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, _root_.add32]
      exact ha5_val
    · rw [SHA256Rounds.compressBlock_getElem _ _ 6 (by norm_num),
        SHA256Rounds.sha256Compress_split_last2, Round63DM.sha256Round_eq, Round63DM.vec8_getElem6,
        ← hst63_val]
      simp only [Vector.getElem_map, ← getElem_eval_vector,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, _root_.add32]
      exact ha6_val
    · rw [SHA256Rounds.compressBlock_getElem _ _ 7 (by norm_num),
        SHA256Rounds.sha256Compress_split_last2, Round63DM.sha256Round_eq, Round63DM.vec8_getElem7,
        ← hst63_val]
      simp only [Vector.getElem_map, ← getElem_eval_vector,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, _root_.add32]
      exact ha7_val
  · intro i
    obtain ⟨i, hi⟩ := i
    simp only [Fin.val_mk]
    rw [red 8 _ i hi]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · exact ho_n0
    · exact ha1_norm
    · exact ha2_norm
    · exact ha3_norm
    · exact ho_n4
    · exact ha5_norm
    · exact ha6_norm
    · exact ha7_norm
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [ScheduleStepLast.Spec, ScheduleStepLast.Assumptions,
    MessageSchedule.Spec46, MessageSchedule.Assumptions,
    SHA256Rounds63.Spec62, SHA256Rounds63.Assumptions62,
    Round62Wide.Spec, Round62Wide.Assumptions,
    Round63DMWide.Spec, Round63DMWide.Assumptions,
    Add32.circuit, Add32.Spec, Add32.Assumptions]
  obtain ⟨h_state_norm, h_block_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_block⟩ := h_input
  obtain ⟨h_sched_impl, h_E62_impl, h_E63_impl, h_st62_impl, h_st63_impl, h_o_impl, _⟩ := h_env
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env.toEnvironment V)[k]'hk = Vector.map (Expression.eval env.toEnvironment) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env.toEnvironment V k hk, CircuitType.eval_var_fields]
  have h_eval : ∀ (i : ℕ) (hi : i < 8),
      Vector.map (Expression.eval env.toEnvironment) (input_var_state[i]'hi) = input_state[i]'hi := by
    intro i hi
    rw [← red 8 input_var_state i hi, h_input_state]
  have h_sched_full : MessageSchedule.Spec46 input_block
      (eval env.toEnvironment (MessageSchedule.circuit46.output input_var_block i₀)) :=
    h_sched_impl h_block_norm
  simp only [MessageSchedule.Spec46] at h_sched_full
  have hnorm : ∀ (j : ℕ) (hj : j < 62),
      Normalized (Vector.map (Expression.eval env.toEnvironment)
        ((MessageSchedule.circuit46.output input_var_block i₀)[j]'(by omega))) := by
    intro j hj
    rw [← red 64 (MessageSchedule.circuit46.output input_var_block i₀) j (by omega)]
    exact (h_sched_full ⟨j, by omega⟩ hj).2
  have hsched_norm := fun (i : Fin 64) (hi : i.val < 62) => (h_sched_full i hi).2
  obtain ⟨_, hE62_bound⟩ := h_E62_impl ⟨hnorm 60 (by norm_num), hnorm 55 (by norm_num),
    hnorm 47 (by norm_num), hnorm 46 (by norm_num)⟩
  obtain ⟨_, hE63_bound⟩ := h_E63_impl ⟨hnorm 61 (by norm_num), hnorm 56 (by norm_num),
    hnorm 48 (by norm_num), hnorm 47 (by norm_num)⟩
  obtain ⟨_, hst62_norm⟩ := h_st62_impl ⟨h_state_norm, hsched_norm⟩
  obtain ⟨_, hst63_norm⟩ := h_st63_impl ⟨hst62_norm, hE62_bound⟩
  have hs0n : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[0]) := by
    rw [h_eval 0 (by norm_num)]; exact h_state_norm 0
  have hs4n : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[4]) := by
    rw [h_eval 4 (by norm_num)]; exact h_state_norm 4
  refine ⟨h_block_norm,
    ⟨hnorm 60 (by norm_num), hnorm 55 (by norm_num), hnorm 47 (by norm_num), hnorm 46 (by norm_num)⟩,
    ⟨hnorm 61 (by norm_num), hnorm 56 (by norm_num), hnorm 48 (by norm_num), hnorm 47 (by norm_num)⟩,
    ⟨h_state_norm, hsched_norm⟩,
    ⟨hst62_norm, hE62_bound⟩,
    ⟨hst63_norm, hs0n, hs4n, hE63_bound⟩,
    ⟨by rw [h_eval 1 (by norm_num)]; exact h_state_norm 1,
      by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst63_norm ⟨0, by norm_num⟩⟩,
    ⟨by rw [h_eval 2 (by norm_num)]; exact h_state_norm 2,
      by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst63_norm ⟨1, by norm_num⟩⟩,
    ⟨by rw [h_eval 3 (by norm_num)]; exact h_state_norm 3,
      by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst63_norm ⟨2, by norm_num⟩⟩,
    ⟨by rw [h_eval 5 (by norm_num)]; exact h_state_norm 5,
      by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst63_norm ⟨4, by norm_num⟩⟩,
    ⟨by rw [h_eval 6 (by norm_num)]; exact h_state_norm 6,
      by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst63_norm ⟨5, by norm_num⟩⟩,
    ⟨by rw [h_eval 7 (by norm_num)]; exact h_state_norm 7,
      by rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact hst63_norm ⟨6, by norm_num⟩⟩⟩

def circuit : FormalCircuit (F p) Inputs SHA256State := {
  main, elaborated, Assumptions, Spec, soundness
  completeness := by simp only [completeness]
}

end CompressBlockWide
end Solution.SHA256
end
