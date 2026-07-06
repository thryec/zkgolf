import Solution.SHA256.SHA256Rounds
import Solution.SHA256.MessageSchedule
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)] [Fact (p > 2^76)]

namespace Solution.SHA256

/-!
# SHA-256 Full Block Compression

Composes the message schedule with the fused 63-round + final-round +
Davies-Meyer compression (`SHA256Rounds.circuit` now includes the Davies-Meyer
feedforward add internally, with round 63's `new_a`/`new_e` fused into the
word-0/word-4 feedforward adders).

This file builds the `FormalCircuit`:
  * `CompressBlock.circuit`    — message schedule + fused compression
-/

namespace CompressBlock

structure Inputs (F : Type) where
  state : SHA256State F
  block : SHA256Block F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) := do
  let w ← MessageSchedule.circuit input.block
  SHA256Rounds.circuit ⟨input.state, w⟩

instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State main := by
  elaborate_circuit

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧
  (∀ i : Fin 16, Normalized input.block[i])

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    Specs.SHA256.compressBlock (input.state.map valueBits) (input.block.map valueBits)
  ∧ ∀ i : Fin 8, Normalized out[i]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [MessageSchedule.circuit, MessageSchedule.Spec, MessageSchedule.Assumptions]
  simp only [circuit_norm, SHA256Rounds.circuit, SHA256Rounds.Spec,
    SHA256Rounds.Assumptions] at h_holds
  obtain ⟨h_state_norm, h_block_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_block⟩ := h_input
  obtain ⟨h_sched, h_rounds⟩ := h_holds
  have h_sched_full := h_sched h_block_norm
  have h_sched_val := fun i => (h_sched_full i).1
  have h_sched_norm := fun i => (h_sched_full i).2
  have h_rounds_full := h_rounds ⟨h_state_norm, h_sched_norm⟩
  obtain ⟨h_rounds_val, h_rounds_norm⟩ := h_rounds_full
  have h_sched_map :
      Vector.map valueBits (eval env (MessageSchedule.varSchedule i₀ input_var_block 48))
        = Specs.SHA256.messageSchedule (Vector.map valueBits input_block) := by
    ext j hj
    simp only [Vector.getElem_map]
    exact h_sched_val ⟨j, hj⟩
  refine ⟨⟨?_, h_rounds_norm⟩, Or.inr ⟨h_state_norm, h_sched_norm⟩⟩
  rw [h_rounds_val, h_sched_map]
  simp only [Specs.SHA256.compressBlock, Vector.getElem_map, Fin.getElem_fin]

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [MessageSchedule.circuit, MessageSchedule.Spec, MessageSchedule.Assumptions]
  simp only [circuit_norm, SHA256Rounds.circuit, SHA256Rounds.Spec,
    SHA256Rounds.Assumptions] at h_env ⊢
  obtain ⟨h_state_norm, h_block_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_block⟩ := h_input
  obtain ⟨h_sched_impl, -⟩ := h_env
  have h_sched_full := h_sched_impl h_block_norm
  have h_sched_norm := fun i => (h_sched_full i).2
  exact ⟨h_block_norm, h_state_norm, h_sched_norm⟩

def circuit : FormalCircuit (F p) Inputs SHA256State := {
  main, elaborated, Assumptions, Spec, soundness
  completeness := by simp only [completeness]
}

end CompressBlock
end Solution.SHA256
end
