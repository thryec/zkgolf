import Solution.SHA256.Block5Schedule
import Solution.SHA256.SHA256Rounds
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)] [Fact (p > 2^76)]

namespace Solution.SHA256
namespace CompressBlock5

open Challenge.Instances.SHA256.Interface (inputBufferLen)

structure Inputs (F : Type) where
  messageLen : F
  lenFlags : fields inputBufferLen F
  state : SHA256State F
deriving ProvableStruct

/-- Block-5 compression with the length-only schedule wired directly into the
fused compression (`SHA256Rounds`, which now includes the Davies-Meyer
feedforward add). -/
def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) :=
  SHA256Rounds.circuit ⟨input.state, block5Schedule input.lenFlags⟩

instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State main := by
  elaborate_circuit

def Assumptions (input : Inputs (F p)) : Prop :=
  input.messageLen.val < inputBufferLen ∧
  OneHotAt input.lenFlags input.messageLen.val ∧
  (∀ i : Fin 8, Normalized input.state[i])

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    Specs.SHA256.compressBlock (input.state.map valueBits)
      (block5SpecBlock input.messageLen.val)
  ∧ ∀ i : Fin 8, Normalized out[i]

omit [Fact (p > 2 ^ 35)] in
/-- The block-5 schedule words are all normalized (each bit is affine one-hot). -/
theorem sched_norm (env : Environment (F p)) (flags : Var (fields inputBufferLen) (F p))
    (ℓ : ℕ) (hℓ : ℓ < inputBufferLen)
    (honehot : OneHotAt (Vector.map (Expression.eval env) flags) ℓ) :
    ∀ i : Fin 64, Normalized (eval env (block5Schedule flags))[i.val] := by
  intro i
  have hget :
      (eval env (block5Schedule flags))[i.val]'i.isLt =
        Vector.map (Expression.eval env) ((block5Schedule flags)[i.val]'i.isLt) := by
    rw [show eval env (block5Schedule flags) =
        (block5Schedule flags).map (eval env) from
      eval_vector (α := fields 32) (n := 64) env (block5Schedule flags)]
    rw [Vector.getElem_map, CircuitType.eval_var_fields]
  rw [hget]
  exact block5Schedule_normalized env flags honehot hℓ i

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F p) main Assumptions Spec := by
  -- Keep the fused rounds circuit out of the `circuit_proof_start` bracket: unfolding
  -- it in the goal whnf-times-out. Unfold it only in `h_holds` afterwards.
  circuit_proof_start
  simp only [circuit_norm, SHA256Rounds.circuit, SHA256Rounds.Spec,
    SHA256Rounds.Assumptions] at h_holds
  obtain ⟨h_len_lt, h_onehot, h_state_norm⟩ := h_assumptions
  obtain ⟨h_input_messageLen, h_input_lenFlags, h_input_state⟩ := h_input
  set ℓ := ZMod.val input_messageLen with hℓ
  have h_onehot_eval : OneHotAt (Vector.map (Expression.eval env) input_var_lenFlags) ℓ := by
    rw [h_input_lenFlags, hℓ]; exact h_onehot
  have h_sched_norm := sched_norm env input_var_lenFlags ℓ (by simpa [hℓ] using h_len_lt) h_onehot_eval
  have h_rounds_full := h_holds ⟨h_state_norm, h_sched_norm⟩
  obtain ⟨h_rounds_val, h_rounds_norm⟩ := h_rounds_full
  have h_sched_map :
      Vector.map valueBits (eval env (block5Schedule input_var_lenFlags)) =
        Specs.SHA256.messageSchedule (block5SpecBlock ℓ) := by
    rw [block5Schedule_map_valueBits env input_var_lenFlags h_onehot_eval
      (by simpa [hℓ] using h_len_lt)]
    rfl
  refine ⟨⟨?_, h_rounds_norm⟩, Or.inr ⟨h_state_norm, h_sched_norm⟩⟩
  rw [h_rounds_val, h_sched_map]
  simp only [Specs.SHA256.compressBlock, Vector.getElem_map, Fin.getElem_fin]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start
  simp only [circuit_norm, SHA256Rounds.circuit, SHA256Rounds.Assumptions]
  obtain ⟨h_len_lt, h_onehot, h_state_norm⟩ := h_assumptions
  obtain ⟨h_input_messageLen, h_input_lenFlags, h_input_state⟩ := h_input
  set ℓ := ZMod.val input_messageLen with hℓ
  have h_onehot_eval : OneHotAt (Vector.map (Expression.eval env.toEnvironment) input_var_lenFlags) ℓ := by
    rw [h_input_lenFlags, hℓ]; exact h_onehot
  have h_sched_norm := sched_norm env.toEnvironment input_var_lenFlags ℓ
    (by simpa [hℓ] using h_len_lt) h_onehot_eval
  exact ⟨h_state_norm, h_sched_norm⟩

def circuit : FormalCircuit (F p) Inputs SHA256State := {
  main, elaborated, Assumptions, Spec, soundness
  completeness := by simp only [completeness]
}

end CompressBlock5
end Solution.SHA256
end
