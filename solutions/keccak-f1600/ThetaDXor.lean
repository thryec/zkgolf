import Solution.KeccakF1600.Xor3Lane

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 3)]

namespace Solution.KeccakF1600

namespace ThetaDXor

/-!
# Fused θ D-fold: `state[x,y] ⊕ C[x−1] ⊕ ROT(C[x+1], 1)`

Folds the separate `D` layer of θ into the state XOR. Instead of computing
`D[x] = C[x−1] ⊕ ROT(C[x+1], 1)` and then `state[x,y] ⊕ D[x]`, each of the 25
output lanes is a single 3-input XOR of the state lane with the two column
parities, using the `Xor3Lane` gadget. `ROT(·,1)` is free rotation wiring.
-/

structure Inputs (F : Type) where
  state : KeccakBitState F
  c : KeccakBitRow F
deriving ProvableStruct

def main : Var Inputs (F p) → Circuit (F p) (Var KeccakBitState (F p))
  | { state, c } => .mapFinRange 25 fun i =>
    Xor3Lane.circuit ⟨state[i.val], c[(i.val % 5 + 4) % 5], rotl 1 c[(i.val % 5 + 1) % 5]⟩

def Assumptions (inputs : Inputs (F p)) : Prop :=
  let ⟨state, c⟩ := inputs
  StateNormalized state ∧ RowNormalized c

def Spec (inputs : Inputs (F p)) (out : KeccakBitState (F p)) : Prop :=
  let ⟨state, c⟩ := inputs
  StateNormalized out ∧ stateValue out = thetaXorSpec (stateValue state) (thetaDSpec (rowValue c))

instance elaborated : ElaboratedCircuit (F p) Inputs KeccakBitState main := by
  elaborate_circuit

lemma spec_loop (A : Vector ℕ 25) (C : Vector ℕ 5) :
    thetaXorSpec A (thetaDSpec C) = .ofFn fun i : Fin 25 =>
      A[i.val] ^^^ C[(i.val % 5 + 4) % 5] ^^^ Specs.Keccak.rotLeft 64 C[(i.val % 5 + 1) % 5] 1 := by
  apply Vector.ext
  intro i hi
  simp only [thetaXorSpec, thetaDSpec, Vector.getElem_ofFn, Nat.xor_assoc]

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [Xor3Lane.circuit, Xor3Lane.Assumptions, Xor3Lane.Spec]
  obtain ⟨state_norm, c_norm⟩ := h_assumptions
  obtain ⟨hs, hc⟩ := h_input
  apply stateNormalized_value_ext
  simp only [circuit_norm, spec_loop, eval_vector, stateValue, rowValue]
  intro i
  have hsi : Vector.map (Expression.eval env) input_var_state[i.val]
      = input_state[i.val] := by
    have h := getElem_eval_vector (α := fields 64) env input_var_state i.val i.isLt
    rw [CircuitType.eval_var_fields] at h; rw [hs] at h; exact h
  have hc1 : Vector.map (Expression.eval env) input_var_c[(i.val % 5 + 4) % 5]
      = input_c[(i.val % 5 + 4) % 5] := by
    have h := getElem_eval_vector (α := fields 64) env input_var_c ((i.val % 5 + 4) % 5) (by omega)
    rw [CircuitType.eval_var_fields] at h; rw [hc] at h; exact h
  have hc2 : Vector.map (Expression.eval env) input_var_c[(i.val % 5 + 1) % 5]
      = input_c[(i.val % 5 + 1) % 5] := by
    have h := getElem_eval_vector (α := fields 64) env input_var_c ((i.val % 5 + 1) % 5) (by omega)
    rw [CircuitType.eval_var_fields] at h; rw [hc] at h; exact h
  have hrot_val : valueBits (Vector.map (Expression.eval env)
      (rotl 1 input_var_c[(i.val % 5 + 1) % 5]))
      = Specs.Keccak.rotLeft 64 (valueBits input_c[(i.val % 5 + 1) % 5]) 1 :=
    valueBits_eval_rotl env _ input_c[(i.val % 5 + 1) % 5] hc2
      (c_norm ⟨(i.val % 5 + 1) % 5, by omega⟩) 1
  have hrot_norm : Normalized (Vector.map (Expression.eval env)
      (rotl 1 input_var_c[(i.val % 5 + 1) % 5])) :=
    Normalized_eval_rotl env _ input_c[(i.val % 5 + 1) % 5] hc2
      (c_norm ⟨(i.val % 5 + 1) % 5, by omega⟩) 1
  have harg : Normalized (Vector.map (Expression.eval env) input_var_state[i.val])
      ∧ Normalized (Vector.map (Expression.eval env) input_var_c[(i.val % 5 + 4) % 5])
      ∧ Normalized (Vector.map (Expression.eval env)
          (rotl 1 input_var_c[(i.val % 5 + 1) % 5])) := by
    rw [hsi, hc1]
    exact ⟨state_norm i, c_norm ⟨(i.val % 5 + 4) % 5, by omega⟩, hrot_norm⟩
  obtain ⟨h_val, h_norm⟩ := h_holds i harg
  refine ⟨h_norm, ?_⟩
  rw [Vector.getElem_ofFn, h_val, hsi, hc1, hrot_val]

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [Xor3Lane.circuit, Xor3Lane.Assumptions, Xor3Lane.Spec]
  obtain ⟨state_norm, c_norm⟩ := h_assumptions
  obtain ⟨hs, hc⟩ := h_input
  intro i
  have hsi : Vector.map (Expression.eval env.toEnvironment) input_var_state[i.val]
      = input_state[i.val] := by
    have h := getElem_eval_vector (α := fields 64) env.toEnvironment input_var_state i.val i.isLt
    rw [CircuitType.eval_var_fields] at h; rw [hs] at h; exact h
  have hc1 : Vector.map (Expression.eval env.toEnvironment) input_var_c[(i.val % 5 + 4) % 5]
      = input_c[(i.val % 5 + 4) % 5] := by
    have h := getElem_eval_vector (α := fields 64) env.toEnvironment input_var_c
      ((i.val % 5 + 4) % 5) (by omega)
    rw [CircuitType.eval_var_fields] at h; rw [hc] at h; exact h
  have hc2 : Vector.map (Expression.eval env.toEnvironment) input_var_c[(i.val % 5 + 1) % 5]
      = input_c[(i.val % 5 + 1) % 5] := by
    have h := getElem_eval_vector (α := fields 64) env.toEnvironment input_var_c
      ((i.val % 5 + 1) % 5) (by omega)
    rw [CircuitType.eval_var_fields] at h; rw [hc] at h; exact h
  have hrot_norm : Normalized (Vector.map (Expression.eval env.toEnvironment)
      (rotl 1 input_var_c[(i.val % 5 + 1) % 5])) :=
    Normalized_eval_rotl env.toEnvironment _ input_c[(i.val % 5 + 1) % 5] hc2
      (c_norm ⟨(i.val % 5 + 1) % 5, by omega⟩) 1
  refine ⟨?_, ?_, hrot_norm⟩
  · rw [hsi]; exact state_norm i
  · rw [hc1]; exact c_norm ⟨(i.val % 5 + 4) % 5, by omega⟩

def circuit : FormalCircuit (F p) Inputs KeccakBitState where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end ThetaDXor
end Solution.KeccakF1600
end
