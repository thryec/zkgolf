import Solution.SHA256.Xor3
import Solution.SHA256.Theorems

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Solution.SHA256

/-!
# Σ₁ (upper sigma 1) for SHA-256

Σ₁(x) = ROTR6(x) XOR ROTR11(x) XOR ROTR25(x)

One xor3 call = 32 witnesses total.

Mirrors `UpperSigma0` with constants 6, 11, 25 instead of 2, 13, 22.
Reuses the shared helper lemmas in `Theorems`.
-/

namespace UpperSigma1

/-- Σ₁(x) = ROTR6(x) XOR ROTR11(x) XOR ROTR25(x) -/
def upperSigma1 (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  Xor3.circuit ⟨rotr32 6 x, rotr32 11 x, rotr32 25 x⟩

def main (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  upperSigma1 x

def Assumptions (x : fields 32 (F p)) : Prop := Normalized x

def Spec (x : fields 32 (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.upperSigma1 (valueBits x) ∧ Normalized z

/-! ## Soundness / Completeness

This gadget composes one `Xor3.circuit` subcircuit over three `rotr32`s of the
input. Both proofs reuse `Xor3`'s `Assumptions`/`Spec` and the shared
`Normalized_eval_rotr32` / `valueBits_eval_rotr32` bridges in `Theorems`; they
never touch witness indices. -/

instance elaborated : ElaboratedCircuit (F p) (fields 32) (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [upperSigma1, Xor3.circuit]
  simp only [Xor3.Assumptions, Xor3.Spec, and_imp] at h_holds
  have nr6 := Normalized_eval_rotr32 env input_var input h_input h_assumptions 6
  have nr11 := Normalized_eval_rotr32 env input_var input h_input h_assumptions 11
  have nr25 := Normalized_eval_rotr32 env input_var input h_input h_assumptions 25
  obtain ⟨v, n⟩ := h_holds nr6 nr11 nr25
  refine ⟨?_, n⟩
  rw [v, valueBits_eval_rotr32 env input_var input h_input h_assumptions 6,
    valueBits_eval_rotr32 env input_var input h_input h_assumptions 11,
    valueBits_eval_rotr32 env input_var input h_input h_assumptions 25]
  rfl

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [upperSigma1, Xor3.circuit]
  simp only [Xor3.Assumptions, Xor3.Spec, and_imp] at h_env ⊢
  have nr6 := Normalized_eval_rotr32 env.toEnvironment input_var input h_input h_assumptions 6
  have nr11 := Normalized_eval_rotr32 env.toEnvironment input_var input h_input h_assumptions 11
  have nr25 := Normalized_eval_rotr32 env.toEnvironment input_var input h_input h_assumptions 25
  exact ⟨nr6, nr11, nr25⟩

def circuit : FormalCircuit (F p) (fields 32) (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end UpperSigma1
end Solution.SHA256
end
