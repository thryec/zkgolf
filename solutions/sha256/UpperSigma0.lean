import Solution.SHA256.Xor3
import Solution.SHA256.Theorems

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Solution.SHA256

/-!
# Σ₀ (upper sigma 0) for SHA-256

Σ₀(x) = ROTR2(x) XOR ROTR13(x) XOR ROTR22(x)

One xor3 call = 32 witnesses total.

Mirrors `LowerSigma0` but with three rotations (no shift) and constants 2, 13, 22.
Reuses the shared helper lemmas in `Theorems`.
-/

namespace UpperSigma0

/-- Σ₀(x) = ROTR2(x) XOR ROTR13(x) XOR ROTR22(x) -/
def upperSigma0 (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  Xor3.circuit ⟨rotr32 2 x, rotr32 13 x, rotr32 22 x⟩

def main (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  upperSigma0 x

def Assumptions (x : fields 32 (F p)) : Prop := Normalized x

def Spec (x : fields 32 (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.upperSigma0 (valueBits x) ∧ Normalized z

/-! ## Soundness / Completeness

This gadget composes one `Xor3.circuit` subcircuit over three `rotr32`s of the
input. Both proofs reuse `Xor3`'s `Assumptions`/`Spec` and the shared
`Normalized_eval_rotr32` / `valueBits_eval_rotr32` bridges in `Theorems`; they
never touch witness indices. -/

instance elaborated : ElaboratedCircuit (F p) (fields 32) (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [upperSigma0, Xor3.circuit]
  simp only [Xor3.Assumptions, Xor3.Spec, and_imp] at h_holds
  have nr2 := Normalized_eval_rotr32 env input_var input h_input h_assumptions 2
  have nr13 := Normalized_eval_rotr32 env input_var input h_input h_assumptions 13
  have nr22 := Normalized_eval_rotr32 env input_var input h_input h_assumptions 22
  obtain ⟨v, n⟩ := h_holds nr2 nr13 nr22
  refine ⟨?_, n⟩
  rw [v, valueBits_eval_rotr32 env input_var input h_input h_assumptions 2,
    valueBits_eval_rotr32 env input_var input h_input h_assumptions 13,
    valueBits_eval_rotr32 env input_var input h_input h_assumptions 22]
  rfl

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [upperSigma0, Xor3.circuit]
  simp only [Xor3.Assumptions, Xor3.Spec, and_imp] at h_env ⊢
  have nr2 := Normalized_eval_rotr32 env.toEnvironment input_var input h_input h_assumptions 2
  have nr13 := Normalized_eval_rotr32 env.toEnvironment input_var input h_input h_assumptions 13
  have nr22 := Normalized_eval_rotr32 env.toEnvironment input_var input h_input h_assumptions 22
  exact ⟨nr2, nr13, nr22⟩

def circuit : FormalCircuit (F p) (fields 32) (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end UpperSigma0
end Solution.SHA256
end
