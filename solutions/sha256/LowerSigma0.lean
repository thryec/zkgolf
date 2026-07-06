import Solution.SHA256.Xor3
import Solution.SHA256.Theorems
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Solution.SHA256

/-!
# σ₀ (lower sigma 0) for SHA-256

σ₀(x) = ROTR7(x) XOR ROTR18(x) XOR SHR3(x)

One xor3 call = 32 witnesses total.
-/

namespace LowerSigma0

/-- σ₀(x) = ROTR7(x) XOR ROTR18(x) XOR SHR3(x) -/
def lowerSigma0 (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  Xor3.circuit ⟨rotr32 7 x, rotr32 18 x, shr32 3 x⟩

def main (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  lowerSigma0 x

def Assumptions (x : fields 32 (F p)) : Prop := Normalized x

def Spec (x : fields 32 (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.lowerSigma0 (valueBits x) ∧ Normalized z

/-! ## Soundness / Completeness

This gadget composes one `Xor3.circuit` subcircuit over `rotr32`/`shr32` of the
input. Both proofs reuse `Xor3`'s `Assumptions`/`Spec` and the shared
`Normalized_eval_*` / `valueBits_eval_*` bridges in `Theorems`; they never touch
witness indices. -/

instance elaborated : ElaboratedCircuit (F p) (fields 32) (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [lowerSigma0, Xor3.circuit]
  simp only [Xor3.Assumptions, Xor3.Spec, and_imp] at h_holds
  -- Discharge the subcircuit `Normalized` assumptions compositionally.
  have nr7 := Normalized_eval_rotr32 env input_var input h_input h_assumptions 7
  have nr18 := Normalized_eval_rotr32 env input_var input h_input h_assumptions 18
  have ns3 := Normalized_eval_shr32 env input_var input h_input h_assumptions 3
  obtain ⟨v, n⟩ := h_holds nr7 nr18 ns3
  refine ⟨?_, n⟩
  rw [v, valueBits_eval_rotr32 env input_var input h_input h_assumptions 7,
    valueBits_eval_rotr32 env input_var input h_input h_assumptions 18,
    valueBits_eval_shr32 env input_var input h_input h_assumptions 3]
  rfl

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [lowerSigma0, Xor3.circuit]
  simp only [Xor3.Assumptions, Xor3.Spec, and_imp] at h_env ⊢
  have nr7 := Normalized_eval_rotr32 env.toEnvironment input_var input h_input h_assumptions 7
  have nr18 := Normalized_eval_rotr32 env.toEnvironment input_var input h_input h_assumptions 18
  have ns3 := Normalized_eval_shr32 env.toEnvironment input_var input h_input h_assumptions 3
  exact ⟨nr7, nr18, ns3⟩

def circuit : FormalCircuit (F p) (fields 32) (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end LowerSigma0
end Solution.SHA256
end
