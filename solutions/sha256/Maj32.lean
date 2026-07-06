import Solution.SHA256.BitwiseOps
import Solution.SHA256.Theorems
import Solution.SHA256.Maj32Theorems
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Solution.SHA256

/-!
# Majority function Maj(a, b, c) for SHA-256

Maj(a, b, c) = (a AND b) XOR (a AND c) XOR (b AND c).
Single-constraint encoding (Verified-zkEVM/clean#395): witness only the majority
output z (32 variables) and impose, per bit, the single R1CS row
  12 + (z + a + b − 9c + 3)·(a + b + 6c − 4) = 0.
The row is linear in `z` with a multiplier that never vanishes on the boolean
cube (values `±2, ±3, ±4`), so `z` is uniquely pinned to the (boolean) majority
value — no separate booleanity row. 32 witnesses, 32 constraints.
-/

namespace Maj32

/-- Majority function: Maj(a, b, c) = (a AND b) XOR (a AND c) XOR (b AND c).
    Single-constraint encoding: witness the majority output z, then constrain, per bit,
      12 + (z + a + b − 9c + 3)·(a + b + 6c − 4) = 0.
    The honest witness value is the standard majority `a·b + c·(a + b − 2·a·b)`. -/
def maj32 (a b c : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let z ← witnessVector 32 fun env =>
    Vector.ofFn fun (i : Fin 32) =>
      env a[i] * env b[i] + env c[i] * (env a[i] + env b[i] - 2 * (env a[i] * env b[i]))
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (12 + (z[i] + a[i] + b[i] - 9 * c[i] + 3) * (a[i] + b[i] + 6 * c[i] - 4))
  return z

structure Inputs (F : Type) where
  a : fields 32 F
  b : fields 32 F
  c : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  maj32 input.a input.b input.c

@[reducible] instance elaborated : ElaboratedCircuit (F p) _ _ main := by
  elaborate_circuit

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b ∧ Normalized input.c

def Spec (input : Inputs (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.Maj (valueBits input.a) (valueBits input.b) (valueBits input.c) ∧
  Normalized z

/-!
## Helper lemmas for valueBits and bitwise Maj

Gadget-private lemmas live in `Maj32Theorems`. Shared lemmas
(`sum_bool_lt_two_pow`, `testBit_binary_sum`, ...) live in `Theorems`.
-/

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [maj32]
  obtain ⟨ha, hb, hc⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b, h_input_c⟩ := h_input
  have h_ai : ∀ i : Fin 32, Expression.eval env input_var_a[i.val] = input_a[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_a i i.isLt
    simp [Vector.getElem_map] at this; exact this
  have h_bi : ∀ i : Fin 32, Expression.eval env input_var_b[i.val] = input_b[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_b i i.isLt
    simp [Vector.getElem_map] at this; exact this
  have h_ci : ∀ i : Fin 32, Expression.eval env input_var_c[i.val] = input_c[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_c i i.isLt
    simp [Vector.getElem_map] at this; exact this
  -- The single constraint family pins each z[i] to the majority value.
  set z : fields 32 (F p) :=
    Vector.map (Expression.eval env) (Vector.mapRange 32 fun i =>
      (var {index := i₀ + i} : Expression (F p))) with hz_def
  have h_z_get : ∀ i : Fin 32, z[i] = env.get (i₀ + i.val) := by
    intro i; simp [z, Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  have h_eq' : ∀ i : Fin 32, z[i] =
      input_a[i] * input_b[i] + input_c[i] * (input_a[i] + input_b[i] - 2 * (input_a[i] * input_b[i])) := by
    intro i
    have hh := h_holds i
    rw [h_ai i, h_bi i, h_ci i, ← h_z_get i] at hh
    exact maj3_unique (ha i) (hb i) (hc i) (by linear_combination hh)
  exact spec_of_constraint input_a input_b input_c z ha hb hc h_eq'

omit [Fact (p > 2^35)] in
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [maj32]
  obtain ⟨ha, hb, hc⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b, h_input_c⟩ := h_input
  have h_ai : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_a[i.val] = input_a[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_a i i.isLt
    simp [Vector.getElem_map] at this; exact this
  have h_bi : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_b[i.val] = input_b[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_b i i.isLt
    simp [Vector.getElem_map] at this; exact this
  have h_ci : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_c[i.val] = input_c[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_c i i.isLt
    simp [Vector.getElem_map] at this; exact this
  intro i
  -- 12 + (maj + a + b − 9c + 3)·(a + b + 6c − 4) = 0 for the honest majority witness
  have henv := h_env i
  simp only [Vector.getElem_ofFn] at henv
  rw [henv, h_ai i, h_bi i, h_ci i]
  rcases ha i with h | h <;> rcases hb i with h' | h' <;> rcases hc i with h'' | h'' <;>
    rw [h, h', h''] <;> ring

def circuit : FormalCircuit (F p) Inputs (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end Maj32
end Solution.SHA256
end
