import Solution.SHA256.BitwiseOps
import Solution.SHA256.Theorems
import Solution.SHA256.Maj32Theorems
import Solution.SHA256.PackedMajRow
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256

variable [Fact (p > 2^76)]

/-!
# Cross-round packed `Maj` gadget

Superimposes the two rounds' majority columns into a single 32-witness column `z`,
at weights `1` and `λ = 2^40`:

  `z[j] = maj(a[j],b[j],c[j]) + 2^40 · maj(u[j],a[j],b[j])`,

where `(a,b,c)` are the round-`t` registers and `u = a_{t+1} = new_a_t`. Because
`maj` is degree 3, one row cannot pin `z`; instead **two** two-valued CLASS-A rows
per lane are emitted (`PackedMajRow.majRows_unique` proves the pair pins `z`
uniquely). Cost per lane: 1 witness + 2 rows, i.e. `(32, 64)` — vs the unpacked
`2 × (32,32) = (64,64)`, a net `−32` allocations. The output is NOT a normalized
bit vector: each lane holds `maj_t[j] + 2^40·maj_{t+1}[j]`, consumed directly by
the fused a-adder (exactly like the packed `Ch` column).
-/

namespace PackedMaj

local notation "λE" => (((2^40 : F p) : Expression (F p)))

/-- The packed cross-round `Maj` gadget. Two `majRows` per lane pin `z`. -/
def packedMaj (a b c u : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let z ← witnessVector 32 fun env =>
    Vector.ofFn fun (j : Fin 32) =>
      PackedMajRow.majBit (env a[j.val]) (env b[j.val]) (env c[j.val])
        + (2^40 : F p) * PackedMajRow.majBit (env u[j.val]) (env a[j.val]) (env b[j.val])
  Circuit.forEach (Vector.finRange 32) fun j =>
    assertZero
      ((z[j.val]'j.isLt - (λE + 1) * a[j.val]'j.isLt)
        * (z[j.val]'j.isLt - (c[j.val]'j.isLt + λE * u[j.val]'j.isLt)))
  Circuit.forEach (Vector.finRange 32) fun j =>
    assertZero
      ((z[j.val]'j.isLt - (a[j.val]'j.isLt + λE * b[j.val]'j.isLt))
        * (z[j.val]'j.isLt
            - (λE * (a[j.val]'j.isLt + b[j.val]'j.isLt + u[j.val]'j.isLt - 1) + c[j.val]'j.isLt)))
  return z

structure Inputs (F : Type) where
  a : fields 32 F
  b : fields 32 F
  c : fields 32 F
  u : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  packedMaj input.a input.b input.c input.u

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b ∧ Normalized input.c ∧ Normalized input.u

/-- The output column is pinned lanewise to the packed value
    `maj(a,b,c)[j] + 2^40·maj(u,a,b)[j]`. -/
def Spec (input : Inputs (F p)) (z : fields 32 (F p)) : Prop :=
  ∀ j : Fin 32, z[j] =
    PackedMajRow.majBit input.a[j] input.b[j] input.c[j]
      + (2^40 : F p) * PackedMajRow.majBit input.u[j] input.a[j] input.b[j]

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 32) main := by
  elaborate_circuit

/-- `λ = 2^40 ≠ 0` for `p > 2^76`. -/
lemma lam_ne_zero : (2^40 : F p) ≠ 0 := by
  have hp : (2:ℕ)^76 < p := Fact.out
  intro hcon
  have hnat : ((1099511627776 : ℕ) : F p) = 0 := by exact_mod_cast hcon
  have hv := congrArg ZMod.val hnat
  rw [ZMod.val_natCast_of_lt (Nat.lt_trans (by norm_num) hp), ZMod.val_zero] at hv
  omega

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [packedMaj]
  obtain ⟨ha, hb, hc, hu⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b, h_input_c, h_input_u⟩ := h_input
  obtain ⟨c_row1, c_row2⟩ := h_holds
  have h_ai : ∀ i : Fin 32, Expression.eval env input_var_a[i.val] = input_a[i] := by
    intro i; have := Vector.ext_iff.mp h_input_a i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_bi : ∀ i : Fin 32, Expression.eval env input_var_b[i.val] = input_b[i] := by
    intro i; have := Vector.ext_iff.mp h_input_b i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_ci : ∀ i : Fin 32, Expression.eval env input_var_c[i.val] = input_c[i] := by
    intro i; have := Vector.ext_iff.mp h_input_c i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_ui : ∀ i : Fin 32, Expression.eval env input_var_u[i.val] = input_u[i] := by
    intro i; have := Vector.ext_iff.mp h_input_u i i.isLt; simp [Vector.getElem_map] at this; exact this
  intro j
  have h1 := c_row1 j
  have h2 := c_row2 j
  rw [h_ai j, h_ci j, h_ui j] at h1
  rw [h_ai j, h_bi j, h_ci j, h_ui j] at h2
  exact PackedMajRow.majRows_unique lam_ne_zero (ha j) (hb j) (hc j) (hu j)
    (by linear_combination h1) (by linear_combination h2)

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [packedMaj]
  obtain ⟨ha, hb, hc, hu⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b, h_input_c, h_input_u⟩ := h_input
  have h_ai : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_a[i.val] = input_a[i] := by
    intro i; have := Vector.ext_iff.mp h_input_a i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_bi : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_b[i.val] = input_b[i] := by
    intro i; have := Vector.ext_iff.mp h_input_b i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_ci : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_c[i.val] = input_c[i] := by
    intro i; have := Vector.ext_iff.mp h_input_c i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_ui : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_u[i.val] = input_u[i] := by
    intro i; have := Vector.ext_iff.mp h_input_u i i.isLt; simp [Vector.getElem_map] at this; exact this
  -- Both rows vanish at the honest packed witness value, per boolean corner.
  have key : ∀ s x y u' : F p, IsBool s → IsBool x → IsBool y → IsBool u' →
      (((PackedMajRow.majBit s x y + (2^40 : F p) * PackedMajRow.majBit u' s x) - ((2^40 : F p) + 1) * s)
          * ((PackedMajRow.majBit s x y + (2^40 : F p) * PackedMajRow.majBit u' s x) - (y + (2^40 : F p) * u')) = 0)
      ∧ (((PackedMajRow.majBit s x y + (2^40 : F p) * PackedMajRow.majBit u' s x) - (s + (2^40 : F p) * x))
          * ((PackedMajRow.majBit s x y + (2^40 : F p) * PackedMajRow.majBit u' s x)
              - ((2^40 : F p) * (s + x + u' - 1) + y)) = 0) := by
    intro s x y u' hs hx hy hu'
    simp only [PackedMajRow.majBit]
    rcases hs with h | h <;> rcases hx with h' | h' <;> rcases hy with h'' | h'' <;>
      rcases hu' with h''' | h''' <;> subst h h' h'' h''' <;> exact ⟨by ring, by ring⟩
  obtain ⟨h_env_w, -⟩ := h_env
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have henv := h_env_w j
    simp only [Vector.getElem_ofFn] at henv
    rw [h_ai j, h_bi j, h_ci j, h_ui j] at henv
    rw [henv, h_ai j, h_ci j, h_ui j]
    linear_combination (key input_a[j] input_b[j] input_c[j] input_u[j] (ha j) (hb j) (hc j) (hu j)).1
  · have henv := h_env_w j
    simp only [Vector.getElem_ofFn] at henv
    rw [h_ai j, h_bi j, h_ci j, h_ui j] at henv
    rw [henv, h_ai j, h_bi j, h_ci j, h_ui j]
    linear_combination (key input_a[j] input_b[j] input_c[j] input_u[j] (ha j) (hb j) (hc j) (hu j)).2

def circuit : FormalCircuit (F p) Inputs (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end PackedMaj
end Solution.SHA256
end
