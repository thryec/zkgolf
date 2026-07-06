import Solution.SHA256.SHA256Round
import Solution.SHA256.Round0Block1
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Solution.SHA256

/-!
# SHA-256 Block-1 Round 1 (Ch/Maj affine-folded)

In block 1, round 0 is constant-folded (`Round0Block1`), so its output state is
`#v[new_a⁰, H0_0, H0_1, H0_2, new_e⁰, H0_4, H0_5, H0_6]`. Feeding this into round 1:

  a = new_a⁰ (variable)   b = H0_0   c = H0_1   d = H0_2
  e = new_e⁰ (variable)   f = H0_4   g = H0_5   h = H0_6

`Σ₁(e)` and `Σ₀(a)` still depend on the variables `e = new_e⁰`, `a = new_a⁰`, so
they remain real gadgets. But `Ch(e, f, g)` with `f = H0_4`, `g = H0_5` constant is
*affine* in `e`'s bits (`chᵢ = gᵢ + eᵢ·(fᵢ − gᵢ)`), and `Maj(a, b, c)` with
`b = H0_0`, `c = H0_1` constant is affine in `a`'s bits
(`majᵢ = aᵢbᵢ + cᵢ(aᵢ + bᵢ − 2aᵢbᵢ)`). Both therefore need no witnesses and no
constraints: they are plain affine *expression vectors* fed straight into the two
fused adders. This peels the two `(32,32)` bit gadgets `Ch` and `Maj` off round 1
(a `(64,64)` saving).

The `valueBits = spec` / `Normalized` obligations for the two affine vectors are
discharged by `Ch32.spec_of_constraint` / `Maj32.spec_of_constraint` (the same
lemmas the full gadgets use), specialised to the constant `f, g` / `b, c` words.
-/

namespace Round1Block1

open Round0Block1 (h0_0 h0_1 h0_2 h0_4 h0_5 h0_6)

/-! ## Round constant `K[1]` -/

def k1C : ℕ := 0x71374491

lemma k1C_eq : k1C = (Specs.SHA256.K[1]).toNat := by decide
lemma k1C_lt : k1C < 2^32 := by norm_num [k1C]

/-! ## Folded constant addend `d + h + K[1]`

In round 1, the three constant addends of `new_e` — `d = H0[2]`, `h = H0[6]`,
`k = K[1]` — fold into the single 32-bit constant `dhkC = h0_2 + h0_6 + k1C`
(which happens to be `< 2^32`, no reduction needed). The 6-word `AddMany`
(34, 35) therefore becomes a 4-word `AddMany.circuit2` (33, 34). -/

def dhkC : ℕ := 0xcd2a11ae

lemma dhkC_lt : dhkC < 2^32 := by norm_num [dhkC]

/-- `dhkC + Σ₁ + Ch + w (mod 2^32)` equals the spec-shaped nested round-1 `new_e`
sum with the constants `H0[2]`, `H0[6]`, `K[1]` re-expanded. -/
lemma mod_dhkC (s c wv : ℕ) :
    (dhkC + s + c + wv) % 2^32 =
      _root_.add32 (Specs.SHA256.H0[2])
        (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (Specs.SHA256.H0[6]) s) c)
          ((Specs.SHA256.K[1]).toNat)) wv) := by
  rw [← Round0Block1.h0_2_eq, ← Round0Block1.h0_6_eq, ← k1C_eq]
  simp only [dhkC, Round0Block1.h0_2, Round0Block1.h0_6, k1C]
  unfold _root_.add32
  omega

/-! ## Named round-1 input state

`sha256Round` applied to a *literal* `#v[..]` state trips the kernel's
deep-recursion guard, because reducing `#v[..][j]` when the entries are the IV
words unfolds `H0` into its huge numerals and the fused `add32` sums then blow the
kernel stack.  Mirroring `Round0Block1`'s use of the *named* `Specs.SHA256.H0`, we
give the round-1 state a name `r1state` and rewrite its indices with rfl lemmas
whose right-hand sides keep `H0[j]` symbolic. -/

/-- The round-1 input state (values): variable words `a = new_a⁰`, `e = new_e⁰`,
with the six constant IV words baked in. -/
def r1state (va ve : ℕ) : Vector ℕ 8 :=
  #v[va, Specs.SHA256.H0[0], Specs.SHA256.H0[1], Specs.SHA256.H0[2],
     ve, Specs.SHA256.H0[4], Specs.SHA256.H0[5], Specs.SHA256.H0[6]]

lemma r1state_0 (va ve : ℕ) : (r1state va ve)[0] = va := rfl
lemma r1state_1 (va ve : ℕ) : (r1state va ve)[1] = Specs.SHA256.H0[0] := rfl
lemma r1state_2 (va ve : ℕ) : (r1state va ve)[2] = Specs.SHA256.H0[1] := rfl
lemma r1state_3 (va ve : ℕ) : (r1state va ve)[3] = Specs.SHA256.H0[2] := rfl
lemma r1state_4 (va ve : ℕ) : (r1state va ve)[4] = ve := rfl
lemma r1state_5 (va ve : ℕ) : (r1state va ve)[5] = Specs.SHA256.H0[4] := rfl
lemma r1state_6 (va ve : ℕ) : (r1state va ve)[6] = Specs.SHA256.H0[5] := rfl
lemma r1state_7 (va ve : ℕ) : (r1state va ve)[7] = Specs.SHA256.H0[6] := rfl

/-- `sha256Round` of the round-1 state, as an explicit 8-entry vector whose entries
keep the IV words `H0[j]` symbolic. Proven with the `r1state_*` rfl lemmas so the
kernel never reduces `H0` to its numerals. -/
lemma sha256Round_r1state (va ve k w : ℕ) :
    Specs.SHA256.sha256Round (r1state va ve) k w =
      #v[_root_.add32
           (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (Specs.SHA256.H0[6])
             (Specs.SHA256.upperSigma1 ve)) (Specs.SHA256.Ch ve (Specs.SHA256.H0[4]) (Specs.SHA256.H0[5]))) k) w)
           (_root_.add32 (Specs.SHA256.upperSigma0 va)
             (Specs.SHA256.Maj va (Specs.SHA256.H0[0]) (Specs.SHA256.H0[1]))),
         va, Specs.SHA256.H0[0], Specs.SHA256.H0[1],
         _root_.add32 (Specs.SHA256.H0[2])
           (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (Specs.SHA256.H0[6])
             (Specs.SHA256.upperSigma1 ve)) (Specs.SHA256.Ch ve (Specs.SHA256.H0[4]) (Specs.SHA256.H0[5]))) k) w),
         ve, Specs.SHA256.H0[4], Specs.SHA256.H0[5]] := by
  simp only [Specs.SHA256.sha256Round, r1state_0, r1state_1, r1state_2, r1state_3,
    r1state_4, r1state_5, r1state_6, r1state_7]

/-- `sha256Round` as an explicit 8-entry vector (whole-vector `rfl`, `s` a
variable so nothing reduces). -/
lemma sha256Round_eq (s : Vector ℕ 8) (k w : ℕ) :
    Specs.SHA256.sha256Round s k w =
      #v[_root_.add32
           (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 s[7]
             (Specs.SHA256.upperSigma1 s[4])) (Specs.SHA256.Ch s[4] s[5] s[6])) k) w)
           (_root_.add32 (Specs.SHA256.upperSigma0 s[0]) (Specs.SHA256.Maj s[0] s[1] s[2])),
         s[0], s[1], s[2],
         _root_.add32 s[3]
           (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 s[7]
             (Specs.SHA256.upperSigma1 s[4])) (Specs.SHA256.Ch s[4] s[5] s[6])) k) w),
         s[4], s[5], s[6]] := rfl

lemma vec8_getElem0 {α : Type*} (x0 x1 x2 x3 x4 x5 x6 x7 : α) :
    (#v[x0, x1, x2, x3, x4, x5, x6, x7] : Vector α 8)[0] = x0 := rfl
lemma vec8_getElem4 {α : Type*} (x0 x1 x2 x3 x4 x5 x6 x7 : α) :
    (#v[x0, x1, x2, x3, x4, x5, x6, x7] : Vector α 8)[4] = x4 := rfl

/-- The block-1 round-0 output state (`sha256Round H0 k w`) already has the round-1
shape (constant IV words in positions 1,2,3,5,6,7), so rebuilding it as
`r1state s[0] s[4]` recovers it. This bridges `Round0Block1`'s output into
`Round1Block1`'s spec. -/
lemma r1state_of_sha256Round_H0 (k w : ℕ) :
    r1state ((Specs.SHA256.sha256Round Specs.SHA256.H0 k w)[0])
            ((Specs.SHA256.sha256Round Specs.SHA256.H0 k w)[4])
      = Specs.SHA256.sha256Round Specs.SHA256.H0 k w := by
  rw [sha256Round_eq Specs.SHA256.H0 k w, vec8_getElem0, vec8_getElem4]; rfl

/-! ## Affine `Ch`/`Maj` expression vectors (no witnesses, no constraints) -/

/-- Affine choice: `chᵢ = gᵢ + eᵢ·(fᵢ − gᵢ)` (affine in `e` when `f, g` constant). -/
def chExpr (e f g : Var (fields 32) (F p)) : Var (fields 32) (F p) :=
  Vector.ofFn fun (i : Fin 32) => g[i] + e[i] * (f[i] - g[i])

/-- Affine majority: `majᵢ = aᵢbᵢ + cᵢ(aᵢ + bᵢ − 2aᵢbᵢ)` (affine in `a` when
`b, c` constant). -/
def majExpr (a b c : Var (fields 32) (F p)) : Var (fields 32) (F p) :=
  Vector.ofFn fun (i : Fin 32) => a[i] * b[i] + c[i] * (a[i] + b[i] - 2 * (a[i] * b[i]))

/-! ## The circuit -/

structure Inputs (F : Type) where
  a : fields 32 F
  e : fields 32 F
  w : fields 32 F
deriving ProvableStruct

/-- Ch/Maj affine-folded round 1 for block 1.  Inputs are the two variable words
`a = new_a⁰`, `e = new_e⁰` and the schedule word `w`; the six constant words are
baked in. -/
def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) := do
  let sig1 ← UpperSigma1.circuit input.e
  let sig0 ← UpperSigma0.circuit input.a
  let ch  := chExpr input.e (constWord32 h0_4) (constWord32 h0_5)
  let maj := majExpr input.a (constWord32 h0_0) (constWord32 h0_1)
  let d := constWord32 (p := p) h0_2
  let new_e ← AddMany.circuit2 (by norm_num) #v[constWord32 dhkC, sig1, ch, input.w]
  let new_a ← AddMany.circuit2c (by norm_num) #v[new_e, sig0, maj, not32 d]
  return #v[new_a, input.a, constWord32 h0_0, constWord32 h0_1, new_e, input.e,
            constWord32 h0_4, constWord32 h0_5]

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.e ∧ Normalized input.w

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    Specs.SHA256.sha256Round (r1state (valueBits input.a) (valueBits input.e))
      (Specs.SHA256.K[1]).toNat (valueBits input.w)
  ∧ ∀ i : Fin 8, Normalized out[i]

instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State main := by
  elaborate_circuit

set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [main, UpperSigma1.circuit, UpperSigma0.circuit,
    AddMany.circuit2, AddMany.circuit2c]
  obtain ⟨ha_norm, he_norm, hw_norm⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_e, h_input_w⟩ := h_input
  simp only [UpperSigma1.Assumptions, UpperSigma0.Assumptions,
    UpperSigma1.Spec, UpperSigma0.Spec,
    AddMany.Assumptions, AddMany.Spec, AddMany.Spec2c, and_imp] at h_holds
  obtain ⟨c_sig1, c_sig0, c_newe, c_newa⟩ := h_holds
  -- per-bit evaluation of the two variable input words
  have h_evi : ∀ i : Fin 32, Expression.eval env input_var_e[i.val] = input_e[i] := by
    intro i; have := Vector.ext_iff.mp h_input_e i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_eva : ∀ i : Fin 32, Expression.eval env input_var_a[i.val] = input_a[i] := by
    intro i; have := Vector.ext_iff.mp h_input_a i i.isLt; simp [Vector.getElem_map] at this; exact this
  -- real Σ gadgets
  have s_sig1 := c_sig1 he_norm
  have s_sig0 := c_sig0 ha_norm
  -- affine Ch(e, H0_4, H0_5) via Ch32's spec lemma
  have h_ch_eq : ∀ i : Fin 32,
      (Vector.map (Expression.eval env) (chExpr input_var_e (constWord32 h0_4) (constWord32 h0_5)))[i]
        = (Vector.map (Expression.eval env) (constWord32 (p:=p) h0_5))[i]
          + input_e[i] * ((Vector.map (Expression.eval env) (constWord32 (p:=p) h0_4))[i]
            - (Vector.map (Expression.eval env) (constWord32 (p:=p) h0_5))[i]) := by
    intro i
    simp only [chExpr, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn, Expression.eval, h_evi]
    ring
  have s_ch : valueBits (Vector.map (Expression.eval env) (chExpr input_var_e (constWord32 h0_4) (constWord32 h0_5))) =
      Specs.SHA256.Ch (valueBits input_e) (valueBits (Vector.map (Expression.eval env) (constWord32 (p:=p) h0_4)))
        (valueBits (Vector.map (Expression.eval env) (constWord32 (p:=p) h0_5))) ∧
      Normalized (Vector.map (Expression.eval env) (chExpr input_var_e (constWord32 h0_4) (constWord32 h0_5))) :=
    Ch32.spec_of_constraint input_e (Vector.map (Expression.eval env) (constWord32 (p:=p) h0_4))
      (Vector.map (Expression.eval env) (constWord32 (p:=p) h0_5))
      (Vector.map (Expression.eval env) (chExpr input_var_e (constWord32 h0_4) (constWord32 h0_5))) he_norm
      (SHA256Rounds.normalized_constWord32 env _) (SHA256Rounds.normalized_constWord32 env _) h_ch_eq
  -- affine Maj(a, H0_0, H0_1) via Maj32's spec lemma
  have h_maj_eq : ∀ i : Fin 32,
      (Vector.map (Expression.eval env) (majExpr input_var_a (constWord32 h0_0) (constWord32 h0_1)))[i]
        = input_a[i] * (Vector.map (Expression.eval env) (constWord32 (p:=p) h0_0))[i]
          + (Vector.map (Expression.eval env) (constWord32 (p:=p) h0_1))[i]
            * (input_a[i] + (Vector.map (Expression.eval env) (constWord32 (p:=p) h0_0))[i]
              - 2 * (input_a[i] * (Vector.map (Expression.eval env) (constWord32 (p:=p) h0_0))[i])) := by
    intro i
    simp only [majExpr, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn, Expression.eval, h_eva]
    ring
  have s_maj : valueBits (Vector.map (Expression.eval env) (majExpr input_var_a (constWord32 h0_0) (constWord32 h0_1))) =
      Specs.SHA256.Maj (valueBits input_a) (valueBits (Vector.map (Expression.eval env) (constWord32 (p:=p) h0_0)))
        (valueBits (Vector.map (Expression.eval env) (constWord32 (p:=p) h0_1))) ∧
      Normalized (Vector.map (Expression.eval env) (majExpr input_var_a (constWord32 h0_0) (constWord32 h0_1))) :=
    Maj32.spec_of_constraint input_a (Vector.map (Expression.eval env) (constWord32 (p:=p) h0_0))
      (Vector.map (Expression.eval env) (constWord32 (p:=p) h0_1))
      (Vector.map (Expression.eval env) (majExpr input_var_a (constWord32 h0_0) (constWord32 h0_1))) ha_norm
      (SHA256Rounds.normalized_constWord32 env _) (SHA256Rounds.normalized_constWord32 env _) h_maj_eq
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env V)[k]'hk = Vector.map (Expression.eval env) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env V k hk, CircuitType.eval_var_fields]
  have s_newe := c_newe (by
    intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · exact SHA256Rounds.normalized_constWord32 env _
    · exact s_sig1.2
    · exact s_ch.2
    · rw [h_input_w]; exact hw_norm)
  have s_newa := c_newa (by
    intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · exact s_newe.2
    · exact s_sig0.2
    · exact s_maj.2
    · rw [SHA256Round.not32_eval env (constWord32 h0_2)]
      exact SHA256Round.normalized_not _ (SHA256Rounds.normalized_constWord32 env _))
  clear c_sig1 c_sig0 c_newe c_newa
  have modc : ∀ dv t1 y5 y6 : ℕ, dv < 2^32 →
      (_root_.add32 dv t1 + y5 + y6 + (2^32 - 1 - dv) + 1) % 2 ^ 32 =
        _root_.add32 t1 (_root_.add32 y5 y6) := by
    intro dv t1 y5 y6 hdv; unfold _root_.add32; omega
  have v_newe : valueBits (Vector.map (Expression.eval env)
        (Vector.mapRange 32 fun i ↦ var { index := i₀ + 32 + 32 + i })) =
      _root_.add32 (Specs.SHA256.H0[2])
        (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (Specs.SHA256.H0[6])
            (Specs.SHA256.upperSigma1 (valueBits input_e)))
            (Specs.SHA256.Ch (valueBits input_e) (Specs.SHA256.H0[4]) (Specs.SHA256.H0[5])))
            ((Specs.SHA256.K[1]).toNat)) (valueBits input_w)) := by
    rw [s_newe.1, Fin.sum_univ_four]
    simp only [Fin.getElem_fin, red,
      show ((0:Fin 4):ℕ)=0 from rfl, show ((1:Fin 4):ℕ)=1 from rfl, show ((2:Fin 4):ℕ)=2 from rfl,
      show ((3:Fin 4):ℕ)=3 from rfl,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [SHA256Rounds.valueBits_constWord32_of_lt env dhkC_lt,
      s_sig1.1, s_ch.1,
      SHA256Rounds.valueBits_constWord32_of_lt env Round0Block1.h0_4_lt,
      SHA256Rounds.valueBits_constWord32_of_lt env Round0Block1.h0_5_lt, h_input_w,
      Round0Block1.h0_4_eq, Round0Block1.h0_5_eq]
    exact mod_dhkC _ _ _
  have v_newa : valueBits (Vector.map (Expression.eval env)
        (Vector.mapRange 32 fun i ↦ var { index := i₀ + 32 + 32 + 33 + i })) =
      _root_.add32
        (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (Specs.SHA256.H0[6])
            (Specs.SHA256.upperSigma1 (valueBits input_e)))
            (Specs.SHA256.Ch (valueBits input_e) (Specs.SHA256.H0[4]) (Specs.SHA256.H0[5])))
            ((Specs.SHA256.K[1]).toNat)) (valueBits input_w))
        (_root_.add32 (Specs.SHA256.upperSigma0 (valueBits input_a))
            (Specs.SHA256.Maj (valueBits input_a) (Specs.SHA256.H0[0]) (Specs.SHA256.H0[1]))) := by
    rw [s_newa.1, Fin.sum_univ_four]
    simp only [Fin.getElem_fin, red,
      show ((0:Fin 4):ℕ)=0 from rfl, show ((1:Fin 4):ℕ)=1 from rfl, show ((2:Fin 4):ℕ)=2 from rfl,
      show ((3:Fin 4):ℕ)=3 from rfl,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [v_newe, s_sig0.1, s_maj.1,
      SHA256Rounds.valueBits_constWord32_of_lt env Round0Block1.h0_0_lt,
      SHA256Rounds.valueBits_constWord32_of_lt env Round0Block1.h0_1_lt,
      SHA256Round.not32_eval env (constWord32 h0_2),
      SHA256Round.valueBits_not (Vector.map (Expression.eval env) (constWord32 (p:=p) h0_2))
        (SHA256Rounds.normalized_constWord32 env _),
      SHA256Rounds.valueBits_constWord32_of_lt env Round0Block1.h0_2_lt,
      Round0Block1.h0_0_eq, Round0Block1.h0_1_eq, Round0Block1.h0_2_eq]
    exact modc _ _ _ _ (by rw [← Round0Block1.h0_2_eq]; exact Round0Block1.h0_2_lt)
  refine ⟨?_, ?_⟩
  · simp only [eval_vector, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, circuit_norm]
    rw [sha256Round_r1state]
    simp only [Vector.getElem_map]
    rw [v_newa, v_newe, h_input_a, h_input_e,
      SHA256Rounds.valueBits_constWord32_of_lt env Round0Block1.h0_0_lt,
      SHA256Rounds.valueBits_constWord32_of_lt env Round0Block1.h0_1_lt,
      SHA256Rounds.valueBits_constWord32_of_lt env Round0Block1.h0_4_lt,
      SHA256Rounds.valueBits_constWord32_of_lt env Round0Block1.h0_5_lt,
      Round0Block1.h0_0_eq, Round0Block1.h0_1_eq, Round0Block1.h0_4_eq, Round0Block1.h0_5_eq]
  · intro i
    fin_cases i <;>
      (rw [red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · exact s_newa.2
    · rw [h_input_a]; exact ha_norm
    · exact SHA256Rounds.normalized_constWord32 env _
    · exact SHA256Rounds.normalized_constWord32 env _
    · exact s_newe.2
    · rw [h_input_e]; exact he_norm
    · exact SHA256Rounds.normalized_constWord32 env _
    · exact SHA256Rounds.normalized_constWord32 env _

set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [main, UpperSigma1.circuit, UpperSigma0.circuit,
    AddMany.circuit2, AddMany.circuit2c]
  obtain ⟨ha_norm, he_norm, hw_norm⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_e, h_input_w⟩ := h_input
  simp only [UpperSigma1.Assumptions, UpperSigma0.Assumptions,
    UpperSigma1.Spec, UpperSigma0.Spec,
    AddMany.Assumptions, AddMany.Spec, AddMany.Spec2c, and_imp] at h_env ⊢
  obtain ⟨e_sig1, e_sig0, e_newe, -⟩ := h_env
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env.toEnvironment V)[k]'hk = Vector.map (Expression.eval env.toEnvironment) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env.toEnvironment V k hk, CircuitType.eval_var_fields]
  have n_e : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_e) := by
    rw [h_input_e]; exact he_norm
  have n_a : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_a) := by
    rw [h_input_a]; exact ha_norm
  -- affine Ch(e, H0_4, H0_5): per-bit constraint feeding `Ch32.spec_of_constraint`
  have h_ch_eq : ∀ i : Fin 32,
      (Vector.map (Expression.eval env.toEnvironment) (chExpr input_var_e (constWord32 h0_4) (constWord32 h0_5)))[i]
        = (Vector.map (Expression.eval env.toEnvironment) (constWord32 (p:=p) h0_5))[i]
          + (Vector.map (Expression.eval env.toEnvironment) input_var_e)[i]
            * ((Vector.map (Expression.eval env.toEnvironment) (constWord32 (p:=p) h0_4))[i]
              - (Vector.map (Expression.eval env.toEnvironment) (constWord32 (p:=p) h0_5))[i]) := by
    intro i
    simp only [chExpr, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn, Expression.eval]
    ring
  have s_ch := Ch32.spec_of_constraint (Vector.map (Expression.eval env.toEnvironment) input_var_e)
    (Vector.map (Expression.eval env.toEnvironment) (constWord32 (p:=p) h0_4))
    (Vector.map (Expression.eval env.toEnvironment) (constWord32 (p:=p) h0_5))
    (Vector.map (Expression.eval env.toEnvironment) (chExpr input_var_e (constWord32 h0_4) (constWord32 h0_5)))
    n_e (SHA256Rounds.normalized_constWord32 env.toEnvironment _)
    (SHA256Rounds.normalized_constWord32 env.toEnvironment _) h_ch_eq
  -- affine Maj(a, H0_0, H0_1): per-bit constraint feeding `Maj32.spec_of_constraint`
  have h_maj_eq : ∀ i : Fin 32,
      (Vector.map (Expression.eval env.toEnvironment) (majExpr input_var_a (constWord32 h0_0) (constWord32 h0_1)))[i]
        = (Vector.map (Expression.eval env.toEnvironment) input_var_a)[i]
            * (Vector.map (Expression.eval env.toEnvironment) (constWord32 (p:=p) h0_0))[i]
          + (Vector.map (Expression.eval env.toEnvironment) (constWord32 (p:=p) h0_1))[i]
            * ((Vector.map (Expression.eval env.toEnvironment) input_var_a)[i]
              + (Vector.map (Expression.eval env.toEnvironment) (constWord32 (p:=p) h0_0))[i]
              - 2 * ((Vector.map (Expression.eval env.toEnvironment) input_var_a)[i]
                * (Vector.map (Expression.eval env.toEnvironment) (constWord32 (p:=p) h0_0))[i])) := by
    intro i
    simp only [majExpr, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn, Expression.eval]
    ring
  have s_maj := Maj32.spec_of_constraint (Vector.map (Expression.eval env.toEnvironment) input_var_a)
    (Vector.map (Expression.eval env.toEnvironment) (constWord32 (p:=p) h0_0))
    (Vector.map (Expression.eval env.toEnvironment) (constWord32 (p:=p) h0_1))
    (Vector.map (Expression.eval env.toEnvironment) (majExpr input_var_a (constWord32 h0_0) (constWord32 h0_1)))
    n_a (SHA256Rounds.normalized_constWord32 env.toEnvironment _)
    (SHA256Rounds.normalized_constWord32 env.toEnvironment _) h_maj_eq
  have s_sig1 := e_sig1 he_norm
  have s_sig0 := e_sig0 ha_norm
  have s_newe := e_newe (by
    intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · exact SHA256Rounds.normalized_constWord32 env.toEnvironment _
    · exact s_sig1.2
    · exact s_ch.2
    · rw [h_input_w]; exact hw_norm)
  refine ⟨he_norm, ha_norm, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · exact SHA256Rounds.normalized_constWord32 env.toEnvironment _
    · exact s_sig1.2
    · exact s_ch.2
    · rw [h_input_w]; exact hw_norm
  · intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · exact s_newe.2
    · exact s_sig0.2
    · exact s_maj.2
    · rw [SHA256Round.not32_eval env.toEnvironment (constWord32 h0_2)]
      exact SHA256Round.normalized_not _ (SHA256Rounds.normalized_constWord32 env.toEnvironment _)

def circuit : FormalCircuit (F p) Inputs SHA256State where
  main; elaborated; Assumptions; Spec; soundness; completeness

end Round1Block1
end Solution.SHA256
end
