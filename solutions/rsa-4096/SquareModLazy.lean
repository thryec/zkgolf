import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulMod
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulModLazy

/-!
# RSA *lazy* modular squaring (gadget G5′-lazy)

`SquareModLazy` certifies `c ≡ a·a (mod n)` (lazy: `NormalizeTight`, no `LessThan`) over normalized big integers, like `MulMod`
but exploiting the symmetry of the product matrix `a[i]·a[j] = a[j]·a[i]`. Instead
of witnessing all `m²` partial products it witnesses only the `m(m+1)/2`
upper-triangular products, then *mirrors* them into the full `m×m` matrix
(`sqMatrix`) and reuses `bigIntMulVars`. Since the mirrored matrix evaluates
exactly like the full product matrix of `a·a`, the entire `MulMod` arithmetic core
(`mulMod_*_core_wm`) is reused verbatim.

The saving is `m² − m(m+1)/2 = m(m−1)/2` cells and rows per squaring.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

namespace SquareModLazy

/-! ## Triangular indexing of the upper-triangular pairs `{(i,j) : i ≤ j < m}` -/

/-- Triangular number `tri m = 0+1+…+m`, defined recursively (no division). -/
def tri : ℕ → ℕ
  | 0 => 0
  | (n + 1) => tri n + (n + 1)

lemma tri_succ (n : ℕ) : tri (n + 1) = tri n + (n + 1) := rfl

lemma tri_mono {j m : ℕ} (h : j ≤ m) : tri j ≤ tri m := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => rw [tri_succ]; omega

/-- Column-major enumeration of pairs `(i, j)`, `i ≤ j < m`. -/
def triCols (m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap fun j => (List.range (j + 1)).map fun i => (i, j)

lemma triCols_length (m : ℕ) : (triCols m).length = tri m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [triCols, List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      List.length_map, List.length_range]
    rw [show ((List.range k).flatMap fun j => (List.range (j+1)).map fun i => (i,j)) = triCols k from rfl,
      ih, tri_succ]

lemma triCols_succ (m : ℕ) :
    triCols (m + 1) = triCols m ++ (List.range (m + 1)).map (fun i => (i, m)) := by
  conv_lhs => rw [triCols, List.range_succ, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

lemma triCols_getElem (i j m : ℕ) (hij : i ≤ j) (hj : j < m) :
    (triCols m)[tri j + i]? = some (i, j) := by
  induction m with
  | zero => omega
  | succ k ih =>
    rw [triCols_succ]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · have hlt : tri j + i < tri k := by
        have h1 : tri (j + 1) ≤ tri k := tri_mono (by omega)
        rw [tri_succ] at h1; omega
      rw [List.getElem?_append_left (by rw [triCols_length]; exact hlt)]
      exact ih (by omega)
    · have hjk' : j = k := by omega
      subst hjk'
      have hik : i < j + 1 := by omega
      rw [List.getElem?_append_right (by rw [triCols_length]; omega), triCols_length,
        Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_range hik]
      rfl

/-- Decode a flat triangular index back to its pair. -/
def sqDecode (m t : ℕ) : ℕ × ℕ := (triCols m).getD t (0, 0)

lemma sqDecode_idx (i j m : ℕ) (hij : i ≤ j) (hj : j < m) :
    sqDecode m (tri j + i) = (i, j) := by
  rw [sqDecode, List.getD_eq_getElem?_getD, triCols_getElem i j m hij hj]; rfl

lemma triCols_bounds (m : ℕ) {x : ℕ × ℕ} (hx : x ∈ triCols m) : x.1 ≤ x.2 ∧ x.2 < m := by
  rw [triCols, List.mem_flatMap] at hx
  obtain ⟨j, hj, hx⟩ := hx
  rw [List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [List.mem_range] at hj hi
  exact ⟨by omega, hj⟩

lemma sqDecode_lt (m t : ℕ) (ht : t < tri m) :
    (sqDecode m t).1 ≤ (sqDecode m t).2 ∧ (sqDecode m t).2 < m := by
  apply triCols_bounds
  rw [sqDecode, List.getD_eq_getElem?_getD]
  have hlt : t < (triCols m).length := by rw [triCols_length]; exact ht
  rw [List.getElem?_eq_getElem hlt]
  exact List.getElem_mem hlt

/-- Column-major flat index of an upper-triangular pair. -/
def sqIdx (i j : ℕ) : ℕ := tri j + i

lemma sqIdx_lt {i j m : ℕ} (hj : j < m) (hij : i ≤ j) : sqIdx i j < tri m := by
  rw [sqIdx]
  have h1 : tri (j + 1) ≤ tri m := tri_mono (by omega)
  rw [tri_succ] at h1; omega

variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

/-- The upper-triangular pair (as bounded indices) at flat position `t`. -/
def sqPair (t : Fin (tri m)) : Fin m × Fin m :=
  (⟨(sqDecode m t.val).1,
      lt_of_le_of_lt (sqDecode_lt m t.val t.isLt).1 (sqDecode_lt m t.val t.isLt).2⟩,
   ⟨(sqDecode m t.val).2, (sqDecode_lt m t.val t.isLt).2⟩)

omit [NeZero m] in
lemma sqPair_idx {mn mx : ℕ} (hmn : mn ≤ mx) (hmx : mx < m) (h : sqIdx mn mx < tri m) :
    sqPair ⟨sqIdx mn mx, h⟩ = (⟨mn, lt_of_le_of_lt hmn hmx⟩, ⟨mx, hmx⟩) := by
  have hd : sqDecode m (sqIdx mn mx) = (mn, mx) := by rw [sqIdx]; exact sqDecode_idx mn mx m hmn hmx
  apply Prod.ext <;> apply Fin.ext <;> simp only [sqPair, hd]

/-- Mirror the `m(m+1)/2` triangular products into the full `m×m` matrix:
entry `(r,c)` reads the witnessed product for the sorted pair `(min r c, max r c)`. -/
def sqMatrix (pp : Vector (Expression (F p)) (tri m)) :
    Vector (Expression (F p)) (m * m) :=
  Vector.ofFn fun t : Fin (m * m) =>
    pp[sqIdx (min (t.val / m) (t.val % m)) (max (t.val / m) (t.val % m))]'(by
      have hc : t.val % m < m := Nat.mod_lt _ (Nat.pos_of_neZero m)
      have hr : t.val / m < m := Nat.div_lt_of_lt_mul t.isLt
      exact sqIdx_lt (max_lt hr hc) (min_le_max))

/-! ## `witnessedSquare`: witness the triangular products, mirror to the full matrix -/

/-- Witness the `m(m+1)/2` upper-triangular partial products `a[i]·a[j]` (`i ≤ j`)
as fresh cells, assert each equals `a[i]·a[j]`, and return the *affine* convolution
coefficient vector of `a·a`, obtained by mirroring the triangular products into the
full `m×m` matrix (`sqMatrix`) and reusing `bigIntMulVars`. -/
def witnessedSquare (a : Var (BigInt m) (F p)) :
    Circuit (F p) (Vector (Expression (F p)) (2 * m - 1)) := do
  let pp ← ProvableType.witness (α := fields (tri m)) fun env =>
    Vector.ofFn fun t : Fin (tri m) =>
      (Expression.eval env.toEnvironment (a[(sqPair t).1.val]'(sqPair t).1.isLt))
        * (Expression.eval env.toEnvironment (a[(sqPair t).2.val]'(sqPair t).2.isLt))
  let constraints : Vector (Expression (F p)) (tri m) :=
    Vector.mapFinRange (tri m) fun t =>
      (a[(sqPair t).1.val]'(sqPair t).1.isLt)
        * (a[(sqPair t).2.val]'(sqPair t).2.isLt)
        - pp[t.val]
  Circuit.forEach constraints assertZero
  return bigIntMulVars (sqMatrix pp)

/-- The output of `witnessedSquare a off` is `bigIntMulVars` of the mirrored full
matrix over the freshly witnessed triangular products at offset `off`. -/
lemma witnessedSquare_output (off : ℕ) (a : Var (BigInt m) (F p)) :
    (witnessedSquare a off).1
      = bigIntMulVars (sqMatrix (Vector.mapRange (tri m) fun i => var (F := F p) { index := off + i })) := by
  simp only [witnessedSquare, circuit_norm]

/-- `witnessedSquare a` allocates exactly `tri m = m(m+1)/2` cells. -/
lemma witnessedSquare_localLength (off : ℕ) (a : Var (BigInt m) (F p)) :
    Operations.localLength (witnessedSquare a off).2 = tri m := by
  simp only [witnessedSquare, circuit_norm, Nat.mul_zero, Nat.add_zero]

/-- Soundness reading of the `witnessedSquare` operations: every product assert
holds, i.e. `a[sqPair(t).1]·a[sqPair(t).2] = env.get (off + t)` for each `t`. -/
lemma witnessedSquare_soundness (off : ℕ) (a : Var (BigInt m) (F p)) (env : Environment (F p))
    (h : Operations.forAllNoOffset
        { assert := fun e => Expression.eval env e = 0, lookup := fun l => l.Soundness env,
          interact := fun i => i.Guarantees env, subcircuit := fun {_n} s => s.Assumptions env → s.Spec env }
        (witnessedSquare a off).2) :
    ∀ t : Fin (tri m),
      Expression.eval env (a[(sqPair t).1.val]'(sqPair t).1.isLt)
          * Expression.eval env (a[(sqPair t).2.val]'(sqPair t).2.isLt)
        = env.get (off + t.val) := by
  simp only [witnessedSquare, circuit_norm] at h
  intro t; have := h t; rw [add_neg_eq_zero] at this; exact this

/-- **Eval bridge (matrix form).** If the triangular product witnesses hold, then
the mirrored full matrix `sqMatrix pp` evaluates like the full product matrix of
`a·a`, so `bigIntMulVars (sqMatrix pp)` matches `bigIntMulNoReduce a a`. This is the
only fact `SquareMod` needs to reuse the `MulMod` arithmetic core with `b = a`. -/
lemma witnessedSquare_map_eval (env : Environment (F p)) (off : ℕ) (a : Var (BigInt m) (F p))
    (hprod : ∀ t : Fin (tri m),
      Expression.eval env (a[(sqPair t).1.val]'(sqPair t).1.isLt)
          * Expression.eval env (a[(sqPair t).2.val]'(sqPair t).2.isLt)
        = env.get (off + t.val)) :
    Vector.map (Expression.eval env)
        (bigIntMulVars (sqMatrix (Vector.mapRange (tri m) fun i => var (F := F p) { index := off + i })))
      = Vector.map (Expression.eval env) (bigIntMulNoReduce a a) := by
  apply map_eval_bigIntMulVars_eq env a a
  intro i j
  -- proof-irrelevant eval of a bounded index
  have acong : ∀ (k1 k2 : ℕ) (h1 : k1 < m) (h2 : k2 < m), k1 = k2 →
      Expression.eval env (a[k1]'h1) = Expression.eval env (a[k2]'h2) := by
    intro k1 k2 h1 h2 he; subst he; rfl
  have hd : (i.val * m + j.val) / m = i.val := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_neZero m), Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  have hr : (i.val * m + j.val) % m = j.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt j.isLt
  have hmx : max i.val j.val < m := max_lt i.isLt j.isLt
  have hlt : sqIdx (min i.val j.val) (max i.val j.val) < tri m := sqIdx_lt hmx min_le_max
  have hprod' := hprod ⟨sqIdx (min i.val j.val) (max i.val j.val), hlt⟩
  rw [sqPair_idx min_le_max hmx hlt] at hprod'
  -- LHS: sqMatrix reads the mirrored (sorted-pair) witness cell
  have hL : Expression.eval env
        ((sqMatrix (Vector.mapRange (tri m) fun i => var (F := F p) { index := off + i }))[i.val * m + j.val]'(by
          have := i.isLt; have := j.isLt
          calc i.val * m + j.val < i.val * m + m := by omega
            _ = (i.val + 1) * m := by ring
            _ ≤ m * m := by apply Nat.mul_le_mul_right; omega))
      = env.get (off + sqIdx (min i.val j.val) (max i.val j.val)) := by
    simp only [sqMatrix, Vector.getElem_ofFn, hd, hr, Vector.getElem_mapRange]
    rfl
  rw [hL, ← hprod']
  -- commutativity: a[min]·a[max] = a[i]·a[j]
  rcases le_total i.val j.val with h | h
  · rw [acong _ i.val _ i.isLt (min_eq_left h), acong _ j.val _ j.isLt (max_eq_right h)]
  · rw [acong _ j.val _ j.isLt (min_eq_right h), acong _ i.val _ i.isLt (max_eq_left h), mul_comm]

/-- **Eval bridge (coefficient form).** Each output coefficient of `witnessedSquare`
evaluates like the corresponding schoolbook coefficient of `a·a`. -/
lemma witnessedSquare_eval_bridge (env : Environment (F p)) (off : ℕ) (a : Var (BigInt m) (F p))
    (h_prod : ∀ t : Fin (tri m),
      Expression.eval env (a[(sqPair t).1.val]'(sqPair t).1.isLt)
          * Expression.eval env (a[(sqPair t).2.val]'(sqPair t).2.isLt)
        = env.get (off + t.val)) :
    ∀ k : Fin (2 * m - 1),
      Expression.eval env (witnessedSquare a off).1[k.val]
        = Expression.eval env (bigIntMulNoReduce a a)[k.val] := by
  intro k
  rw [witnessedSquare_output off a]
  have hvec := witnessedSquare_map_eval env off a h_prod
  have := congrArg (fun v => v[k.val]) hvec
  simpa only [Vector.getElem_map] using this

/-- The `witnessedSquare` operations carry no requirements (only asserts). -/
lemma witnessedSquare_requirements (off : ℕ) (a : Var (BigInt m) (F p)) (env : Environment (F p)) :
    Operations.forAllNoOffset
      { interact := fun i => i.Requirements env,
        subcircuit := fun {_n} s => s.channelsWithRequirements = [] ∨ s.Assumptions env }
      (witnessedSquare a off).2 := by
  simp only [witnessedSquare, circuit_norm]

/-- From `UsesLocalWitnessesCompleteness`: the product witnesses take their intended
values `env.get (off+t) = a[sqPair(t).1]·a[sqPair(t).2]`. -/
lemma witnessedSquare_usesLocalWitnesses (off off' : ℕ) (a : Var (BigInt m) (F p))
    (penv : ProverEnvironment (F p)) (heq : off' = off)
    (h : penv.UsesLocalWitnessesCompleteness off' (witnessedSquare a off).2) :
    ∀ t : Fin (tri m), penv.toEnvironment.get (off + t.val)
        = Expression.eval penv.toEnvironment (a[(sqPair t).1.val]'(sqPair t).1.isLt)
            * Expression.eval penv.toEnvironment (a[(sqPair t).2.val]'(sqPair t).2.isLt) := by
  subst heq
  simp only [witnessedSquare, circuit_norm] at h
  intro t
  have := h t
  simpa only [Vector.getElem_ofFn] using this

/-- Completeness reading: if every product witness holds, the `witnessedSquare`
operations are satisfiable. -/
lemma witnessedSquare_completeness (off : ℕ) (a : Var (BigInt m) (F p)) (penv : ProverEnvironment (F p))
    (h : ∀ t : Fin (tri m), penv.toEnvironment.get (off + t.val)
        = Expression.eval penv.toEnvironment (a[(sqPair t).1.val]'(sqPair t).1.isLt)
            * Expression.eval penv.toEnvironment (a[(sqPair t).2.val]'(sqPair t).2.isLt)) :
    Operations.forAllNoOffset
      { assert := fun e => Expression.eval penv.toEnvironment e = 0,
        lookup := fun l => l.Completeness penv.toEnvironment,
        interact := fun i => i.Guarantees penv.toEnvironment, subcircuit := fun {_n} s => s.ProverAssumptions penv }
      (witnessedSquare a off).2 := by
  simp only [witnessedSquare, circuit_norm]
  intro t; rw [h t]; ring

/-! ## The `SquareMod` formal circuit -/

/-- Inputs of `SquareModLazy`: the operand `a` and the `modulus`. -/
structure Inputs (m : ℕ) (F : Type) where
  a : BigInt m F
  modulus : BigInt m F
deriving ProvableStruct

/-- Natural-number value of a witnessed limb vector (used only in witness generators). -/
private def evalValue (B : ℕ) (env : ProverEnvironment (F p))
    (x : Var (BigInt m) (F p)) : ℕ :=
  Specs.RSA.fromLimbs B ((x.map (Expression.eval env.toEnvironment)).toList.map ZMod.val)

/-- The `main` circuit of `SquareModLazy`: witness `q = a²/n`, `r = a²%n`,
tight-normalize `q` (top limb `< 2^(tb+1)`: the honest quotient is
`< 2^((m-1)B + tb + 1)` since `n ≥ 2^((m-1)B + tb - 1)`), tight-normalize `r`,
certify `a·a = q·n + r`, and return `r`. Like `MulModLazy` there is no
`LessThan` — only congruence mod `n` is certified. -/
def main (P : BigIntParams p m) (tb : ℕ) (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htbB : tb + 2 ≤ P.B)
    [Fact (p > 2)] (input : Var (Inputs m) (F p)) :
    Circuit (F p) (Var (BigInt m) (F p)) := do
  let a := input.a
  let n := input.modulus

  let q ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env a * evalValue P.B env a
    let qval : ℕ := prod / evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((qval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)
  let r ← ProvableType.witness (α := BigInt m) fun env =>
    let prod := evalValue P.B env a * evalValue P.B env a
    let rval : ℕ := prod % evalValue P.B env n
    Vector.ofFn fun k : Fin m => ((rval / 2 ^ (P.B * k.val) % 2 ^ P.B : ℕ) : F p)

  NormalizeTight.circuit P (tb + 2)
    ⟨by omega, lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) htbB) P.hB⟩
    htbB q
  NormalizeTight.circuit P tb htb (Nat.le_of_succ_le (Nat.le_of_succ_le htbB)) r

  let Pc ← MulMod.interpolatedMul a a
  let Sqn ← MulMod.interpolatedMul q n
  let S : Vector (Expression (F p)) (2 * m - 1) := Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then Sqn[k.val] + r[k.val]'h else Sqn[k.val]

  EqViaCarries.circuit P { lhs := Pc, rhs := S }
  return r

instance elaborated (P : BigIntParams p m) (tb : ℕ) (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htbB : tb + 2 ≤ P.B)
    [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) (BigInt m) (main P tb htb htbB) where
  localLength _ :=
    m + m + ((m - 1) * (P.B - 1) + (tb + 2 - 1)) + ((m - 1) * (P.B - 1) + (tb - 1))
      + (2 * m - 1) + (2 * m - 1)
      + ((2 * m - 1 - 1) * (P.W - 1) + (2 * m - 1 - 1))
  output _ i0 := varFromOffset (BigInt m) (i0 + m)
  localLength_eq := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, circuit_norm, Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, EqViaCarries.circuit, EqViaCarries.elaborated,
      EqViaCarries.main, RangeCheck.circuit, Gadgets.ToBits.rangeCheck]
    omega
  output_eq := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, circuit_norm, Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, EqViaCarries.circuit, EqViaCarries.elaborated,
      EqViaCarries.main, RangeCheck.circuit, Gadgets.ToBits.rangeCheck]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, MulMod.interpolatedMul, circuit_norm, Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, EqViaCarries.circuit, EqViaCarries.elaborated,
      EqViaCarries.main, RangeCheck.circuit, Gadgets.ToBits.rangeCheck]
  channelsLawful := by
    intro input offset
    simp only [main, MulMod.interpolatedMul, circuit_norm, Normalize.circuit,
      Normalize.elaborated, Normalize.main, NormalizeTight.circuit, NormalizeTight.elaborated,
      NormalizeTight.main, EqViaCarries.circuit, EqViaCarries.elaborated,
      EqViaCarries.main, RangeCheck.circuit, Gadgets.ToBits.rangeCheck]

/-- Preconditions for lazy modular squaring: `a`, `n` normalized; `a`, `n` both
`< 2^((m-1)B+tb)`; and the modulus lower bound `2^((m-1)B+tb-1) ≤ n` (so the
honest quotient `q = ⌊a²/n⌋` is `< 2^((m-1)B+tb+1)`, fitting `m` limbs with a
`tb+1`-bit top limb). -/
def Assumptions (B tb : ℕ) (input : Inputs m (F p)) : Prop :=
  let a := input.a
  let n := input.modulus
  a.Normalized B ∧ n.Normalized B ∧
    a.value B < 2 ^ ((m - 1) * B + tb) ∧
    n.value B < 2 ^ ((m - 1) * B + tb) ∧ 0 < n.value B ∧
    2 ^ ((m - 1) * B + tb) ≤ 4 * n.value B

/-- Postcondition: the output is tight-normalized and **congruent** to `a·a` mod `n`. -/
def Spec (B tb : ℕ) (input : Inputs m (F p)) (out : BigInt m (F p)) : Prop :=
  let a := input.a
  let n := input.modulus
  BigInt.NormalizedTight B tb out ∧ out.value B % n.value B = (a.value B * a.value B) % n.value B

/-- The `SquareModLazy` formal circuit: `c ≡ a · a (mod n)` over normalized big
integers, with `c` tight-normalized (`< 2^((m-1)B+tb)`). -/
def circuit (P : BigIntParams p m) (tb : ℕ) (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htbB : tb + 2 ≤ P.B)
    [Fact (p > 2)] :
    FormalCircuit (F p) (Inputs m) (BigInt m) where
    main := main P tb htb htbB
    Assumptions := Assumptions P.B tb
    Spec := Spec P.B tb
    soundness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
        NormalizeTight.Assumptions, NormalizeTight.Spec,
        EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
        EqViaCarries.Assumptions, EqViaCarries.Spec]
      obtain ⟨ha_norm, hn_norm, hab_ltT, hn_ltT, hn_pos, hn_ge⟩ := h_assumptions
      obtain ⟨hq_tight, hr_tight, hSq_ops, hQN_ops, h_eq_impl⟩ := h_holds
      have hpm : 2 * m - 1 < p := MulMod.two_m_sub_one_lt hp
      have h_pSq := MulMod.interpolatedMul_soundness (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))
        input_var.a input_var.a env hSq_ops
      have h_pQN := MulMod.interpolatedMul_soundness
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
          (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus env hQN_ops
      refine ⟨⟨hr_tight, ?_⟩, MulMod.interpolatedMul_requirements _ _ _ _, MulMod.interpolatedMul_requirements _ _ _ _⟩
      have h_input' : (Vector.map (Expression.eval env) input_var.a,
          Vector.map (Expression.eval env) input_var.a,
          Vector.map (Expression.eval env) input_var.modulus)
            = ((input.a, input.a, input.modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [← h_input]
      have heqSq_get := MulMod.interpolatedMul_eval_bridge env (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))
        input_var.a input_var.a hpm h_pSq
      have heqQN_get := MulMod.interpolatedMul_eval_bridge env
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
          (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus hpm h_pQN
      exact (MulMod.mulMod_soundness_core_wm_lazy (B := B) hp i₀ env
        input_var.a input_var.a input_var.modulus
        (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).1
        (MulMod.interpolatedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus
          (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
            (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)).1
        (input.a, input.a, input.modulus) h_input' ha_norm ha_norm hn_norm hq_tight.1 hr_tight.1
        heqSq_get heqQN_get h_eq_impl).2
    completeness := by
      obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
      circuit_proof_start [Normalize.circuit, Normalize.elaborated, Normalize.main,
        Normalize.Assumptions, Normalize.Spec,
        NormalizeTight.circuit, NormalizeTight.elaborated, NormalizeTight.main,
        NormalizeTight.Assumptions, NormalizeTight.Spec,
        EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
        EqViaCarries.Assumptions, EqViaCarries.Spec]
      obtain ⟨ha_norm, hn_norm, hab_ltT, hn_ltT, hn_pos, hn_ge⟩ := h_assumptions
      have hn_big : 2 ^ (2 * ((m - 1) * B + tb)) ≤ BigInt.value B input.modulus * 2 ^ (B * m) :=
        MulMod.hn_big_of_ge4 htbB hn_ge
      obtain ⟨hq_env, hr_env, hSq_uses, hQN_uses⟩ := h_env
      have h_pvSq := MulMod.interpolatedMul_usesLocalWitnesses (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1))) input_var.a input_var.a env rfl hSq_uses
      have h_pvQN := MulMod.interpolatedMul_usesLocalWitnesses
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
          (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)
        (Operations.localLength (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2
          + (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1))))
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus env
        (Nat.add_comm _ _) hQN_uses
      have heva : evalValue B env input_var.a = BigInt.value B input.a := by
        rw [evalValue, BigInt.value, ← h_input]
      have hevn : evalValue B env input_var.modulus = BigInt.value B input.modulus := by
        rw [evalValue, BigInt.value, ← h_input]
      have hqwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + i.val)
          = ((BigInt.value B input.a * BigInt.value B input.a / BigInt.value B input.modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hq_env i, Vector.getElem_ofFn, heva, hevn]
      have hrwit : ∀ i : Fin m, env.toEnvironment.get (i₀ + m + i.val)
          = ((BigInt.value B input.a * BigInt.value B input.a % BigInt.value B input.modulus
              / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p) := by
        intro i; rw [hr_env i, Vector.getElem_ofFn, heva, hevn]
      have h_input' : (Vector.map (Expression.eval env.toEnvironment) input_var.a,
          Vector.map (Expression.eval env.toEnvironment) input_var.a,
          Vector.map (Expression.eval env.toEnvironment) input_var.modulus)
            = ((input.a, input.a, input.modulus) :
              ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p)) := by
        simp only [← h_input]
      have heqSq_get := MulMod.interpolatedMul_eval_bridge_uses env.toEnvironment
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1))) input_var.a input_var.a h_pvSq
      have heqQN_get := MulMod.interpolatedMul_eval_bridge_uses env.toEnvironment
        (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
          (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)
        (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus h_pvQN
      have core := MulMod.mulMod_completeness_core_wm_lazy (B := B) (tb := tb) hB
        (Nat.le_of_succ_le (Nat.le_of_succ_le htbB)) hp i₀ env.toEnvironment
        input_var.a input_var.a input_var.modulus
        (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).1
        (MulMod.interpolatedMul (Vector.mapRange m fun i => var { index := i₀ + i }) input_var.modulus
          (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1)) + Operations.localLength
            (MulMod.interpolatedMul input_var.a input_var.a (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1)))).2)).1
        (input.a, input.a, input.modulus) h_input' ha_norm ha_norm hn_norm
        hab_ltT hab_ltT hn_ltT hn_pos hn_big hqwit hrwit heqSq_get heqQN_get
      have hqtight := MulMod.qwit_tight4 (B := B) (tb := tb) (tq := tb + 2) hB htbB
        (Nat.le_refl _) i₀ env.toEnvironment
        (BigInt.value B input.a) (BigInt.value B input.a) (BigInt.value B input.modulus)
        hab_ltT hab_ltT hn_ge hqwit
      exact ⟨hqtight, core.2.1,
        MulMod.interpolatedMul_completeness (i₀ + m + m + ((m - 1) * (B - 1) + (tb + 2 - 1)) + ((m - 1) * (B - 1) + (tb - 1))) input_var.a input_var.a env h_pvSq,
        MulMod.interpolatedMul_completeness _ (Vector.mapRange m fun i => var { index := i₀ + i })
          input_var.modulus env h_pvQN,
        core.2.2⟩

end SquareModLazy
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
