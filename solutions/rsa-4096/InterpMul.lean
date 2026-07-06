import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulModTheorems
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Vandermonde

/-!
# xJsnark O(m) interpolation multiplication check (`interpolatedMul`)

Replaces the `m·m`-product `witnessedMul` gadget with the interpolation check:
witness the `2m-1` convolution coefficients directly, and pin them by evaluating
the product polynomial at the `2m-1` fixed points `1, 2, …, 2m-1`.

Cost drops from `⟨m·m, m·m⟩` to `⟨2m-1, 2m-1⟩`. The returned coefficient vector is
*affine* (just the witnessed cells), and each constraint
`(Σ_i a_i c^i)(Σ_i b_i c^i) − (Σ_k z_k c^k)` is a single R1CS row (affine·affine − affine).

Soundness (`interpolatedMul_map_eval`) uses the interpolation-uniqueness lemma
from `Vandermonde.lean`: the constraints force `z_k = conv_k` at `2m-1` distinct
points, so `z` evaluates to the schoolbook convolution `bigIntMulNoReduce a b`.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace MulMod

/-- Affine polynomial-evaluation expression `Σ_i coeffs[i] · x^i` for a constant
point `x : F p`. Built as a `Fin.foldl` of `+` and constant-`*`, mirroring
`fieldFromBitsExpr`, so it is affine whenever the `coeffs` are. -/
def polyEvalExpr {n : ℕ} (coeffs : Vector (Expression (F p)) n) (x : F p) : Expression (F p) :=
  Fin.foldl n (fun acc (i : Fin n) => acc + coeffs[i.val] * (x ^ i.val : F p)) 0

/-- `polyEvalExpr` evaluates to `Σ_i (eval coeffs[i]) · x^i`. -/
lemma polyEvalExpr_eval {n : ℕ} (env : Environment (F p))
    (coeffs : Vector (Expression (F p)) n) (x : F p) :
    Expression.eval env (polyEvalExpr coeffs x)
      = ∑ i : Fin n, (Expression.eval env coeffs[i.val]) * x ^ i.val := by
  simp only [polyEvalExpr]
  induction n with
  | zero => simp only [Fin.foldl_zero, Expression.eval, Finset.univ_eq_empty, Finset.sum_empty]
  | succ k ih =>
    obtain ih := ih coeffs.pop
    simp only [Vector.getElem_pop'] at ih
    rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
    simp only [Expression.eval, Fin.val_last, Fin.val_castSucc]
    rw [← ih]

/-- The interpolation multiplication gadget. Witness the `2m-1` convolution
coefficients `z`, then for each point `c ∈ {1,…,2m-1}` assert
`(Σ_i a_i c^i)(Σ_i b_i c^i) − (Σ_k z_k c^k) = 0`. Returns the affine vector `z`. -/
def interpolatedMul (a b : Var (BigInt m) (F p)) :
    Circuit (F p) (Vector (Expression (F p)) (2 * m - 1)) := do
  -- witness the 2m-1 convolution coefficients directly
  let z ← ProvableType.witness (α := fields (2 * m - 1)) fun env =>
    Vector.ofFn fun k : Fin (2 * m - 1) =>
      Expression.eval env.toEnvironment ((bigIntMulNoReduce a b)[k.val])
  -- for each c = cIdx+1 ∈ {1..2m-1}, assert (polyEval a c)(polyEval b c) = polyEval z c
  let constraints : Vector (Expression (F p)) (2 * m - 1) :=
    Vector.mapFinRange (2 * m - 1) fun cIdx =>
      let c : F p := ((cIdx.val + 1 : ℕ) : F p)
      polyEvalExpr a c * polyEvalExpr b c - polyEvalExpr z c
  Circuit.forEach constraints assertZero
  return z

/-- The output of `interpolatedMul a b off` is the affine vector of freshly
witnessed coefficient cells at offset `off`. -/
lemma interpolatedMul_output (off : ℕ) (a b : Var (BigInt m) (F p)) :
    (interpolatedMul a b off).1
      = (Vector.mapRange (2 * m - 1) fun i => var (F := F p) { index := off + i }) := by
  simp only [interpolatedMul, circuit_norm]

/-- `interpolatedMul a b` allocates exactly `2m-1` cells (the coefficient vector). -/
lemma interpolatedMul_localLength (off : ℕ) (a b : Var (BigInt m) (F p)) :
    Operations.localLength (interpolatedMul a b off).2 = 2 * m - 1 := by
  simp only [interpolatedMul, circuit_norm, Nat.mul_zero, Nat.add_zero]

/-- The witnessed coefficient vector `z` at offset `off`. -/
def zVec (m off : ℕ) : Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapRange (2 * m - 1) fun i => var (F := F p) { index := off + i }

/-- Soundness reading of the `interpolatedMul` operations: every point constraint
holds, i.e. for each `cIdx`, `polyEval a c · polyEval b c = polyEval z c` with
`c = cIdx+1` and `z = zVec off`. -/
lemma interpolatedMul_soundness (off : ℕ) (a b : Var (BigInt m) (F p)) (env : Environment (F p))
    (h : Operations.forAllNoOffset
        { assert := fun e => Expression.eval env e = 0, lookup := fun l => l.Soundness env,
          interact := fun i => i.Guarantees env, subcircuit := fun {_n} s => s.Assumptions env → s.Spec env }
        (interpolatedMul a b off).2) :
    ∀ cIdx : Fin (2 * m - 1),
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr (zVec m off) ((cIdx.val + 1 : ℕ) : F p)) := by
  simp only [interpolatedMul, circuit_norm, zVec] at h ⊢
  intro cIdx
  have hc := h cIdx
  simp only [Expression.eval] at hc
  rw [add_neg_eq_zero] at hc
  exact hc

/-- `2m-1 < p` follows from the `MulMod` field bound `hp : 2^(2B)·(m+1)·4 < p`. -/
lemma two_m_sub_one_lt {B : ℕ} (hp : 2 ^ (2 * B) * (m + 1) * 4 < p) :
    2 * m - 1 < p := by
  have hpow : 1 ≤ 2 ^ (2 * B) := Nat.one_le_two_pow
  have hge : 2 ^ (2 * B) * (m + 1) * 4 ≥ 1 * (m + 1) * 4 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hpow)
  omega

/-- The points `1, 2, …, 2m-1` embedded in `F p` are distinct, provided
`2m-1 ≤ p` (so no wraparound). -/
lemma interp_points_injective (hpm : 2 * m - 1 < p) :
    Function.Injective (fun cIdx : Fin (2 * m - 1) => (((cIdx.val + 1 : ℕ)) : F p)) := by
  intro i j hij
  simp only at hij
  have hi : i.val + 1 < p := by have := i.isLt; omega
  have hj : j.val + 1 < p := by have := j.isLt; omega
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hij
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  exact Fin.ext (by omega)

/-- **Soundness bridge.** From the point constraints, the witnessed coefficient
vector `z = zVec off` evaluates equal to the schoolbook convolution
`bigIntMulNoReduce a b`, coordinate-wise. This is the only fact the downstream
`MulMod` arithmetic cores consume. -/
lemma interpolatedMul_map_eval (env : Environment (F p)) (off : ℕ)
    (a b : Var (BigInt m) (F p)) (hpm : 2 * m - 1 < p)
    (hpts : ∀ cIdx : Fin (2 * m - 1),
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr (zVec m off) ((cIdx.val + 1 : ℕ) : F p))) :
    Vector.map (Expression.eval env) (zVec m off)
      = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
  have hm : 0 < m := Nat.pos_of_neZero m
  -- coefficient functions
  set u : Fin (2 * m - 1) → F p := fun k => Expression.eval env (zVec m off)[k.val] with hu
  set v : Fin (2 * m - 1) → F p := fun k => Expression.eval env (bigIntMulNoReduce a b)[k.val] with hv
  -- interpolation-uniqueness hypothesis: agreement at the 2m-1 points
  have hagree : ∀ cIdx : Fin (2 * m - 1),
      (∑ k : Fin (2 * m - 1), u k * (((cIdx.val + 1 : ℕ)) : F p) ^ k.val)
        = ∑ k : Fin (2 * m - 1), v k * (((cIdx.val + 1 : ℕ)) : F p) ^ k.val := by
    intro cIdx
    set c : F p := (((cIdx.val + 1 : ℕ)) : F p) with hcdef
    -- RHS of soundness = Σ_k u_k c^k
    have hz : Expression.eval env (polyEvalExpr (zVec m off) c)
        = ∑ k : Fin (2 * m - 1), u k * c ^ k.val := by
      rw [polyEvalExpr_eval]
    -- LHS of soundness = (Σ_i a_i c^i)(Σ_i b_i c^i)
    have hab : Expression.eval env (polyEvalExpr a c) * Expression.eval env (polyEvalExpr b c)
        = (∑ i : Fin m, Expression.eval env a[i.val] * c ^ i.val)
          * (∑ i : Fin m, Expression.eval env b[i.val] * c ^ i.val) := by
      rw [polyEvalExpr_eval, polyEvalExpr_eval]
    -- Cauchy: (Σa)(Σb) = Σ_k conv_k c^k, and conv_k = v_k
    have hcauchy := cauchy_diag hm
      (fun i : Fin m => Expression.eval env a[i.val])
      (fun i : Fin m => Expression.eval env b[i.val]) c
    have hconv : ∀ k : Fin (2 * m - 1),
        (∑ i : Fin m, if hh : i.val ≤ k.val ∧ k.val - i.val < m then
          (fun i : Fin m => Expression.eval env a[i.val]) i
            * (fun i : Fin m => Expression.eval env b[i.val]) ⟨k.val - i.val, hh.2⟩ else 0)
        = v k := by
      intro k
      show _ = Expression.eval env (bigIntMulNoReduce a b)[k.val]
      rw [eval_bigIntMulNoReduce_coeff env a b k]
    -- assemble
    have hsound := hpts cIdx
    rw [hz] at hsound
    rw [hab] at hsound
    rw [hcauchy] at hsound
    -- hsound : Σ_k conv_k c^k = Σ_k u_k c^k
    rw [← hsound]
    apply Finset.sum_congr rfl; intro k _
    rw [hconv k]
  -- apply interpolation-uniqueness
  have huniq := interp_uniqueness u v
    (fun cIdx : Fin (2 * m - 1) => (((cIdx.val + 1 : ℕ)) : F p))
    (interp_points_injective hpm) hagree
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, Vector.getElem_map]
  exact huniq ⟨k, hk⟩

/-- Per-element eval bridge for the `interpolatedMul` output: each coefficient of
the output evaluates like the schoolbook convolution `bigIntMulNoReduce a b`. -/
lemma interpolatedMul_eval_bridge (env : Environment (F p)) (off : ℕ) (a b : Var (BigInt m) (F p))
    (hpm : 2 * m - 1 < p)
    (hpts : ∀ cIdx : Fin (2 * m - 1),
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr (zVec m off) ((cIdx.val + 1 : ℕ) : F p))) :
    ∀ k : Fin (2 * m - 1),
      Expression.eval env (interpolatedMul a b off).1[k.val]
        = Expression.eval env (bigIntMulNoReduce a b)[k.val] := by
  intro k
  rw [interpolatedMul_output off a b]
  have hvec := interpolatedMul_map_eval env off a b hpm hpts
  have := congrArg (fun w => w[k.val]) hvec
  simpa only [zVec, Vector.getElem_map] using this

/-- **Completeness eval bridge.** From the coefficient-witness reads
(`env.get (off+k) = eval (bigIntMulNoReduce a b)[k]`), the output vector evaluates
equal to the schoolbook convolution, coordinate-wise. Mirrors
`interpolatedMul_eval_bridge` but sourced from `usesLocalWitnesses` rather than the
point constraints (used on the completeness side). -/
lemma interpolatedMul_eval_bridge_uses (env : Environment (F p)) (off : ℕ) (a b : Var (BigInt m) (F p))
    (h : ∀ k : Fin (2 * m - 1), env.get (off + k.val)
        = Expression.eval env ((bigIntMulNoReduce a b)[k.val])) :
    ∀ k : Fin (2 * m - 1),
      Expression.eval env (interpolatedMul a b off).1[k.val]
        = Expression.eval env (bigIntMulNoReduce a b)[k.val] := by
  intro k
  rw [interpolatedMul_output off a b]
  rw [Vector.getElem_mapRange]
  show env.get (off + k.val) = _
  exact h k

/-- The `interpolatedMul` operations carry no requirements (only asserts). -/
lemma interpolatedMul_requirements (off : ℕ) (a b : Var (BigInt m) (F p)) (env : Environment (F p)) :
    Operations.forAllNoOffset
      { interact := fun i => i.Requirements env,
        subcircuit := fun {_n} s => s.channelsWithRequirements = [] ∨ s.Assumptions env }
      (interpolatedMul a b off).2 := by
  simp only [interpolatedMul, circuit_norm]

/-- From `UsesLocalWitnessesCompleteness`: the coefficient witnesses take their
intended values `env.get (off+k) = eval (bigIntMulNoReduce a b)[k]`. -/
lemma interpolatedMul_usesLocalWitnesses (off off' : ℕ) (a b : Var (BigInt m) (F p))
    (penv : ProverEnvironment (F p)) (heq : off' = off)
    (h : penv.UsesLocalWitnessesCompleteness off' (interpolatedMul a b off).2) :
    ∀ k : Fin (2 * m - 1), penv.toEnvironment.get (off + k.val)
        = Expression.eval penv.toEnvironment ((bigIntMulNoReduce a b)[k.val]) := by
  subst heq
  simp only [interpolatedMul, circuit_norm] at h
  intro k
  have := h k
  simpa only [Vector.getElem_ofFn] using this

/-- Completeness reading: if every coefficient witness holds
(`env.get (off+k) = eval (bigIntMulNoReduce a b)[k]`), the `interpolatedMul`
operations are satisfiable (each point constraint holds). -/
lemma interpolatedMul_completeness (off : ℕ) (a b : Var (BigInt m) (F p)) (penv : ProverEnvironment (F p))
    (h : ∀ k : Fin (2 * m - 1), penv.toEnvironment.get (off + k.val)
        = Expression.eval penv.toEnvironment ((bigIntMulNoReduce a b)[k.val])) :
    Operations.forAllNoOffset
      { assert := fun e => Expression.eval penv.toEnvironment e = 0,
        lookup := fun l => l.Completeness penv.toEnvironment,
        interact := fun i => i.Guarantees penv.toEnvironment, subcircuit := fun {_n} s => s.ProverAssumptions penv } (interpolatedMul a b off).2 := by
  simp only [interpolatedMul, circuit_norm]
  intro cIdx
  have hm : 0 < m := Nat.pos_of_neZero m
  set c : F p := (((cIdx.val + 1 : ℕ)) : F p) with hcdef
  rw [add_neg_eq_zero]
  -- evaluate all three point-evaluations
  rw [show Expression.eval penv.toEnvironment (polyEvalExpr a c)
        = ∑ i : Fin m, Expression.eval penv.toEnvironment a[i.val] * c ^ i.val from polyEvalExpr_eval _ _ _,
    show Expression.eval penv.toEnvironment (polyEvalExpr b c)
        = ∑ i : Fin m, Expression.eval penv.toEnvironment b[i.val] * c ^ i.val from polyEvalExpr_eval _ _ _,
    show Expression.eval penv.toEnvironment
          (polyEvalExpr (Vector.mapRange (2 * m - 1) fun i => var (F := F p) { index := off + i }) c)
        = ∑ k : Fin (2 * m - 1),
            Expression.eval penv.toEnvironment
              (Vector.mapRange (2 * m - 1) fun i => var (F := F p) { index := off + i })[k.val] * c ^ k.val
      from polyEvalExpr_eval _ _ _]
  -- Cauchy on LHS
  rw [cauchy_diag hm (fun i : Fin m => Expression.eval penv.toEnvironment a[i.val])
    (fun i : Fin m => Expression.eval penv.toEnvironment b[i.val]) c]
  -- both sides are Σ_k (something_k) c^k; show the coefficients agree
  apply Finset.sum_congr rfl; intro k _
  congr 1
  -- LHS conv coeff = eval (bigIntMulNoReduce a b)[k] = env.get (off+k) = z-cell eval
  rw [show (∑ i : Fin m, if hh : i.val ≤ k.val ∧ k.val - i.val < m then
        (fun i : Fin m => Expression.eval penv.toEnvironment a[i.val]) i
          * (fun i : Fin m => Expression.eval penv.toEnvironment b[i.val]) ⟨k.val - i.val, hh.2⟩ else 0)
      = Expression.eval penv.toEnvironment (bigIntMulNoReduce a b)[k.val] from by
    rw [eval_bigIntMulNoReduce_coeff penv.toEnvironment a b k]]
  rw [← h k]
  simp only [Vector.getElem_mapRange, Expression.eval]

/-! ### Witness-free point-row assertion over a caller-provided coefficient vector -/

/-- Point-constraint assertion over a *caller-provided* coefficient expression
vector `z`: for each `c ∈ {1,…,2m-1}` assert `A(c)·B(c) − Z(c) = 0`. With the
`2m−1` distinct points this pins `z` to the convolution coefficients of `a·b`
coordinatewise — including entries of `z` that are not witness cells (e.g. a
definitional top coefficient). Carries no witnesses of its own. -/
def interpolatedMulAssert (a b : Var (BigInt m) (F p))
    (z : Vector (Expression (F p)) (2 * m - 1)) : Circuit (F p) Unit := do
  let constraints : Vector (Expression (F p)) (2 * m - 1) :=
    Vector.mapFinRange (2 * m - 1) fun cIdx =>
      let c : F p := ((cIdx.val + 1 : ℕ) : F p)
      polyEvalExpr a c * polyEvalExpr b c - polyEvalExpr z c
  Circuit.forEach constraints assertZero

/-- `interpolatedMulAssert` allocates nothing. -/
lemma interpolatedMulAssert_localLength (off : ℕ) (a b : Var (BigInt m) (F p))
    (z : Vector (Expression (F p)) (2 * m - 1)) :
    Operations.localLength (interpolatedMulAssert a b z off).2 = 0 := by
  simp only [interpolatedMulAssert, circuit_norm, Nat.mul_zero, Nat.add_zero]

/-- Soundness reading of the `interpolatedMulAssert` operations: every point
constraint holds. -/
lemma interpolatedMulAssert_soundness (off : ℕ) (a b : Var (BigInt m) (F p))
    (z : Vector (Expression (F p)) (2 * m - 1)) (env : Environment (F p))
    (h : Operations.forAllNoOffset
        { assert := fun e => Expression.eval env e = 0, lookup := fun l => l.Soundness env,
          interact := fun i => i.Guarantees env, subcircuit := fun {_n} s => s.Assumptions env → s.Spec env }
        (interpolatedMulAssert a b z off).2) :
    ∀ cIdx : Fin (2 * m - 1),
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr z ((cIdx.val + 1 : ℕ) : F p)) := by
  simp only [interpolatedMulAssert, circuit_norm] at h ⊢
  intro cIdx
  have hc := h cIdx
  simp only [Expression.eval] at hc
  rw [add_neg_eq_zero] at hc
  exact hc

/-- **Generalized soundness bridge.** From the point constraints, an arbitrary
coefficient expression vector `z` evaluates equal to the schoolbook convolution
`bigIntMulNoReduce a b`, coordinate-wise. Generalizes `interpolatedMul_map_eval`
from the witnessed cell vector `zVec` to any `z`. -/
lemma interpolatedMulAssertZ_map_eval (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (z : Vector (Expression (F p)) (2 * m - 1))
    (hpm : 2 * m - 1 < p)
    (hpts : ∀ cIdx : Fin (2 * m - 1),
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr z ((cIdx.val + 1 : ℕ) : F p))) :
    ∀ k : Fin (2 * m - 1),
      Expression.eval env z[k.val]
        = Expression.eval env (bigIntMulNoReduce a b)[k.val] := by
  have hm : 0 < m := Nat.pos_of_neZero m
  set u : Fin (2 * m - 1) → F p := fun k => Expression.eval env z[k.val] with hu
  set v : Fin (2 * m - 1) → F p := fun k => Expression.eval env (bigIntMulNoReduce a b)[k.val] with hv
  have hagree : ∀ cIdx : Fin (2 * m - 1),
      (∑ k : Fin (2 * m - 1), u k * (((cIdx.val + 1 : ℕ)) : F p) ^ k.val)
        = ∑ k : Fin (2 * m - 1), v k * (((cIdx.val + 1 : ℕ)) : F p) ^ k.val := by
    intro cIdx
    set c : F p := (((cIdx.val + 1 : ℕ)) : F p) with hcdef
    have hz : Expression.eval env (polyEvalExpr z c)
        = ∑ k : Fin (2 * m - 1), u k * c ^ k.val := by
      rw [polyEvalExpr_eval]
    have hab : Expression.eval env (polyEvalExpr a c) * Expression.eval env (polyEvalExpr b c)
        = (∑ i : Fin m, Expression.eval env a[i.val] * c ^ i.val)
          * (∑ i : Fin m, Expression.eval env b[i.val] * c ^ i.val) := by
      rw [polyEvalExpr_eval, polyEvalExpr_eval]
    have hcauchy := cauchy_diag hm
      (fun i : Fin m => Expression.eval env a[i.val])
      (fun i : Fin m => Expression.eval env b[i.val]) c
    have hconv : ∀ k : Fin (2 * m - 1),
        (∑ i : Fin m, if hh : i.val ≤ k.val ∧ k.val - i.val < m then
          (fun i : Fin m => Expression.eval env a[i.val]) i
            * (fun i : Fin m => Expression.eval env b[i.val]) ⟨k.val - i.val, hh.2⟩ else 0)
        = v k := by
      intro k
      show _ = Expression.eval env (bigIntMulNoReduce a b)[k.val]
      rw [eval_bigIntMulNoReduce_coeff env a b k]
    have hsound := hpts cIdx
    rw [hz] at hsound
    rw [hab] at hsound
    rw [hcauchy] at hsound
    rw [← hsound]
    apply Finset.sum_congr rfl; intro k _
    rw [hconv k]
  have huniq := interp_uniqueness u v
    (fun cIdx : Fin (2 * m - 1) => (((cIdx.val + 1 : ℕ)) : F p))
    (interp_points_injective hpm) hagree
  exact huniq

/-- The `interpolatedMulAssert` operations carry no requirements (only asserts). -/
lemma interpolatedMulAssert_requirements (off : ℕ) (a b : Var (BigInt m) (F p))
    (z : Vector (Expression (F p)) (2 * m - 1)) (env : Environment (F p)) :
    Operations.forAllNoOffset
      { interact := fun i => i.Requirements env,
        subcircuit := fun {_n} s => s.channelsWithRequirements = [] ∨ s.Assumptions env }
      (interpolatedMulAssert a b z off).2 := by
  simp only [interpolatedMulAssert, circuit_norm]

/-- Completeness reading: if every coefficient of `z` evaluates to the
corresponding schoolbook convolution coefficient, the `interpolatedMulAssert`
operations are satisfiable (each point constraint holds). -/
lemma interpolatedMulAssert_completeness (off : ℕ) (a b : Var (BigInt m) (F p))
    (z : Vector (Expression (F p)) (2 * m - 1)) (penv : ProverEnvironment (F p))
    (h : ∀ k : Fin (2 * m - 1),
        Expression.eval penv.toEnvironment z[k.val]
          = Expression.eval penv.toEnvironment ((bigIntMulNoReduce a b)[k.val])) :
    Operations.forAllNoOffset
      { assert := fun e => Expression.eval penv.toEnvironment e = 0,
        lookup := fun l => l.Completeness penv.toEnvironment,
        interact := fun i => i.Guarantees penv.toEnvironment, subcircuit := fun {_n} s => s.ProverAssumptions penv } (interpolatedMulAssert a b z off).2 := by
  simp only [interpolatedMulAssert, circuit_norm]
  intro cIdx
  have hm : 0 < m := Nat.pos_of_neZero m
  set c : F p := (((cIdx.val + 1 : ℕ)) : F p) with hcdef
  rw [add_neg_eq_zero]
  rw [show Expression.eval penv.toEnvironment (polyEvalExpr a c)
        = ∑ i : Fin m, Expression.eval penv.toEnvironment a[i.val] * c ^ i.val from polyEvalExpr_eval _ _ _,
    show Expression.eval penv.toEnvironment (polyEvalExpr b c)
        = ∑ i : Fin m, Expression.eval penv.toEnvironment b[i.val] * c ^ i.val from polyEvalExpr_eval _ _ _,
    show Expression.eval penv.toEnvironment (polyEvalExpr z c)
        = ∑ k : Fin (2 * m - 1),
            Expression.eval penv.toEnvironment z[k.val] * c ^ k.val
      from polyEvalExpr_eval _ _ _]
  rw [cauchy_diag hm (fun i : Fin m => Expression.eval penv.toEnvironment a[i.val])
    (fun i : Fin m => Expression.eval penv.toEnvironment b[i.val]) c]
  apply Finset.sum_congr rfl; intro k _
  congr 1
  rw [show (∑ i : Fin m, if hh : i.val ≤ k.val ∧ k.val - i.val < m then
        (fun i : Fin m => Expression.eval penv.toEnvironment a[i.val]) i
          * (fun i : Fin m => Expression.eval penv.toEnvironment b[i.val]) ⟨k.val - i.val, hh.2⟩ else 0)
      = Expression.eval penv.toEnvironment (bigIntMulNoReduce a b)[k.val] from by
    rw [eval_bigIntMulNoReduce_coeff penv.toEnvironment a b k]]
  rw [← h k]

end MulMod

end

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
