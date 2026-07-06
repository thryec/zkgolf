import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Cost

/-!
# Mixed-length xJsnark O(n₁+n₂) interpolation multiplication check (`interpolatedMulX`)

Mixed-length generalization of `interpolatedMul` (`InterpMul.lean`): instead of two
equal-length `BigInt m` operands, `interpolatedMulX` takes plain coefficient
vectors `a : Vector _ n₁`, `b : Vector _ n₂` of possibly different lengths, so
callers can feed it the affine outputs of other gadgets directly. Witness the
`n₁+n₂-1` convolution coefficients directly, and pin them by evaluating the
product polynomial at the `n₁+n₂-1` fixed points `1, 2, …, n₁+n₂-1`.

Cost is `⟨n₁+n₂-1, n₁+n₂-1⟩`. The returned coefficient vector is *affine* (just
the witnessed cells), and each constraint
`(Σ_i a_i c^i)(Σ_i b_i c^i) − (Σ_k z_k c^k)` is a single R1CS row
(affine·affine − affine), exactly as in `interpolatedMul`.

Soundness (`interpolatedMulX_map_eval`) uses `Vandermonde.lean`'s
`interp_uniqueness` lemma unchanged — it is already generic in the number of
interpolation points. Only the Cauchy-product step (`cauchy_diag` in
`Vandermonde.lean`, specialized to equal-length `a b : Fin m → K`) needed a
mixed-length generalization; that generalization (`cauchy_diag_mixed`) is added
here rather than in `Vandermonde.lean`.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537

/-- **Cauchy product, diagonal form (mixed length).** Mixed-length generalization
of `cauchy_diag` (`Vandermonde.lean`, specialized to `a b : Fin m → K` of equal
length `m`): for `a : Fin n₁ → K`, `b : Fin n₂ → K`, and `x : K`, the product of
the two truncated polynomials `Σ_i a_i x^i` and `Σ_j b_j x^j` equals
`Σ_k conv_k x^k` over `k : Fin (n₁+n₂-1)`, where
`conv_k = Σ_i [i≤k ∧ k-i<n₂] a_i b_{k-i}` is the schoolbook convolution
coefficient. -/
lemma cauchy_diag_mixed {K : Type*} [CommRing K] {n₁ n₂ : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (a : Fin n₁ → K) (b : Fin n₂ → K) (x : K) :
    (∑ i : Fin n₁, a i * x ^ i.val) * (∑ j : Fin n₂, b j * x ^ j.val)
      = ∑ k : Fin (n₁ + n₂ - 1),
          (∑ i : Fin n₁, if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
            a i * b ⟨k.val - i.val, h.2⟩ else 0) * x ^ k.val := by
  rw [Fintype.sum_mul_sum]
  -- LHS = Σ_i Σ_j a_i b_j x^(i+j)
  have hL : (∑ i : Fin n₁, ∑ j : Fin n₂, a i * x ^ i.val * (b j * x ^ j.val))
      = ∑ i : Fin n₁, ∑ j : Fin n₂, (a i * b j) * x ^ (i.val + j.val) := by
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    rw [pow_add]; ring
  rw [hL]
  -- RHS: distribute the x^k into the inner sum
  have hR : (∑ k : Fin (n₁ + n₂ - 1),
        (∑ i : Fin n₁, if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
          a i * b ⟨k.val - i.val, h.2⟩ else 0) * x ^ k.val)
      = ∑ k : Fin (n₁ + n₂ - 1), ∑ i : Fin n₁,
          if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
            (a i * b ⟨k.val - i.val, h.2⟩) * x ^ k.val else 0 := by
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < n₂
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h, zero_mul]
  rw [hR]
  conv_rhs => rw [Finset.sum_comm]
  -- goal: Σ_i Σ_j a_i b_j x^(i+j) = Σ_i Σ_k (guarded)
  -- for each i, reindex Σ_k (guarded) = Σ_j a_i b_j x^(i+j)
  apply Finset.sum_congr rfl; intro i _
  -- RHS: rewrite the dite-guarded sum over univ as a sum over the filtered set
  classical
  have hfilter : (∑ k : Fin (n₁ + n₂ - 1),
        if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
          a i * b ⟨k.val - i.val, h.2⟩ * x ^ k.val else 0)
      = ∑ k ∈ (Finset.univ.filter (fun k : Fin (n₁ + n₂ - 1) => i.val ≤ k.val ∧ k.val - i.val < n₂)),
          if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
            a i * b ⟨k.val - i.val, h.2⟩ * x ^ k.val else 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl; intro k _
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < n₂
    · rw [dif_pos h, if_pos h]
    · rw [dif_neg h, if_neg h]
  rw [hfilter]
  -- now bijection: j : Fin n₂ ↔ k = i+j in the filter.  s = univ (Fin n₂), t = filter.
  refine Finset.sum_nbij'
    (i := fun (j : Fin n₂) => (⟨i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩ : Fin (n₁ + n₂ - 1)))
    (j := fun (k : Fin (n₁ + n₂ - 1)) => (⟨min (k.val - i.val) (n₂ - 1), by omega⟩ : Fin n₂))
    ?hi ?hj ?left_inv ?right_inv ?h
  case hi =>
    intro j _; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    show i.val ≤ i.val + j.val ∧ (i.val + j.val) - i.val < n₂
    have := j.isLt; omega
  case hj =>
    intro k hk; exact Finset.mem_univ _
  case left_inv =>
    intro j _
    show (⟨min ((i.val + j.val) - i.val) (n₂ - 1), _⟩ : Fin n₂) = j
    apply Fin.ext; show min ((i.val + j.val) - i.val) (n₂ - 1) = j.val
    have := j.isLt; omega
  case right_inv =>
    intro k hk; obtain ⟨_, hle, hlt⟩ := Finset.mem_filter.mp hk
    show (⟨i.val + min (k.val - i.val) (n₂ - 1), _⟩ : Fin (n₁ + n₂ - 1)) = k
    apply Fin.ext; show i.val + min (k.val - i.val) (n₂ - 1) = k.val
    omega
  case h =>
    intro j _
    show a i * b j * x ^ (i.val + j.val)
      = (if h : i.val ≤ (i.val + j.val) ∧ (i.val + j.val) - i.val < n₂ then
          a i * b ⟨(i.val + j.val) - i.val, h.2⟩ * x ^ (i.val + j.val) else 0)
    have hguard : i.val ≤ i.val + j.val ∧ (i.val + j.val) - i.val < n₂ := by
      have := j.isLt; omega
    rw [dif_pos hguard]
    have hbj : (⟨(i.val + j.val) - i.val, hguard.2⟩ : Fin n₂) = j := by
      apply Fin.ext; show (i.val + j.val) - i.val = j.val; omega
    rw [hbj]

section
variable {p : ℕ} [Fact p.Prime]
variable {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]

namespace MulMod

/-- Mixed-length schoolbook convolution `mulNoReduceX a b`, direct analogue of
`bigIntMulNoReduce` (`Theorems.lean`) for two coefficient vectors of possibly
different lengths: returns the `n₁+n₂-1` coefficients
`P_k = Σ_{i+j=k} a[i] · b[j]` as `Expression`s. It carries no witnesses and no
constraints, so it is a plain total function over `Expression (F p)`. -/
def mulNoReduceX (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂) :
    Vector (Expression (F p)) (n₁ + n₂ - 1) :=
  Vector.mapFinRange (n₁ + n₂ - 1) fun k =>
    (Vector.finRange n₁).foldl
      (fun acc i =>
        if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
          acc + a[i.val] * b[k.val - i.val]'(h.2)
        else acc)
      (0 : Expression (F p))

omit [NeZero n₁] [NeZero n₂] in
/-- The evaluated `k`-th convolution coefficient of `mulNoReduceX a b`, expressed
as a guarded `Finset.sum` over `Fin n₁` in the field `F p`. Mirrors
`eval_bigIntMulNoReduce_coeff`. -/
lemma eval_mulNoReduceX_coeff (env : Environment (F p))
    (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂) (k : Fin (n₁ + n₂ - 1)) :
    Expression.eval env ((mulNoReduceX a b)[k.val])
      = ∑ i : Fin n₁, if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
          (Expression.eval env a[i.val]) * (Expression.eval env (b[k.val - i.val]'h.2)) else 0 := by
  simp only [mulNoReduceX, Vector.getElem_mapFinRange]
  rw [vector_foldl_finRange]
  rw [eval_foldl env n₁
    (fun acc i => if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
        acc + a[i.val] * b[k.val - i.val]'h.2 else acc) 0
    (by intro e i; by_cases h : i.val ≤ k.val ∧ k.val - i.val < n₂ <;> simp [h, circuit_norm])]
  simp only [apply_dite (Expression.eval env), Expression.eval]
  rw [foldl_dif_add_eq_sum n₁ (fun i : Fin n₁ => i.val ≤ k.val ∧ k.val - i.val < n₂)
    (fun i h => (Expression.eval env a[i.val]) * (Expression.eval env (b[k.val - i.val]'h.2)))]

/-- The mixed-length interpolation multiplication gadget. Generalizes
`interpolatedMul` to two coefficient vectors `a : Vector _ n₁`, `b : Vector _ n₂`
of possibly different lengths. Witness the `n₁+n₂-1` convolution coefficients
`z`, then for each point `c ∈ {1,…,n₁+n₂-1}` assert
`(Σ_i a_i c^i)(Σ_i b_i c^i) − (Σ_k z_k c^k) = 0`. Returns the affine vector `z`. -/
def interpolatedMulX (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂) :
    Circuit (F p) (Vector (Expression (F p)) (n₁ + n₂ - 1)) := do
  -- witness the n₁+n₂-1 convolution coefficients directly
  let z ← ProvableType.witness (α := fields (n₁ + n₂ - 1)) fun env =>
    Vector.ofFn fun k : Fin (n₁ + n₂ - 1) =>
      Expression.eval env.toEnvironment ((mulNoReduceX a b)[k.val])
  -- for each c = cIdx+1 ∈ {1..n₁+n₂-1}, assert (polyEval a c)(polyEval b c) = polyEval z c
  let constraints : Vector (Expression (F p)) (n₁ + n₂ - 1) :=
    Vector.mapFinRange (n₁ + n₂ - 1) fun cIdx =>
      let c : F p := ((cIdx.val + 1 : ℕ) : F p)
      polyEvalExpr a c * polyEvalExpr b c - polyEvalExpr z c
  Circuit.forEach constraints assertZero
  return z

/-- The output of `interpolatedMulX a b off` is the affine vector of freshly
witnessed coefficient cells at offset `off`. -/
lemma interpolatedMulX_output (off : ℕ) (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂) :
    (interpolatedMulX a b off).1
      = (Vector.mapRange (n₁ + n₂ - 1) fun i => var (F := F p) { index := off + i }) := by
  simp only [interpolatedMulX, circuit_norm]

/-- `interpolatedMulX a b` allocates exactly `n₁+n₂-1` cells (the coefficient
vector). -/
lemma interpolatedMulX_localLength (off : ℕ) (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂) :
    Operations.localLength (interpolatedMulX a b off).2 = n₁ + n₂ - 1 := by
  simp only [interpolatedMulX, circuit_norm, Nat.mul_zero, Nat.add_zero]

/-- The witnessed coefficient vector `z` at offset `off`. -/
def zVecX (n₁ n₂ off : ℕ) : Vector (Expression (F p)) (n₁ + n₂ - 1) :=
  Vector.mapRange (n₁ + n₂ - 1) fun i => var (F := F p) { index := off + i }

/-- The points `1, 2, …, n₁+n₂-1` embedded in `F p` are distinct, provided
`n₁+n₂-1 < p` (so no wraparound). Mirrors `interp_points_injective`. -/
lemma interp_points_injective_mixed (hpm : n₁ + n₂ - 1 < p) :
    Function.Injective (fun cIdx : Fin (n₁ + n₂ - 1) => (((cIdx.val + 1 : ℕ)) : F p)) := by
  intro i j hij
  simp only at hij
  have hi : i.val + 1 < p := by have := i.isLt; omega
  have hj : j.val + 1 < p := by have := j.isLt; omega
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hij
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  exact Fin.ext (by omega)

/-- **Soundness bridge (mixed length).** From the point constraints, the
witnessed coefficient vector `z = zVecX n₁ n₂ off` evaluates equal to the mixed
schoolbook convolution `mulNoReduceX a b`, coordinate-wise. Mirrors
`interpolatedMul_map_eval`. -/
lemma interpolatedMulX_map_eval (env : Environment (F p)) (off : ℕ)
    (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂) (hpm : n₁ + n₂ - 1 < p)
    (hpts : ∀ cIdx : Fin (n₁ + n₂ - 1),
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr (zVecX n₁ n₂ off) ((cIdx.val + 1 : ℕ) : F p))) :
    Vector.map (Expression.eval env) (zVecX n₁ n₂ off)
      = Vector.map (Expression.eval env) (mulNoReduceX a b) := by
  have hn1 : 0 < n₁ := Nat.pos_of_neZero n₁
  have hn2 : 0 < n₂ := Nat.pos_of_neZero n₂
  -- coefficient functions
  set u : Fin (n₁ + n₂ - 1) → F p := fun k => Expression.eval env (zVecX n₁ n₂ off)[k.val] with hu
  set v : Fin (n₁ + n₂ - 1) → F p := fun k => Expression.eval env (mulNoReduceX a b)[k.val] with hv
  -- interpolation-uniqueness hypothesis: agreement at the n₁+n₂-1 points
  have hagree : ∀ cIdx : Fin (n₁ + n₂ - 1),
      (∑ k : Fin (n₁ + n₂ - 1), u k * (((cIdx.val + 1 : ℕ)) : F p) ^ k.val)
        = ∑ k : Fin (n₁ + n₂ - 1), v k * (((cIdx.val + 1 : ℕ)) : F p) ^ k.val := by
    intro cIdx
    set c : F p := (((cIdx.val + 1 : ℕ)) : F p) with hcdef
    -- RHS of soundness = Σ_k u_k c^k
    have hz : Expression.eval env (polyEvalExpr (zVecX n₁ n₂ off) c)
        = ∑ k : Fin (n₁ + n₂ - 1), u k * c ^ k.val := by
      rw [polyEvalExpr_eval]
    -- LHS of soundness = (Σ_i a_i c^i)(Σ_i b_i c^i)
    have hab : Expression.eval env (polyEvalExpr a c) * Expression.eval env (polyEvalExpr b c)
        = (∑ i : Fin n₁, Expression.eval env a[i.val] * c ^ i.val)
          * (∑ i : Fin n₂, Expression.eval env b[i.val] * c ^ i.val) := by
      rw [polyEvalExpr_eval, polyEvalExpr_eval]
    -- Cauchy (mixed length): (Σa)(Σb) = Σ_k conv_k c^k, and conv_k = v_k
    have hcauchy := cauchy_diag_mixed hn1 hn2
      (fun i : Fin n₁ => Expression.eval env a[i.val])
      (fun i : Fin n₂ => Expression.eval env b[i.val]) c
    have hconv : ∀ k : Fin (n₁ + n₂ - 1),
        (∑ i : Fin n₁, if hh : i.val ≤ k.val ∧ k.val - i.val < n₂ then
          (fun i : Fin n₁ => Expression.eval env a[i.val]) i
            * (fun i : Fin n₂ => Expression.eval env b[i.val]) ⟨k.val - i.val, hh.2⟩ else 0)
        = v k := by
      intro k
      show _ = Expression.eval env (mulNoReduceX a b)[k.val]
      rw [eval_mulNoReduceX_coeff env a b k]
    -- assemble
    have hsound := hpts cIdx
    rw [hz] at hsound
    rw [hab] at hsound
    rw [hcauchy] at hsound
    -- hsound : Σ_k conv_k c^k = Σ_k u_k c^k
    rw [← hsound]
    apply Finset.sum_congr rfl; intro k _
    rw [hconv k]
  -- apply interpolation-uniqueness (already generic in the number of points)
  have huniq := interp_uniqueness u v
    (fun cIdx : Fin (n₁ + n₂ - 1) => (((cIdx.val + 1 : ℕ)) : F p))
    (interp_points_injective_mixed hpm) hagree
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, Vector.getElem_map]
  exact huniq ⟨k, hk⟩


/-- Point-constraint assertion over a *caller-provided* coefficient expression
vector `z`: for each `c ∈ {1,…,n₁+n₂-1}` assert `A(c)·B(c) − Z(c) = 0`. With
the `n₁+n₂−1` distinct points this pins `z` to the convolution coefficients of
`a·b` coordinatewise — including entries of `z` that are not witness cells
(e.g. a definitional top coefficient). Carries no witnesses of its own. -/
def interpolatedMulXAssert (a : Vector (Expression (F p)) n₁)
    (b : Vector (Expression (F p)) n₂)
    (z : Vector (Expression (F p)) (n₁ + n₂ - 1)) : Circuit (F p) Unit := do
  let constraints : Vector (Expression (F p)) (n₁ + n₂ - 1) :=
    Vector.mapFinRange (n₁ + n₂ - 1) fun cIdx =>
      let c : F p := ((cIdx.val + 1 : ℕ) : F p)
      polyEvalExpr a c * polyEvalExpr b c - polyEvalExpr z c
  Circuit.forEach constraints assertZero

/-- `interpolatedMulXAssert` allocates nothing. -/
lemma interpolatedMulXAssert_localLength (off : ℕ) (a : Vector (Expression (F p)) n₁)
    (b : Vector (Expression (F p)) n₂) (z : Vector (Expression (F p)) (n₁ + n₂ - 1)) :
    Operations.localLength (interpolatedMulXAssert a b z off).2 = 0 := by
  simp only [interpolatedMulXAssert, circuit_norm, Nat.mul_zero, Nat.add_zero]

/-- **Generalized soundness bridge.** From the point constraints, an arbitrary
coefficient expression vector `z` evaluates equal to the mixed schoolbook
convolution `mulNoReduceX a b`, coordinate-wise. Generalizes
`interpolatedMulX_map_eval` from the witnessed cell vector `zVecX` to any `z`. -/
lemma interpolatedMulXZ_map_eval (env : Environment (F p))
    (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂)
    (z : Vector (Expression (F p)) (n₁ + n₂ - 1)) (hpm : n₁ + n₂ - 1 < p)
    (hpts : ∀ cIdx : Fin (n₁ + n₂ - 1),
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr z ((cIdx.val + 1 : ℕ) : F p))) :
    Vector.map (Expression.eval env) z
      = Vector.map (Expression.eval env) (mulNoReduceX a b) := by
  have hn1 : 0 < n₁ := Nat.pos_of_neZero n₁
  have hn2 : 0 < n₂ := Nat.pos_of_neZero n₂
  set u : Fin (n₁ + n₂ - 1) → F p := fun k => Expression.eval env z[k.val] with hu
  set v : Fin (n₁ + n₂ - 1) → F p := fun k => Expression.eval env (mulNoReduceX a b)[k.val] with hv
  have hagree : ∀ cIdx : Fin (n₁ + n₂ - 1),
      (∑ k : Fin (n₁ + n₂ - 1), u k * (((cIdx.val + 1 : ℕ)) : F p) ^ k.val)
        = ∑ k : Fin (n₁ + n₂ - 1), v k * (((cIdx.val + 1 : ℕ)) : F p) ^ k.val := by
    intro cIdx
    set c : F p := (((cIdx.val + 1 : ℕ)) : F p) with hcdef
    have hz : Expression.eval env (polyEvalExpr z c)
        = ∑ k : Fin (n₁ + n₂ - 1), u k * c ^ k.val := by
      rw [polyEvalExpr_eval]
    have hab : Expression.eval env (polyEvalExpr a c) * Expression.eval env (polyEvalExpr b c)
        = (∑ i : Fin n₁, Expression.eval env a[i.val] * c ^ i.val)
          * (∑ i : Fin n₂, Expression.eval env b[i.val] * c ^ i.val) := by
      rw [polyEvalExpr_eval, polyEvalExpr_eval]
    have hcauchy := cauchy_diag_mixed hn1 hn2
      (fun i : Fin n₁ => Expression.eval env a[i.val])
      (fun i : Fin n₂ => Expression.eval env b[i.val]) c
    have hconv : ∀ k : Fin (n₁ + n₂ - 1),
        (∑ i : Fin n₁, if hh : i.val ≤ k.val ∧ k.val - i.val < n₂ then
          (fun i : Fin n₁ => Expression.eval env a[i.val]) i
            * (fun i : Fin n₂ => Expression.eval env b[i.val]) ⟨k.val - i.val, hh.2⟩ else 0)
        = v k := by
      intro k
      show _ = Expression.eval env (mulNoReduceX a b)[k.val]
      rw [eval_mulNoReduceX_coeff env a b k]
    have hsound := hpts cIdx
    rw [hz] at hsound
    rw [hab] at hsound
    rw [hcauchy] at hsound
    rw [← hsound]
    apply Finset.sum_congr rfl; intro k _
    rw [hconv k]
  have huniq := interp_uniqueness u v
    (fun cIdx : Fin (n₁ + n₂ - 1) => (((cIdx.val + 1 : ℕ)) : F p))
    (interp_points_injective_mixed hpm) hagree
  apply Vector.ext
  intro k hk
  rw [Vector.getElem_map, Vector.getElem_map]
  exact huniq ⟨k, hk⟩

/-- Soundness reading of the `interpolatedMulXAssert` operations: every point
constraint holds. -/
lemma interpolatedMulXAssert_soundness (off : ℕ) (a : Vector (Expression (F p)) n₁)
    (b : Vector (Expression (F p)) n₂) (z : Vector (Expression (F p)) (n₁ + n₂ - 1))
    (env : Environment (F p))
    (h : Operations.forAllNoOffset
        { assert := fun e => Expression.eval env e = 0, lookup := fun l => l.Soundness env,
          interact := fun i => i.Guarantees env, subcircuit := fun {_n} s => s.Assumptions env → s.Spec env }
        (interpolatedMulXAssert a b z off).2) :
    ∀ cIdx : Fin (n₁ + n₂ - 1),
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr z ((cIdx.val + 1 : ℕ) : F p)) := by
  simp only [interpolatedMulXAssert, circuit_norm] at h ⊢
  intro cIdx
  have hc := h cIdx
  simp only [Expression.eval] at hc
  rw [add_neg_eq_zero] at hc
  exact hc

/-- Per-element form of `interpolatedMulXZ_map_eval`. -/
lemma interpolatedMulXAssertZ_eval_bridge (env : Environment (F p))
    (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂)
    (z : Vector (Expression (F p)) (n₁ + n₂ - 1)) (hpm : n₁ + n₂ - 1 < p)
    (hpts : ∀ cIdx : Fin (n₁ + n₂ - 1),
      Expression.eval env (polyEvalExpr a ((cIdx.val + 1 : ℕ) : F p))
          * Expression.eval env (polyEvalExpr b ((cIdx.val + 1 : ℕ) : F p))
        = Expression.eval env (polyEvalExpr z ((cIdx.val + 1 : ℕ) : F p))) :
    ∀ k : Fin (n₁ + n₂ - 1),
      Expression.eval env z[k.val]
        = Expression.eval env (mulNoReduceX a b)[k.val] := by
  intro k
  have hvec := interpolatedMulXZ_map_eval env a b z hpm hpts
  have := congrArg (fun w => w[k.val]) hvec
  simpa only [Vector.getElem_map] using this

/-- The `interpolatedMulXAssert` operations carry no requirements (only asserts). -/
lemma interpolatedMulXAssert_requirements (off : ℕ) (a : Vector (Expression (F p)) n₁)
    (b : Vector (Expression (F p)) n₂) (z : Vector (Expression (F p)) (n₁ + n₂ - 1))
    (env : Environment (F p)) :
    Operations.forAllNoOffset
      { interact := fun i => i.Requirements env,
        subcircuit := fun {_n} s => s.channelsWithRequirements = [] ∨ s.Assumptions env }
      (interpolatedMulXAssert a b z off).2 := by
  simp only [interpolatedMulXAssert, circuit_norm]

/-- Completeness reading: if every coefficient of `z` evaluates to the
corresponding mixed schoolbook convolution coefficient, the
`interpolatedMulXAssert` operations are satisfiable. -/
lemma interpolatedMulXAssert_completeness (off : ℕ) (a : Vector (Expression (F p)) n₁)
    (b : Vector (Expression (F p)) n₂) (z : Vector (Expression (F p)) (n₁ + n₂ - 1))
    (penv : ProverEnvironment (F p))
    (h : ∀ k : Fin (n₁ + n₂ - 1),
        Expression.eval penv.toEnvironment z[k.val]
          = Expression.eval penv.toEnvironment ((mulNoReduceX a b)[k.val])) :
    Operations.forAllNoOffset
      { assert := fun e => Expression.eval penv.toEnvironment e = 0,
        lookup := fun l => l.Completeness penv.toEnvironment,
        interact := fun i => i.Guarantees penv.toEnvironment,
        subcircuit := fun {_n} s => s.ProverAssumptions penv } (interpolatedMulXAssert a b z off).2 := by
  simp only [interpolatedMulXAssert, circuit_norm]
  intro cIdx
  have hn1 : 0 < n₁ := Nat.pos_of_neZero n₁
  have hn2 : 0 < n₂ := Nat.pos_of_neZero n₂
  set c : F p := (((cIdx.val + 1 : ℕ)) : F p) with hcdef
  rw [add_neg_eq_zero]
  rw [show Expression.eval penv.toEnvironment (polyEvalExpr a c)
        = ∑ i : Fin n₁, Expression.eval penv.toEnvironment a[i.val] * c ^ i.val from polyEvalExpr_eval _ _ _,
    show Expression.eval penv.toEnvironment (polyEvalExpr b c)
        = ∑ i : Fin n₂, Expression.eval penv.toEnvironment b[i.val] * c ^ i.val from polyEvalExpr_eval _ _ _,
    show Expression.eval penv.toEnvironment (polyEvalExpr z c)
        = ∑ k : Fin (n₁ + n₂ - 1),
            Expression.eval penv.toEnvironment z[k.val] * c ^ k.val
      from polyEvalExpr_eval _ _ _]
  rw [cauchy_diag_mixed hn1 hn2 (fun i : Fin n₁ => Expression.eval penv.toEnvironment a[i.val])
    (fun i : Fin n₂ => Expression.eval penv.toEnvironment b[i.val]) c]
  apply Finset.sum_congr rfl; intro k _
  congr 1
  rw [show (∑ i : Fin n₁, if hh : i.val ≤ k.val ∧ k.val - i.val < n₂ then
        (fun i : Fin n₁ => Expression.eval penv.toEnvironment a[i.val]) i
          * (fun i : Fin n₂ => Expression.eval penv.toEnvironment b[i.val]) ⟨k.val - i.val, hh.2⟩ else 0)
      = Expression.eval penv.toEnvironment (mulNoReduceX a b)[k.val] from by
    rw [eval_mulNoReduceX_coeff penv.toEnvironment a b k]]
  rw [← h k]

end MulMod

end

namespace GadgetCost

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Challenge.CostR1CS
open Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostInfra

variable {n₁ n₂ : ℕ}

/-- The output of `interpolatedMulX a b` is the affine vector of freshly
witnessed coefficient cells, hence affine at every offset. Mirrors
`affineW_interpolatedMul_output`. -/
theorem affineW_interpolatedMulX_output [NeZero n₁] [NeZero n₂]
    (a : Vector (Expression (F circomPrime)) n₁) (b : Vector (Expression (F circomPrime)) n₂) (off : ℕ) :
    AffineW ((MulMod.interpolatedMulX a b).output off) := by
  rw [show (MulMod.interpolatedMulX a b).output off
        = (Vector.mapRange (n₁ + n₂ - 1) fun i => var (F := F circomPrime) { index := off + i })
      from MulMod.interpolatedMulX_output off a b]
  intro k hk
  rw [Vector.getElem_mapRange]; exact Affine.var _

/-- `interpolatedMulX a b` witnesses the `n₁+n₂-1` coefficient cells
(`⟨n₁+n₂-1, 0⟩`) and asserts each of the `n₁+n₂-1` point constraints
(`n₁+n₂-1` rows): `⟨n₁+n₂-1, n₁+n₂-1⟩`. Mirrors `costIs_interpolatedMul`. -/
theorem costIs_interpolatedMulX [NeZero n₁] [NeZero n₂]
    (a : Vector (Expression (F circomPrime)) n₁) (b : Vector (Expression (F circomPrime)) n₂) :
    CostIs (MulMod.interpolatedMulX a b) ⟨n₁ + n₂ - 1, n₁ + n₂ - 1⟩ := by
  rw [show (⟨n₁ + n₂ - 1, n₁ + n₂ - 1⟩ : Count)
        = ⟨n₁ + n₂ - 1, 0⟩ + (⟨(n₁ + n₂ - 1) * 0, (n₁ + n₂ - 1) * 1⟩ + Count.zero) from by
      simp only [Count.zero]; congr 1
      simp only [Count.add_constraints]; ring]
  unfold MulMod.interpolatedMulX
  refine CostIs.bind (CostIs.provableWitness _) fun z => ?_
  refine CostIs.bind (CostIs.forEach fun a k => CostIs.assertZero _ k) fun _ => ?_
  exact CostIs.pure _

/-- Each point constraint `polyEval a c · polyEval b c − polyEval z c` of
`interpolatedMulX` is a single R1CS row (affine·affine − affine), given affine
inputs `a, b`. Mirrors `isR1CS_interpolatedMul`. -/
theorem isR1CS_interpolatedMulX [NeZero n₁] [NeZero n₂]
    (a : Vector (Expression (F circomPrime)) n₁) (b : Vector (Expression (F circomPrime)) n₂)
    (ha : AffineW a) (hb : AffineW b) :
    IsR1CSCirc (MulMod.interpolatedMulX a b) := by
  unfold MulMod.interpolatedMulX
  refine IsR1CSCirc.bind_out (IsR1CSCirc.provableWitness _) fun nz => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun t k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul_sub (affine_polyEvalExpr _ _ (fun i hi => ha i hi))
      (affine_polyEvalExpr _ _ (fun i hi => hb i hi))
      (affine_polyEvalExpr _ _ (fun i hi =>
        affineW_provableWitness_bigInt (k := n₁ + n₂ - 1) _ nz i hi))
  exact IsR1CSCirc.pure _

/-- `interpolatedMulXAssert` witnesses nothing and asserts each of the
`n₁+n₂-1` point constraints: `⟨0, n₁+n₂-1⟩`. -/
theorem costIs_interpolatedMulXAssert [NeZero n₁] [NeZero n₂]
    (a : Vector (Expression (F circomPrime)) n₁) (b : Vector (Expression (F circomPrime)) n₂)
    (z : Vector (Expression (F circomPrime)) (n₁ + n₂ - 1)) :
    CostIs (MulMod.interpolatedMulXAssert a b z) ⟨0, n₁ + n₂ - 1⟩ := by
  rw [show (⟨0, n₁ + n₂ - 1⟩ : Count)
        = ⟨(n₁ + n₂ - 1) * 0, (n₁ + n₂ - 1) * 1⟩ from by
      congr 1
      ring]
  unfold MulMod.interpolatedMulXAssert
  exact CostIs.forEach fun a k => CostIs.assertZero _ k

/-- Each point constraint of `interpolatedMulXAssert` is a single R1CS row
(affine·affine − affine), given affine `a, b, z`. -/
theorem isR1CS_interpolatedMulXAssert [NeZero n₁] [NeZero n₂]
    (a : Vector (Expression (F circomPrime)) n₁) (b : Vector (Expression (F circomPrime)) n₂)
    (z : Vector (Expression (F circomPrime)) (n₁ + n₂ - 1))
    (ha : AffineW a) (hb : AffineW b) (hz : AffineW z) :
    IsR1CSCirc (MulMod.interpolatedMulXAssert a b z) := by
  unfold MulMod.interpolatedMulXAssert
  refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun t k => ?_
  refine IsR1CSCirc.assertZero ?_ k
  rw [Vector.getElem_mapFinRange]
  exact isR1CSRow_mul_sub (affine_polyEvalExpr _ _ (fun i hi => ha i hi))
    (affine_polyEvalExpr _ _ (fun i hi => hb i hi))
    (affine_polyEvalExpr _ _ (fun i hi => hz i hi))

variable {m : ℕ}

/-- `interpolatedMulAssert` (equal-length) witnesses nothing and asserts each of
the `2m-1` point constraints: `⟨0, 2m-1⟩`. -/
theorem costIs_interpolatedMulAssert [NeZero m]
    (a b : Var (BigInt m) (F circomPrime))
    (z : Vector (Expression (F circomPrime)) (2 * m - 1)) :
    CostIs (MulMod.interpolatedMulAssert a b z) ⟨0, 2 * m - 1⟩ := by
  rw [show (⟨0, 2 * m - 1⟩ : Count)
        = ⟨(2 * m - 1) * 0, (2 * m - 1) * 1⟩ from by
      congr 1
      ring]
  unfold MulMod.interpolatedMulAssert
  exact CostIs.forEach fun a k => CostIs.assertZero _ k

/-- Each point constraint of `interpolatedMulAssert` is a single R1CS row
(affine·affine − affine), given affine `a, b, z`. -/
theorem isR1CS_interpolatedMulAssert [NeZero m]
    (a b : Var (BigInt m) (F circomPrime))
    (z : Vector (Expression (F circomPrime)) (2 * m - 1))
    (ha : AffineW a) (hb : AffineW b) (hz : AffineW z) :
    IsR1CSCirc (MulMod.interpolatedMulAssert a b z) := by
  unfold MulMod.interpolatedMulAssert
  refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun t k => ?_
  refine IsR1CSCirc.assertZero ?_ k
  rw [Vector.getElem_mapFinRange]
  exact isR1CSRow_mul_sub (affine_polyEvalExpr _ _ (fun i hi => ha i hi))
    (affine_polyEvalExpr _ _ (fun i hi => hb i hi))
    (affine_polyEvalExpr _ _ (fun i hi => hz i hi))

end GadgetCost

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
