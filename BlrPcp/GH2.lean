import BlrPcp.GowersHatami
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Gowers-Hatami via the regular representation model

This file is a second blueprint for the Gowers-Hatami theorem, following the
proof sketch in the slides "Approximate representations are close to true
representations".

The point of this version is that it avoids the Fourier/irreducible
decomposition construction.  Given an approximate representation
`rho : G -> U(H)`, it takes

* `H' = L(G, H)`, the Hilbert space of functions `G -> H` with uniform inner
  product;
* `V u`, the function `x |-> rho x u`;
* `rho0`, the right regular representation `(rho0 x F) y = F (y * x)`.

The two identities in the proof sketch are then:

* `V` is an isometry;
* `V^* rho0(x) V = E_y rho(y)^* rho(y*x)`.

Combining the second identity with the approximate representation hypothesis
and `sigma_proximity_iff` gives the desired average `sigma`-norm estimate.
-/

open scoped Matrix ComplexConjugate ComplexOrder
open BigOperators Finset

variable {d : Nat}
variable (G : Type*) [Group G] [Fintype G]

/-! ## The enlarged Hilbert space `L(G,H)` -/

/-- Matrix index for the space `L(G, C^d)`, identified with `G x Fin d`. -/
abbrev GH2Index (G : Type*) (d : Nat) := G × Fin d

/-- The normalization constant for the uniform inner product on `L(G,H)`. -/
noncomputable def gh2Scale (G : Type*) [Fintype G] : Complex :=
  ((Real.sqrt (Fintype.card G : Real))⁻¹ : Complex)

/-- The square of the normalization constant is `1 / |G|`. -/
theorem gh2Scale_mul_self (G : Type*) [Fintype G] [Nonempty G] :
    gh2Scale G * gh2Scale G = (Fintype.card G : Complex)⁻¹ := by
  have hsqrt_sq :
      (Real.sqrt (Fintype.card G : Real) : Complex) *
        (Real.sqrt (Fintype.card G : Real) : Complex) =
          (Fintype.card G : Complex) := by
    rw [← Complex.ofReal_mul, ← sq]
    simp [Real.sq_sqrt (Nat.cast_nonneg _)]
  have hprod :
      gh2Scale G * gh2Scale G * (Fintype.card G : Complex) = 1 := by
    simp [gh2Scale, ← hsqrt_sq, mul_assoc]
  have hcard : (Fintype.card G : Complex) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← mul_right_inj' hcard]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hprod

/-- The normalization constant is real, hence fixed by complex conjugation. -/
@[simp]
theorem starRingEnd_gh2Scale (G : Type*) [Fintype G] :
    (starRingEnd Complex) (gh2Scale G) = gh2Scale G := by
  simp [gh2Scale]

/-!
The next definition is the isometry `V : H -> L(G,H)` from the slide proof.
With the matrix conventions used in `GowersHatami.lean`, `V` is represented as
a `d` by `G x d` matrix.  Thus this matrix is the adjoint of the map
`u |-> (x |-> rho(x) u)`, which is why its entries are those of `rho(x)^*`.
-/
noncomputable def gh2Embedding
    (rho : G -> Matrix (Fin d) (Fin d) Complex) :
    Matrix (Fin d) (GH2Index G d) Complex :=
  fun i xj => gh2Scale G * (starRingEnd Complex) (rho xj.1 xj.2 i)

/-!
The right regular representation of `G` on `L(G,H)`.
On functions it is `(rho0 x F) y = F (y * x)`.
-/
def gh2RightShift (x : G) : Equiv.Perm (GH2Index G d) where
  toFun y := (y.1 * x, y.2)
  invFun y := (y.1 * x⁻¹, y.2)
  left_inv y := by simp [mul_assoc]
  right_inv y := by simp [mul_assoc]

def gh2RightRegularMatrix
    [DecidableEq G]
    (x : G) : Matrix (GH2Index G d) (GH2Index G d) Complex :=
  (gh2RightShift (G := G) (d := d) x).permMatrix Complex

/-- Right shifts compose contravariantly, as functions act on the right. -/
theorem gh2RightShift_mul
    (G : Type*) [Group G] {d : Nat} (x y : G) :
    gh2RightShift (G := G) (d := d) (x * y) =
      gh2RightShift (G := G) (d := d) y * gh2RightShift (G := G) (d := d) x := by
  ext a <;> simp [gh2RightShift, mul_assoc]

/-- The right-regular matrix is unitary. -/
theorem gh2RightRegularMatrix_unitary [DecidableEq G] (x : G) :
    gh2RightRegularMatrix G x ∈ Matrix.unitaryGroup (GH2Index G d) Complex := by
  rw [Matrix.mem_unitaryGroup_iff]
  change (gh2RightShift (G := G) (d := d) x).permMatrix Complex *
    ((gh2RightShift (G := G) (d := d) x).permMatrix Complex)ᴴ = 1
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

/-- The identity element acts as the identity matrix. -/
theorem gh2RightRegularMatrix_one
    (G : Type*) [Group G] [DecidableEq G] {d : Nat} :
    gh2RightRegularMatrix (G := G) (d := d) 1 = 1 := by
  ext y z
  simp [gh2RightRegularMatrix, gh2RightShift, Matrix.one_apply, Prod.ext_iff]

/-- Right-regular matrices multiply according to the group multiplication. -/
theorem gh2RightRegularMatrix_mul [DecidableEq G] (x y : G) :
    gh2RightRegularMatrix (G := G) (d := d) (x * y) =
      gh2RightRegularMatrix (G := G) (d := d) x *
        gh2RightRegularMatrix (G := G) (d := d) y := by
  ext a b
  change ((gh2RightShift (G := G) (d := d) (x * y)).permMatrix Complex) a b =
    ((gh2RightShift (G := G) (d := d) x).permMatrix Complex *
      (gh2RightShift (G := G) (d := d) y).permMatrix Complex) a b
  rw [gh2RightShift_mul G x y, Matrix.permMatrix_mul]

/-- The right-regular matrix, bundled as a unitary matrix. -/
def gh2RightRegularUnitary [DecidableEq G]
    (x : G) : Matrix.unitaryGroup (GH2Index G d) Complex :=
  ⟨gh2RightRegularMatrix G x, gh2RightRegularMatrix_unitary G x⟩

noncomputable def gh2RightRegular [DecidableEq G]
    (d : Nat) :
    MonoidHom G (Matrix.unitaryGroup (GH2Index G d) Complex) where
  toFun := gh2RightRegularUnitary G
  map_one' := by
    apply Subtype.ext
    exact gh2RightRegularMatrix_one (G := G) (d := d)
  map_mul' x y := by
    apply Subtype.ext
    exact gh2RightRegularMatrix_mul (G := G) (d := d) x y

@[simp]
theorem gh2RightRegular_apply [DecidableEq G] (x : G) :
    (gh2RightRegular G d x :
      Matrix (GH2Index G d) (GH2Index G d) Complex) =
        gh2RightRegularMatrix G x := rfl

/--
Multiplying on the left by the right-regular matrix shifts the row index:
`(R_x M)(y,i) = M(y*x,i)`.
-/
@[simp]
theorem gh2RightRegularMatrix_mul_apply [DecidableEq G]
    (x : G) (M : Matrix (GH2Index G d) (Fin d) Complex)
    (y : GH2Index G d) (j : Fin d) :
    (gh2RightRegularMatrix (G := G) (d := d) x * M) y j =
      M (y.1 * x, y.2) j := by
  change
    (((gh2RightShift (G := G) (d := d) x).toPEquiv.toMatrix :
        Matrix (GH2Index G d) (GH2Index G d) Complex) * M) y j =
      M ((gh2RightShift (G := G) (d := d) x) y) j
  rw [PEquiv.toMatrix_toPEquiv_mul]
  rfl

/-- Applying the right-regular matrix to `V^*` evaluates `rho` at the shifted group element. -/
@[simp]
theorem gh2RightRegularMatrix_mul_embedding_conjTranspose_apply [DecidableEq G]
    (rho : G -> Matrix (Fin d) (Fin d) Complex)
    (x : G) (y : GH2Index G d) (j : Fin d) :
    (gh2RightRegularMatrix (G := G) (d := d) x * (gh2Embedding G rho)ᴴ) y j =
      gh2Scale G * rho (y.1 * x) y.2 j := by
  simp [gh2Embedding, Matrix.conjTranspose_apply]

/-! ## The two identities from the slide proof -/

/-- Column orthogonality for a unitary matrix. -/
theorem gh2_unitary_col_sum
    (A : Matrix (Fin d) (Fin d) Complex)
    (hA : A ∈ Matrix.unitaryGroup (Fin d) Complex)
    (i j : Fin d) :
    (∑ k : Fin d, (starRingEnd Complex) (A k i) * A k j) =
      (1 : Matrix (Fin d) (Fin d) Complex) i j := by
  have hmat : Aᴴ * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hA
  have hij := congr_fun (congr_fun hmat i) j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using hij

omit [Group G] in
/--
Entrywise expansion of `V V^*`.  This is the only bookkeeping step in the
isometry proof; the following theorem then just applies column orthogonality.
-/
theorem gh2Embedding_mul_conjTranspose_apply
    (rho : G -> Matrix (Fin d) (Fin d) Complex)
    (i j : Fin d) :
    (gh2Embedding G rho * (gh2Embedding G rho)ᴴ) i j =
      ∑ x : G, gh2Scale G * gh2Scale G *
        (∑ k : Fin d, (starRingEnd Complex) (rho x k i) * rho x k j) := by
  simp [gh2Embedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- The map `V u = (x |-> rho x u)` is an isometry. -/
theorem gh2Embedding_isometry
    (rho : G -> Matrix (Fin d) (Fin d) Complex)
    (hrho : forall x, rho x ∈ Matrix.unitaryGroup (Fin d) Complex) :
    gh2Embedding G rho * (gh2Embedding G rho)ᴴ = 1 := by
  ext i j
  calc
    (gh2Embedding G rho * (gh2Embedding G rho)ᴴ) i j
        = ∑ x : G, gh2Scale G * gh2Scale G *
            (∑ k : Fin d, (starRingEnd Complex) (rho x k i) * rho x k j) := by
            exact gh2Embedding_mul_conjTranspose_apply G rho i j
    _ = ∑ _x : G, gh2Scale G * gh2Scale G *
          (1 : Matrix (Fin d) (Fin d) Complex) i j := by
            simp [gh2_unitary_col_sum _ (hrho _) i j]
    _ = (1 : Matrix (Fin d) (Fin d) Complex) i j := by
            simp [gh2Scale_mul_self G]

/--
Hermiticity of `sigma` makes the two cross terms in the expansion of
`‖A - B‖_sigma^2` have the same real part.
-/
theorem sigma_cross_re_comm
    (sigma A B : Matrix (Fin d) (Fin d) Complex)
    (hsigma : Matrix.PosSemidef sigma) :
    (Matrix.trace (Bᴴ * A * sigma)).re =
      (Matrix.trace (Aᴴ * B * sigma)).re := by
  have hsigmaH : sigmaᴴ = sigma := hsigma.1
  have htrace :
      Matrix.trace (Bᴴ * A * sigma) =
        star (Matrix.trace (Aᴴ * B * sigma)) := by
    calc
      Matrix.trace (Bᴴ * A * sigma)
          = Matrix.trace (sigma * (Bᴴ * A)) := by
              rw [Matrix.trace_mul_cycle]
              simp [Matrix.mul_assoc]
      _ = Matrix.trace ((Aᴴ * B * sigma)ᴴ) := by
              congr 1
              simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, hsigmaH]
      _ = star (Matrix.trace (Aᴴ * B * sigma)) := Matrix.trace_conjTranspose _
  calc
    (Matrix.trace (Bᴴ * A * sigma)).re
        = (star (Matrix.trace (Aᴴ * B * sigma))).re := by rw [htrace]
    _ = (Matrix.trace (Aᴴ * B * sigma)).re := by simp

/-- Algebraic expansion of the `sigma`-norm square of a difference. -/
theorem sigmaNormSq_sub_eq
    (sigma A B : Matrix (Fin d) (Fin d) Complex)
    (hsigma : Matrix.PosSemidef sigma) :
    sigmaNormSq sigma (A - B) =
      sigmaNormSq sigma A + sigmaNormSq sigma B -
        2 * (sigmaInner sigma A B).re := by
  have hcross := sigma_cross_re_comm sigma A B hsigma
  unfold sigmaNormSq sigmaInner
  simp only [Matrix.conjTranspose_sub]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.sub_mul]
  simp only [Matrix.trace_sub, Complex.sub_re]
  rw [hcross]
  ring

/--
If two matrices have `sigma`-norm at most one, then the usual unitary
distance/correlation identity becomes an inequality.

This is the form needed for compressions of unitaries: the compression need not
be unitary, but it is enough to know its `sigma`-norm is bounded by one.
-/
theorem sigmaNormSq_sub_le_of_sigmaNormSq_le
    (sigma A B : Matrix (Fin d) (Fin d) Complex)
    (hsigma : Matrix.PosSemidef sigma)
    (hA : sigmaNormSq sigma A <= 1)
    (hB : sigmaNormSq sigma B <= 1) :
    sigmaNormSq sigma (A - B) <= 2 - 2 * (sigmaInner sigma A B).re := by
  have hnorm := sigmaNormSq_sub_eq sigma A B hsigma
  rw [hnorm]
  linarith

/-- A unitary matrix has `sigma`-norm one against a trace-one state. -/
theorem sigmaNormSq_unitary
    (sigma A : Matrix (Fin d) (Fin d) Complex)
    (hsigmatr : Matrix.trace sigma = 1)
    (hA : A ∈ Matrix.unitaryGroup (Fin d) Complex) :
    sigmaNormSq sigma A = 1 := by
  have hA' : Aᴴ * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hA
  unfold sigmaNormSq sigmaInner
  simp [hA', hsigmatr]

/-- If `A` and `B` are unitary, then `A^* B` is unitary. -/
theorem unitary_conjTranspose_mul
    {A B : Matrix (Fin d) (Fin d) Complex}
    (hA : A ∈ Matrix.unitaryGroup (Fin d) Complex)
    (hB : B ∈ Matrix.unitaryGroup (Fin d) Complex) :
    Aᴴ * B ∈ Matrix.unitaryGroup (Fin d) Complex := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hAA : Aᴴ * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hA
  have hBB : B * Bᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hB
  have hprod : (Aᴴ * B) * (Bᴴ * A) = 1 := by
    calc
      (Aᴴ * B) * (Bᴴ * A) = Aᴴ * (B * Bᴴ) * A := by
        simp [Matrix.mul_assoc]
      _ = Aᴴ * 1 * A := by rw [hBB]
      _ = 1 := by simpa [Matrix.mul_assoc] using hAA
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose] using hprod

@[simp]
theorem matrix_reindex_one
    {n n' : Type*} [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']
    (e : n ≃ n') :
    Matrix.reindex e e (1 : Matrix n n Complex) = 1 :=
  Matrix.reindexLinearEquiv_one Complex Complex e

/-- Reindexing a unitary matrix along an equivalence gives a unitary matrix. -/
noncomputable def reindexUnitary
    {n n' : Type*} [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']
    (e : n ≃ n') (U : Matrix.unitaryGroup n Complex) :
    Matrix.unitaryGroup n' Complex where
  val := Matrix.reindex e e (U : Matrix n n Complex)
  property := by
    rw [Matrix.mem_unitaryGroup_iff]
    change Matrix.reindex e e (U : Matrix n n Complex) *
      (Matrix.reindex e e (U : Matrix n n Complex))ᴴ = 1
    have hU : (U : Matrix n n Complex) * (U : Matrix n n Complex)ᴴ = 1 :=
      Matrix.mem_unitaryGroup_iff.mp U.property
    calc
      Matrix.reindex e e (U : Matrix n n Complex) *
          (Matrix.reindex e e (U : Matrix n n Complex))ᴴ
          = Matrix.reindex e e ((U : Matrix n n Complex) * (U : Matrix n n Complex)ᴴ) := by
              rw [Matrix.conjTranspose_reindex]
              exact Matrix.reindexLinearEquiv_mul Complex Complex e e e
                (U : Matrix n n Complex) ((U : Matrix n n Complex)ᴴ)
      _ = 1 := by
              simp [hU]

@[simp]
theorem reindexUnitary_coe
    {n n' : Type*} [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']
    (e : n ≃ n') (U : Matrix.unitaryGroup n Complex) :
    (reindexUnitary e U : Matrix n' n' Complex) =
      Matrix.reindex e e (U : Matrix n n Complex) := rfl

/-- Reindex a unitary representation along an equivalence of index types. -/
noncomputable def reindexUnitaryRep
    {n n' : Type*} [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']
    (e : n ≃ n') (rho0 : MonoidHom G (Matrix.unitaryGroup n Complex)) :
    MonoidHom G (Matrix.unitaryGroup n' Complex) where
  toFun x := reindexUnitary e (rho0 x)
  map_one' := by
    apply Subtype.ext
    simp [reindexUnitary]
  map_mul' x y := by
    apply Subtype.ext
    simp [reindexUnitary]

omit [Fintype G] in
@[simp]
theorem reindexUnitaryRep_apply
    {n n' : Type*} [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']
    (e : n ≃ n') (rho0 : MonoidHom G (Matrix.unitaryGroup n Complex)) (x : G) :
    (reindexUnitaryRep G e rho0 x : Matrix n' n' Complex) =
      Matrix.reindex e e (rho0 x : Matrix n n Complex) := rfl

/-- Reindexing the enlarged space preserves the compressed operator `V R V^*`. -/
@[simp]
theorem reindex_compression
    {n n' : Type*} [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']
    (e : n ≃ n')
    (V : Matrix (Fin d) n Complex)
    (R : Matrix n n Complex) :
    Matrix.reindex (Equiv.refl (Fin d)) e V *
      Matrix.reindex e e R *
      (Matrix.reindex (Equiv.refl (Fin d)) e V)ᴴ =
        V * R * Vᴴ := by
  have hVR :
      Matrix.reindex (Equiv.refl (Fin d)) e V * Matrix.reindex e e R =
        Matrix.reindex (Equiv.refl (Fin d)) e (V * R) := by
    exact Matrix.reindexLinearEquiv_mul Complex Complex (Equiv.refl (Fin d)) e e V R
  have hVRV :
      Matrix.reindex (Equiv.refl (Fin d)) e (V * R) *
          Matrix.reindex e (Equiv.refl (Fin d)) Vᴴ =
        Matrix.reindex (Equiv.refl (Fin d)) (Equiv.refl (Fin d)) ((V * R) * Vᴴ) := by
    exact Matrix.reindexLinearEquiv_mul Complex Complex (Equiv.refl (Fin d)) e
      (Equiv.refl (Fin d)) (V * R) Vᴴ
  calc
    Matrix.reindex (Equiv.refl (Fin d)) e V *
      Matrix.reindex e e R *
      (Matrix.reindex (Equiv.refl (Fin d)) e V)ᴴ
        = Matrix.reindex (Equiv.refl (Fin d)) e (V * R) *
            Matrix.reindex e (Equiv.refl (Fin d)) Vᴴ := by
              rw [Matrix.conjTranspose_reindex, hVR]
    _ = Matrix.reindex (Equiv.refl (Fin d)) (Equiv.refl (Fin d)) ((V * R) * Vᴴ) := hVRV
    _ = V * R * Vᴴ := by simp [Matrix.mul_assoc]

/-- Reindexing the enlarged space preserves the isometry equation. -/
theorem reindex_isometry
    {n n' : Type*} [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n']
    (e : n ≃ n')
    (V : Matrix (Fin d) n Complex)
    (hV : V * Vᴴ = 1) :
    Matrix.reindex (Equiv.refl (Fin d)) e V *
      (Matrix.reindex (Equiv.refl (Fin d)) e V)ᴴ = 1 := by
  calc
    Matrix.reindex (Equiv.refl (Fin d)) e V *
        (Matrix.reindex (Equiv.refl (Fin d)) e V)ᴴ
        = Matrix.reindex (Equiv.refl (Fin d)) (Equiv.refl (Fin d)) (V * Vᴴ) := by
            rw [Matrix.conjTranspose_reindex]
            exact Matrix.reindexLinearEquiv_mul Complex Complex
              (Equiv.refl (Fin d)) e (Equiv.refl (Fin d)) V Vᴴ
    _ = 1 := by simp [hV]

/-- Transport one Gowers-Hatami witness along an equivalence of the enlarged index type. -/
theorem gh_witness_reindex
    {n : Type*} [Fintype n] [DecidableEq n] {d' : Nat}
    (e : n ≃ Fin d') (hd_le : d <= d')
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (rho : G -> Matrix (Fin d) (Fin d) Complex)
    (eps : Real)
    (V : Matrix (Fin d) n Complex)
    (hV : V * Vᴴ = 1)
    (rho0 : MonoidHom G (Matrix.unitaryGroup n Complex))
    (hprox :
      (∑ x : G,
        sigmaNormSq sigma
          (rho x - V * (rho0 x : Matrix n n Complex) * Vᴴ)) /
        Fintype.card G <= 2 * eps) :
    ∃ (d' : Nat) (_ : d <= d')
      (V' : Matrix (Fin d) (Fin d') Complex)
      (_hV' : V' * V'ᴴ = 1)
      (rho0' : MonoidHom G (Matrix.unitaryGroup (Fin d') Complex)),
      (∑ x : G,
        sigmaNormSq sigma
          (rho x - V' * (rho0' x : Matrix (Fin d') (Fin d') Complex) * V'ᴴ)) /
        Fintype.card G <= 2 * eps := by
  let V' := Matrix.reindex (Equiv.refl (Fin d)) e V
  let rho0' := reindexUnitaryRep G e rho0
  refine ⟨d', hd_le, V', reindex_isometry e V hV, rho0', ?_⟩
  have hsum :
      (∑ x : G,
        sigmaNormSq sigma
          (rho x - V' * (rho0' x : Matrix (Fin d') (Fin d') Complex) * V'ᴴ)) =
        ∑ x : G,
          sigmaNormSq sigma
            (rho x - V * (rho0 x : Matrix n n Complex) * Vᴴ) := by
    apply Finset.sum_congr rfl
    intro x _
    simp [V', rho0']
  rw [hsum]
  exact hprox

/-- `sigmaNormSq` is the square of the norm induced by the positive semidefinite matrix `sigma`. -/
theorem sigmaNormSq_eq_matrix_norm_sq
    (sigma A : Matrix (Fin d) (Fin d) Complex)
    (hsigma : Matrix.PosSemidef sigma) :
    sigmaNormSq sigma A =
      letI : SeminormedAddCommGroup (Matrix (Fin d) (Fin d) Complex) :=
        Matrix.toMatrixSeminormedAddCommGroup sigma hsigma
      ‖A‖ ^ 2 := by
  letI : SeminormedAddCommGroup (Matrix (Fin d) (Fin d) Complex) :=
    Matrix.toMatrixSeminormedAddCommGroup sigma hsigma
  letI : InnerProductSpace Complex (Matrix (Fin d) (Fin d) Complex) :=
    Matrix.toMatrixInnerProductSpace sigma hsigma
  calc
    sigmaNormSq sigma A = (Matrix.trace (A * sigma * Aᴴ)).re := by
      unfold sigmaNormSq sigmaInner
      calc
        (Matrix.trace (Aᴴ * A * sigma)).re
            = (Matrix.trace ((A * sigma) * Aᴴ)).re := by
                simpa [Matrix.mul_assoc] using
                  congrArg Complex.re (Matrix.trace_mul_comm Aᴴ (A * sigma))
        _ = (Matrix.trace (A * sigma * Aᴴ)).re := by simp [Matrix.mul_assoc]
    _ = ‖A‖ ^ 2 := by
      rw [@norm_sq_eq_re_inner Complex (Matrix (Fin d) (Fin d) Complex) _ _ _ A]
      rfl

/-- The average of vectors of norm at most one still has norm at most one. -/
theorem norm_average_le_one
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace Complex E]
    (F : G -> E) (hF : forall x, ‖F x‖ <= 1) :
    ‖(Fintype.card G : Complex)⁻¹ • ∑ x : G, F x‖ <= 1 := by
  have hcard_pos : 0 < (Fintype.card G : Real) := by
    exact_mod_cast Fintype.card_pos
  have hcard_ne : (Fintype.card G : Real) ≠ 0 := ne_of_gt hcard_pos
  have hnorm_inv :
      ‖(Fintype.card G : Complex)⁻¹‖ = (Fintype.card G : Real)⁻¹ := by
    simp [norm_inv]
  have hsum_norm : ‖∑ x : G, F x‖ <= (Fintype.card G : Real) := by
    calc
      ‖∑ x : G, F x‖ <= ∑ x : G, ‖F x‖ := norm_sum_le _ _
      _ <= ∑ _x : G, (1 : Real) := by
        exact Finset.sum_le_sum fun x _ => hF x
      _ = (Fintype.card G : Real) := by simp
  calc
    ‖(Fintype.card G : Complex)⁻¹ • ∑ x : G, F x‖
        <= (Fintype.card G : Real)⁻¹ * ‖∑ x : G, F x‖ := by
          simpa [hnorm_inv] using
            NormedSpace.norm_smul_le
              (Fintype.card G : Complex)⁻¹ (∑ x : G, F x)
    _ <= (Fintype.card G : Real)⁻¹ * (Fintype.card G : Real) := by
          exact mul_le_mul_of_nonneg_left hsum_norm
            (inv_nonneg.mpr (le_of_lt hcard_pos))
    _ = 1 := by field_simp [hcard_ne]

/--
The `sigma`-unit ball is convex.  We use the seminorm induced by the positive
semidefinite matrix `sigma`, so this is just the triangle inequality for an
average.
-/
theorem sigmaNormSq_average_le_one
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (hsigma : Matrix.PosSemidef sigma)
    (F : G -> Matrix (Fin d) (Fin d) Complex)
    (hF : forall x, sigmaNormSq sigma (F x) <= 1) :
    sigmaNormSq sigma ((Fintype.card G : Complex)⁻¹ • ∑ x : G, F x) <= 1 := by
  letI : SeminormedAddCommGroup (Matrix (Fin d) (Fin d) Complex) :=
    Matrix.toMatrixSeminormedAddCommGroup sigma hsigma
  letI : InnerProductSpace Complex (Matrix (Fin d) (Fin d) Complex) :=
    Matrix.toMatrixInnerProductSpace sigma hsigma
  have hnormF : forall x : G, ‖F x‖ <= 1 := by
    intro x
    have hsq : ‖F x‖ ^ 2 <= 1 := by
      simpa [sigmaNormSq_eq_matrix_norm_sq sigma (F x) hsigma] using hF x
    nlinarith [norm_nonneg (F x)]
  have havg_norm := norm_average_le_one G F hnormF
  have hsq_avg : ‖((Fintype.card G : Complex)⁻¹ • ∑ x : G, F x)‖ ^ 2 <= 1 := by
    nlinarith [norm_nonneg ((Fintype.card G : Complex)⁻¹ • ∑ x : G, F x)]
  simpa [sigmaNormSq_eq_matrix_norm_sq sigma
    ((Fintype.card G : Complex)⁻¹ • ∑ x : G, F x) hsigma] using hsq_avg

/-- Averaging the affine expression `2 - 2 c_x`. -/
theorem average_two_sub_two_mul
    (c : G -> Real) :
    (∑ x : G, (2 - 2 * c x)) / Fintype.card G =
      2 - 2 * ((∑ x : G, c x) / Fintype.card G) := by
  have hcard_pos : 0 < (Fintype.card G : Real) := by
    exact_mod_cast Fintype.card_pos
  have hcard_ne : (Fintype.card G : Real) ≠ 0 := ne_of_gt hcard_pos
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp [hcard_ne]
  simp [Finset.card_univ]
  rw [← Finset.mul_sum]
  ring

/--
Entrywise expansion of the compression `V R_x V^*`.  The following theorem
then packages this expansion as the average from the slide proof.
-/
theorem gh2_compression_apply
    [DecidableEq G]
    (rho : G -> Matrix (Fin d) (Fin d) Complex)
    (x : G) (i j : Fin d) :
    (gh2Embedding G rho * gh2RightRegularMatrix (G := G) (d := d) x *
        (gh2Embedding G rho)ᴴ) i j =
      ∑ y : G, ∑ k : Fin d, (gh2Scale G * gh2Scale G) *
        ((starRingEnd Complex) (rho y k i) * rho (y * x) k j) := by
  rw [Matrix.mul_assoc]
  change (∑ a : GH2Index G d,
    gh2Embedding G rho i a *
      (gh2RightRegularMatrix (G := G) (d := d) x *
        (gh2Embedding G rho)ᴴ) a j) =
      ∑ y : G, ∑ k : Fin d, (gh2Scale G * gh2Scale G) *
        ((starRingEnd Complex) (rho y k i) * rho (y * x) k j)
  simp [gh2Embedding,
    Fintype.sum_prod_type, mul_assoc, mul_left_comm, mul_comm]

/--
The compression of the right regular representation by `V` is the average
`E_y rho(y)^* rho(y*x)`.
-/
theorem gh2_compression_eq_average
    [DecidableEq G]
    (rho : G -> Matrix (Fin d) (Fin d) Complex)
    (x : G) :
    gh2Embedding G rho *
      gh2RightRegularMatrix (G := G) (d := d) x *
      (gh2Embedding G rho)ᴴ =
        (Fintype.card G : Complex)⁻¹ •
          ∑ y : G, (rho y)ᴴ * rho (y * x) := by
  ext i j
  calc
    (gh2Embedding G rho * gh2RightRegularMatrix (G := G) (d := d) x *
        (gh2Embedding G rho)ᴴ) i j
        = ∑ y : G, ∑ k : Fin d, (gh2Scale G * gh2Scale G) *
            ((starRingEnd Complex) (rho y k i) * rho (y * x) k j) := by
            exact gh2_compression_apply G rho x i j
    _ = (Fintype.card G : Complex)⁻¹ *
          (∑ y : G, ∑ k : Fin d,
            (starRingEnd Complex) (rho y k i) * rho (y * x) k j) := by
            simp [gh2Scale_mul_self G, Finset.mul_sum]
    _ = ((Fintype.card G : Complex)⁻¹ •
          ∑ y : G, (rho y)ᴴ * rho (y * x)) i j := by
            simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
              Matrix.sum_apply, Finset.mul_sum]

/--
Compression of a unitary has `sigma`-norm at most one.

After rewriting the compression as an average, each summand is a product of
unitaries, hence has `sigma`-norm one; the preceding convexity lemma then gives
the bound.
-/
theorem gh2_compression_sigmaNormSq_le_one
    [DecidableEq G]
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (rho : G -> Matrix (Fin d) (Fin d) Complex)
    (x : G)
    (hsigma : Matrix.PosSemidef sigma)
    (hsigmatr : Matrix.trace sigma = 1)
    (hrho : forall y, rho y ∈ Matrix.unitaryGroup (Fin d) Complex) :
    sigmaNormSq sigma
      (gh2Embedding G rho *
        gh2RightRegularMatrix (G := G) (d := d) x *
      (gh2Embedding G rho)ᴴ) <= 1 := by
  rw [gh2_compression_eq_average G rho x]
  apply sigmaNormSq_average_le_one G sigma hsigma
  intro y
  have hy_unitary :
      (rho y)ᴴ * rho (y * x) ∈ Matrix.unitaryGroup (Fin d) Complex :=
    unitary_conjTranspose_mul (hrho y) (hrho (y * x))
  rw [sigmaNormSq_unitary sigma ((rho y)ᴴ * rho (y * x)) hsigmatr hy_unitary]

/--
Taking the `sigma`-inner product against the compressed right-regular action
recovers the approximate-representation correlation, averaged over the
auxiliary group element.
-/
theorem sigmaInner_gh2_compression
    [DecidableEq G]
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (rho : G -> Matrix (Fin d) (Fin d) Complex)
    (x : G) :
    sigmaInner sigma (rho x)
        (gh2Embedding G rho *
          gh2RightRegularMatrix (G := G) (d := d) x *
          (gh2Embedding G rho)ᴴ) =
      (Fintype.card G : Complex)⁻¹ *
        ∑ y : G, sigmaInner sigma (rho y * rho x) (rho (y * x)) := by
  rw [gh2_compression_eq_average G rho x]
  unfold sigmaInner
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]
  congr 1
  rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro y _
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/--
The approximate-representation hypothesis gives high average correlation
between `rho(x)` and the compressed exact representation.
-/
theorem gh2_average_correlation
    [DecidableEq G]
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (rho : G -> Matrix (Fin d) (Fin d) Complex)
    (eps : Real)
    (hApprox : IsApproxRepresentation G sigma rho eps) :
    (∑ x : G,
      (sigmaInner sigma (rho x)
        (gh2Embedding G rho *
          gh2RightRegularMatrix (G := G) (d := d) x *
          (gh2Embedding G rho)ᴴ)).re) /
      Fintype.card G >= 1 - eps := by
  have hcard : (Fintype.card G : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hmain :
      (∑ x : G,
        (sigmaInner sigma (rho x)
          (gh2Embedding G rho *
            gh2RightRegularMatrix (G := G) (d := d) x *
            (gh2Embedding G rho)ᴴ)).re) / Fintype.card G =
        (∑ x : G, ∑ y : G,
          (sigmaInner sigma (rho x * rho y) (rho (x * y))).re) /
          (Fintype.card G ^ 2 : Real) := by
    calc
      (∑ x : G,
        (sigmaInner sigma (rho x)
          (gh2Embedding G rho *
            gh2RightRegularMatrix (G := G) (d := d) x *
            (gh2Embedding G rho)ᴴ)).re) / Fintype.card G
          = (∑ x : G,
              ((Fintype.card G : Complex)⁻¹ *
                ∑ y : G, sigmaInner sigma (rho y * rho x) (rho (y * x))).re) /
              Fintype.card G := by
              simp [sigmaInner_gh2_compression G sigma rho]
      _ = (∑ x : G, ∑ y : G,
              (sigmaInner sigma (rho y * rho x) (rho (y * x))).re) /
              (Fintype.card G ^ 2 : Real) := by
              simp [Complex.inv_re, hcard, Finset.mul_sum, div_eq_mul_inv,
                pow_two, mul_left_comm, mul_comm]
      _ = (∑ x : G, ∑ y : G,
              (sigmaInner sigma (rho x * rho y) (rho (x * y))).re) /
              (Fintype.card G ^ 2 : Real) := by
              rw [Finset.sum_comm]
  simpa [hmain, IsApproxRepresentation] using hApprox

/-! ## Gowers-Hatami, regular-representation proof -/

/--
Gowers-Hatami theorem in the concrete enlarged space `L(G,C^d)`.

This is the theorem proved directly by the slide sketch: the exact
representation is the right regular representation on `L(G,H)`, and the
isometry is `u |-> (x |-> rho(x)u)`.
-/
theorem gowers_hatami_GH2_product
    [DecidableEq G]
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (hsigma : Matrix.PosSemidef sigma) (hsigmatr : Matrix.trace sigma = 1)
    (rho : G -> Matrix (Fin d) (Fin d) Complex)
    (eps : Real) (_heps : 0 <= eps)
    (hrho : forall x, rho x ∈ Matrix.unitaryGroup (Fin d) Complex)
    (hApprox : IsApproxRepresentation G sigma rho eps) :
    ∃ (V : Matrix (Fin d) (GH2Index G d) Complex)
      (_hV : V * Vᴴ = 1)
      (rho0 : MonoidHom G (Matrix.unitaryGroup (GH2Index G d) Complex)),
      (∑ x : G,
        sigmaNormSq sigma
          (rho x -
            V * (rho0 x : Matrix (GH2Index G d) (GH2Index G d) Complex) * Vᴴ)) /
        Fintype.card G <= 2 * eps := by
  refine ⟨gh2Embedding G rho, gh2Embedding_isometry G rho hrho,
    gh2RightRegular G d, ?_⟩
  simp only [gh2RightRegular_apply]
  have hcorr := gh2_average_correlation G sigma rho eps hApprox
  let comp : G -> Matrix (Fin d) (Fin d) Complex := fun x =>
    gh2Embedding G rho *
      gh2RightRegularMatrix (G := G) (d := d) x *
      (gh2Embedding G rho)ᴴ
  have hpoint :
      forall x : G,
        sigmaNormSq sigma (rho x - comp x) <=
          2 - 2 * (sigmaInner sigma (rho x) (comp x)).re := by
    intro x
    exact sigmaNormSq_sub_le_of_sigmaNormSq_le sigma (rho x) (comp x) hsigma
      (by
        rw [sigmaNormSq_unitary sigma (rho x) hsigmatr (hrho x)])
      (by
        exact gh2_compression_sigmaNormSq_le_one G sigma rho x hsigma hsigmatr hrho)
  have hsum :
      (∑ x : G, sigmaNormSq sigma (rho x - comp x)) <=
        ∑ x : G, (2 - 2 * (sigmaInner sigma (rho x) (comp x)).re) := by
    exact Finset.sum_le_sum fun x _ => hpoint x
  have hcard_pos : 0 < (Fintype.card G : Real) := by
    exact_mod_cast Fintype.card_pos
  have hcard_ne : (Fintype.card G : Real) ≠ 0 := ne_of_gt hcard_pos
  have hcorr' :
      ((∑ x : G, (sigmaInner sigma (rho x) (comp x)).re) / Fintype.card G) >=
        1 - eps := by
    simpa [comp] using hcorr
  calc
    (∑ x : G, sigmaNormSq sigma (rho x - comp x)) / Fintype.card G
        <= (∑ x : G, (2 - 2 * (sigmaInner sigma (rho x) (comp x)).re)) /
            Fintype.card G := by
          exact div_le_div_of_nonneg_right hsum (le_of_lt hcard_pos)
    _ = 2 - 2 *
          ((∑ x : G, (sigmaInner sigma (rho x) (comp x)).re) / Fintype.card G) := by
          exact average_two_sub_two_mul G
            (fun x : G => (sigmaInner sigma (rho x) (comp x)).re)
    _ <= 2 * eps := by
          linarith

/--
The same statement in the dimensional format used by `gowers_hatami` in
`GowersHatami.lean`.

The intended witness is `d' = |G| * d`, obtained by reindexing
`GH2Index G d = G x Fin d` with `Fin (|G| * d)`.
-/
theorem gowers_hatami_GH2
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (hsigma : Matrix.PosSemidef sigma) (hsigmatr : Matrix.trace sigma = 1)
    (rho : G -> Matrix (Fin d) (Fin d) Complex)
    (eps : Real) (heps : 0 <= eps)
    (hrho : forall x, rho x ∈ Matrix.unitaryGroup (Fin d) Complex)
    (hApprox : IsApproxRepresentation G sigma rho eps) :
    ∃ (d' : Nat) (_ : d <= d')
      (V : Matrix (Fin d) (Fin d') Complex)
      (_hV : V * Vᴴ = 1)
      (rho0 : MonoidHom G (Matrix.unitaryGroup (Fin d') Complex)),
      (∑ x : G,
        sigmaNormSq sigma
          (rho x - V * (rho0 x : Matrix (Fin d') (Fin d') Complex) * Vᴴ)) /
        Fintype.card G <= 2 * eps := by
  classical
  obtain ⟨V, hV, rho0, hprox⟩ :=
    gowers_hatami_GH2_product G sigma hsigma hsigmatr rho eps heps hrho hApprox
  let d' := Fintype.card G * d
  let e : GH2Index G d ≃ Fin d' :=
    (Equiv.prodCongr (Fintype.equivFin G) (Equiv.refl (Fin d))).trans
      finProdFinEquiv
  have hd_le : d <= d' := by
    exact Nat.le_mul_of_pos_left d Fintype.card_pos
  exact gh_witness_reindex G e hd_le sigma rho eps V hV rho0 hprox
