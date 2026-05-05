/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import BlrPcp.GH3.Background

/-!
# Gowers-Hatami with an abstract finite target index

This file proves the finite-coordinate Gowers-Hatami theorem in a form where the
large Hilbert space is indexed by an arbitrary finite type.

The background file `BlrPcp.GH3.Background` supplies rho-free tools: the right
regular representation, sigma-norm algebra, and averaging lemmas.  This file
contains the proof-specific layer: the normalized embedding associated to an
approximate representation `rho`, the isometry identity, the compression
calculation, and the abstract theorem `GH3.gowers_hatami_abstract`.

The concrete `Fin d'` formulation is derived separately in
`BlrPcp.GH3.Concrete` by one final reindexing step.
-/
open scoped Matrix ComplexConjugate ComplexOrder
open BigOperators Finset

universe u

variable {d : Nat}
variable (G : Type u) [Group G] [Fintype G]

namespace GH3

noncomputable section
/-- The coordinate Hilbert space with basis indexed by an arbitrary finite type. -/
abbrev CoordHilbert (ι : Type*) := EuclideanSpace Complex ι

/-- Compression of a representation on the enlarged coordinate space by an isometry adjoint `V`. -/
def compression {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix (Fin d) ι Complex)
    (rho0 : G →* Matrix.unitaryGroup ι Complex)
    (x : G) : Matrix (Fin d) (Fin d) Complex :=
  V * (rho0 x : Matrix ι ι Complex) * Vᴴ

/--
A finite-dimensional Hilbert-space witness for Gowers-Hatami, in coordinates.

The target Hilbert space is `CoordHilbert ι` for an arbitrary finite index type
`ι`; no choice of an equivalence `ι ≃ Fin d'` is part of this statement.
-/
def HasFiniteHilbertWitness
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (eps : Real) : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι)
    (V : Matrix (Fin d) ι Complex)
    (_hV : V * Vᴴ = 1)
    (rho0 : G →* Matrix.unitaryGroup ι Complex),
    (∑ x : G, sigmaNormSq sigma (rho x - compression G V rho0 x)) /
      Fintype.card G ≤ 2 * eps

/-! ## The normalized embedding and isometry -/

/-- The normalization constant for the uniform inner product on `L(G, ℂ^d)`. -/
def scale (G : Type*) [Fintype G] : Complex :=
  ((Real.sqrt (Fintype.card G : Real))⁻¹ : Complex)

@[simp]
theorem scale_mul_self (G : Type*) [Fintype G] [Nonempty G] :
    scale G * scale G = (Fintype.card G : Complex)⁻¹ := by
  have hsqrt_sq :
      (Real.sqrt (Fintype.card G : Real) : Complex) *
          (Real.sqrt (Fintype.card G : Real) : Complex) =
        (Fintype.card G : Complex) := by
    rw [← Complex.ofReal_mul, ← sq]
    simp [Real.sq_sqrt (Nat.cast_nonneg _)]
  have hprod : scale G * scale G * (Fintype.card G : Complex) = 1 := by
    simp [scale, ← hsqrt_sq, mul_assoc]
  have hcard : (Fintype.card G : Complex) ≠ 0 := card_ne_zero_complex G
  rw [← mul_right_inj' hcard]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hprod

@[simp]
theorem starRingEnd_scale (G : Type*) [Fintype G] :
    (starRingEnd Complex) (scale G) = scale G := by
  simp [scale]

/-- The adjoint of `u ↦ fun x ↦ rho x u`, with normalized counting measure on `G`. -/
def embedding (rho : G → Matrix (Fin d) (Fin d) Complex) :
    Matrix (Fin d) (Index G d) Complex :=
  fun i xj ↦ scale G * (starRingEnd Complex) (rho xj.1 xj.2 i)

private theorem unitary_conjTranspose_mul_self
    {A : Matrix (Fin d) (Fin d) Complex}
    (hA : A ∈ Matrix.unitaryGroup (Fin d) Complex) :
    Aᴴ * A = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp hA

private theorem unitary_col_sum
    (A : Matrix (Fin d) (Fin d) Complex)
    (hA : A ∈ Matrix.unitaryGroup (Fin d) Complex)
    (i j : Fin d) :
    (∑ k : Fin d, (starRingEnd Complex) (A k i) * A k j) =
      (1 : Matrix (Fin d) (Fin d) Complex) i j := by
  have hmat : Aᴴ * A = 1 := unitary_conjTranspose_mul_self hA
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using
    congr_fun (congr_fun hmat i) j

omit [Group G] in
private theorem embedding_mul_conjTranspose_apply
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (i j : Fin d) :
    (embedding G rho * (embedding G rho)ᴴ) i j =
      ∑ x : G, scale G * scale G *
        (∑ k : Fin d, (starRingEnd Complex) (rho x k i) * rho x k j) := by
  simp [embedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- The map `V u = fun x ↦ rho x u` is an isometry. -/
theorem embedding_isometry
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (hrho : ∀ x, rho x ∈ Matrix.unitaryGroup (Fin d) Complex) :
    embedding G rho * (embedding G rho)ᴴ = 1 := by
  ext i j
  calc
    (embedding G rho * (embedding G rho)ᴴ) i j
        = ∑ x : G, scale G * scale G *
            (∑ k : Fin d, (starRingEnd Complex) (rho x k i) * rho x k j) :=
          embedding_mul_conjTranspose_apply G rho i j
    _ = ∑ _x : G, scale G * scale G *
          (1 : Matrix (Fin d) (Fin d) Complex) i j := by
          simp [unitary_col_sum _ (hrho _) i j]
    _ = (1 : Matrix (Fin d) (Fin d) Complex) i j := by
          simp

/-! ## Compression by the right regular representation -/

/-- The concrete compression coming from the right-regular representation. -/
def regularCompression [DecidableEq G]
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (x : G) : Matrix (Fin d) (Fin d) Complex :=
  embedding G rho *
    rightRegularMatrix (G := G) (d := d) x *
    (embedding G rho)ᴴ

/-- Applying the right-regular matrix to `Vᴴ` evaluates `rho` at the shifted group element. -/
@[simp]
theorem rightRegularMatrix_mul_embedding_conjTranspose_apply [DecidableEq G]
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (x : G) (y : Index G d) (j : Fin d) :
    (rightRegularMatrix (G := G) (d := d) x * (embedding G rho)ᴴ) y j =
      scale G * rho (y.1 * x) y.2 j := by
  rw [rightRegularMatrix_mul_apply]
  simp [embedding, Matrix.conjTranspose_apply]

/-! ## The compression identity -/

/-- Entrywise form of `V R_x V^*` before collecting it as a matrix average. -/
private theorem compression_apply [DecidableEq G]
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (x : G) (i j : Fin d) :
    (embedding G rho * rightRegularMatrix (G := G) (d := d) x *
        (embedding G rho)ᴴ) i j =
      ∑ y : G, ∑ k : Fin d, (scale G * scale G) *
        ((starRingEnd Complex) (rho y k i) * rho (y * x) k j) := by
  rw [Matrix.mul_assoc]
  change (∑ a : Index G d,
    embedding G rho i a *
      (rightRegularMatrix (G := G) (d := d) x *
        (embedding G rho)ᴴ) a j) =
      ∑ y : G, ∑ k : Fin d, (scale G * scale G) *
        ((starRingEnd Complex) (rho y k i) * rho (y * x) k j)
  simp [-scale_mul_self, embedding,
    Fintype.sum_prod_type, mul_assoc, mul_left_comm, mul_comm]

/-- `V R_x V^*` is the average `E_y rho(y)^* rho(y*x)`. -/
theorem compression_eq_average [DecidableEq G]
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (x : G) :
    embedding G rho *
      rightRegularMatrix (G := G) (d := d) x *
      (embedding G rho)ᴴ =
        (Fintype.card G : Complex)⁻¹ •
          ∑ y : G, (rho y)ᴴ * rho (y * x) := by
  ext i j
  calc
    (embedding G rho * rightRegularMatrix (G := G) (d := d) x *
        (embedding G rho)ᴴ) i j
        = ∑ y : G, ∑ k : Fin d, (scale G * scale G) *
            ((starRingEnd Complex) (rho y k i) * rho (y * x) k j) :=
          compression_apply G rho x i j
    _ = (Fintype.card G : Complex)⁻¹ *
          (∑ y : G, ∑ k : Fin d,
            (starRingEnd Complex) (rho y k i) * rho (y * x) k j) := by
            simp [scale_mul_self G, Finset.mul_sum]
    _ = ((Fintype.card G : Complex)⁻¹ •
          ∑ y : G, (rho y)ᴴ * rho (y * x)) i j := by
            simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
              Matrix.sum_apply, Finset.mul_sum]

/-- Compression of a unitary has `sigma`-norm square at most one. -/
theorem compression_sigmaNormSq_le_one [DecidableEq G]
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (x : G)
    (hsigma : Matrix.PosSemidef sigma)
    (hsigmatr : Matrix.trace sigma = 1)
    (hrho : ∀ y, rho y ∈ Matrix.unitaryGroup (Fin d) Complex) :
    sigmaNormSq sigma (regularCompression G rho x) ≤ 1 := by
  unfold regularCompression
  rw [compression_eq_average G rho x]
  apply sigmaNormSq_average_le_one G sigma hsigma
  intro y
  have hy_unitary :
      (rho y)ᴴ * rho (y * x) ∈ Matrix.unitaryGroup (Fin d) Complex :=
    unitary_conjTranspose_mul (hrho y) (hrho (y * x))
  rw [sigmaNormSq_unitary sigma ((rho y)ᴴ * rho (y * x)) hsigmatr hy_unitary]

/-- The compressed correlation is the average approximate-representation correlation. -/
theorem sigmaInner_compression [DecidableEq G]
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (x : G) :
    sigmaInner sigma (rho x) (regularCompression G rho x) =
      (Fintype.card G : Complex)⁻¹ *
        ∑ y : G, sigmaInner sigma (rho y * rho x) (rho (y * x)) := by
  unfold regularCompression
  rw [compression_eq_average G rho x]
  unfold sigmaInner
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]
  congr 1
  rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro y _
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The approximate-representation hypothesis gives high average compressed correlation. -/
theorem average_correlation [DecidableEq G]
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (eps : Real)
    (hApprox : IsApproxRepresentation G sigma rho eps) :
    (∑ x : G, (sigmaInner sigma (rho x) (regularCompression G rho x)).re) /
      Fintype.card G ≥ 1 - eps := by
  have hcard : (Fintype.card G : Real) ≠ 0 := card_ne_zero_real G
  have hmain :
      (∑ x : G, (sigmaInner sigma (rho x) (regularCompression G rho x)).re) /
          Fintype.card G =
        (∑ x : G, ∑ y : G,
          (sigmaInner sigma (rho x * rho y) (rho (x * y))).re) /
          (Fintype.card G ^ 2 : Real) := by
    calc
      (∑ x : G, (sigmaInner sigma (rho x) (regularCompression G rho x)).re) /
          Fintype.card G
          = (∑ x : G,
              ((Fintype.card G : Complex)⁻¹ *
                ∑ y : G, sigmaInner sigma (rho y * rho x) (rho (y * x))).re) /
              Fintype.card G := by
              simp [sigmaInner_compression G sigma rho]
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

/-! ## The regular witness estimate -/

/-- Pointwise distance bound for the right-regular compression. -/
theorem sigmaNormSq_sub_regularCompression_le [DecidableEq G]
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (hsigma : Matrix.PosSemidef sigma) (hsigmatr : Matrix.trace sigma = 1)
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (hrho : ∀ x, rho x ∈ Matrix.unitaryGroup (Fin d) Complex)
    (x : G) :
    sigmaNormSq sigma (rho x - regularCompression G rho x) ≤
      2 - 2 * (sigmaInner sigma (rho x) (regularCompression G rho x)).re := by
  exact sigmaNormSq_sub_le_of_sigmaNormSq_le sigma (rho x) (regularCompression G rho x) hsigma
    (by rw [sigmaNormSq_unitary sigma (rho x) hsigmatr (hrho x)])
    (compression_sigmaNormSq_le_one G sigma rho x hsigma hsigmatr hrho)

/-- The right-regular compression is close to the approximate representation on average. -/
theorem regularCompression_proximity [DecidableEq G]
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (hsigma : Matrix.PosSemidef sigma) (hsigmatr : Matrix.trace sigma = 1)
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (eps : Real)
    (hrho : ∀ x, rho x ∈ Matrix.unitaryGroup (Fin d) Complex)
    (hApprox : IsApproxRepresentation G sigma rho eps) :
    (∑ x : G, sigmaNormSq sigma (rho x - regularCompression G rho x)) /
      Fintype.card G ≤ 2 * eps := by
  let c : G → Real :=
    fun x ↦ (sigmaInner sigma (rho x) (regularCompression G rho x)).re
  have hcorr : (∑ x : G, c x) / Fintype.card G ≥ 1 - eps := by
    simpa [c] using average_correlation G sigma rho eps hApprox
  have hsum :
      (∑ x : G, sigmaNormSq sigma (rho x - regularCompression G rho x)) ≤
        ∑ x : G, (2 - 2 * c x) :=
    Finset.sum_le_sum fun x _ ↦
      show sigmaNormSq sigma (rho x - regularCompression G rho x) ≤ 2 - 2 * c x from
        sigmaNormSq_sub_regularCompression_le G sigma hsigma hsigmatr rho hrho x
  have hcard_pos : 0 < (Fintype.card G : Real) := card_pos_real G
  calc
    (∑ x : G, sigmaNormSq sigma (rho x - regularCompression G rho x)) /
        Fintype.card G
        ≤ (∑ x : G, (2 - 2 * c x)) / Fintype.card G :=
          div_le_div_of_nonneg_right hsum (le_of_lt hcard_pos)
    _ = 2 - 2 * ((∑ x : G, c x) / Fintype.card G) :=
          average_two_sub_two_mul G c
    _ ≤ 2 * eps := by
          linarith [hcorr]

/-! ## Gowers-Hatami, abstract finite-coordinate form -/

/--
Gowers-Hatami theorem with no chosen numeric dimension for the enlarged space.

The target is an arbitrary finite coordinate Hilbert space, represented by its
index type `ι`.  The proof chooses the natural space `ι = G × Fin d`, so there
is no final reindexing step.
-/
theorem gowers_hatami_abstract [DecidableEq G]
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (hsigma : Matrix.PosSemidef sigma) (hsigmatr : Matrix.trace sigma = 1)
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (eps : Real) (_heps : 0 ≤ eps)
    (hrho : ∀ x, rho x ∈ Matrix.unitaryGroup (Fin d) Complex)
    (hApprox : IsApproxRepresentation G sigma rho eps) :
    HasFiniteHilbertWitness G sigma rho eps := by
  refine ⟨Index G d, inferInstance, inferInstance,
    embedding G rho, embedding_isometry G rho hrho, rightRegular G d, ?_⟩
  change
    (∑ x : G, sigmaNormSq sigma (rho x - regularCompression G rho x)) /
      Fintype.card G ≤ 2 * eps
  exact regularCompression_proximity G sigma hsigma hsigmatr rho eps hrho hApprox

end

end GH3
