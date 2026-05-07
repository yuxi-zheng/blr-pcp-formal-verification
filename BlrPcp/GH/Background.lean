import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Background lemmas for the Gowers-Hatami theorem

This file contains general facts that will be used in the proof of the Gowers Hatami theorem

The main ingredients are:

- the coordinate index `GH3.Index G d` for `L(G, ℂ^d)`;
- basic cardinality facts for finite averages;
- the right regular representation on `L(G, ℂ^d)`;
- algebraic facts about the `sigma`-norm;
- convexity and averaging estimates for the `sigma`-unit ball.

-/

open scoped Matrix ComplexConjugate ComplexOrder
open BigOperators Finset

universe u

variable {d : Nat}
variable (G : Type u) [Group G] [Fintype G]

namespace GH

noncomputable section

/-! ## Basic facts about a finite non-empty group G -/

/-- A nonempty finite group has positive cardinality as a real number. -/
theorem card_pos_real (G : Type*) [Fintype G] [Nonempty G] :
    0 < (Fintype.card G : Real) := by
  exact_mod_cast Fintype.card_pos

/-- A nonempty finite group has nonzero cardinality as a real number. -/
theorem card_ne_zero_real (G : Type*) [Fintype G] [Nonempty G] :
    (Fintype.card G : Real) ≠ 0 :=
  ne_of_gt (card_pos_real G)

/-- A nonempty finite group has nonzero cardinality as a complex number. -/
theorem card_ne_zero_complex (G : Type*) [Fintype G] [Nonempty G] :
    (Fintype.card G : Complex) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero


/-! ## Basic facts about unitary matrices -/


/-- The product `Aᴴ * B` of two unitary matrices is unitary. -/
theorem unitary_conjTranspose_mul
    {A B : Matrix (Fin d) (Fin d) Complex}
    (hA : A ∈ Matrix.unitaryGroup (Fin d) Complex)
    (hB : B ∈ Matrix.unitaryGroup (Fin d) Complex) :
    Aᴴ * B ∈ Matrix.unitaryGroup (Fin d) Complex := by
  let UA : Matrix.unitaryGroup (Fin d) Complex := ⟨A, hA⟩
  let UB : Matrix.unitaryGroup (Fin d) Complex := ⟨B, hB⟩
  have h : ((UA⁻¹ * UB : Matrix.unitaryGroup (Fin d) Complex) :
      Matrix (Fin d) (Fin d) Complex) ∈ Matrix.unitaryGroup (Fin d) Complex :=
    (UA⁻¹ * UB).property
  simpa [UA, UB, Matrix.star_eq_conjTranspose] using h

/-! ## Definition and properties of the sigma seminorm -/

def sigmaInner {n : ℕ} (σ A B : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  Matrix.trace (Aᴴ * B * σ)

def sigmaNormSq {n : ℕ} (σ A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (sigmaInner σ A A).re

private theorem sigma_cross_re_comm
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
      _ = star (Matrix.trace (Aᴴ * B * sigma)) :=
              Matrix.trace_conjTranspose _
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

/-- A unitary matrix has `sigma`-norm one against a trace-one state. -/
theorem sigmaNormSq_unitary
    (sigma A : Matrix (Fin d) (Fin d) Complex)
    (hsigmatr : Matrix.trace sigma = 1)
    (hA : A ∈ Matrix.unitaryGroup (Fin d) Complex) :
    sigmaNormSq sigma A = 1 := by
  have hA' : Aᴴ * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hA
  unfold sigmaNormSq sigmaInner
  simp [hA', hsigmatr]


/-! ## Convexity of the `sigma`-unit ball -/

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
  unfold sigmaNormSq sigmaInner
  have h : (Matrix.trace (Aᴴ * A * sigma)).re =
      (Matrix.trace (A * sigma * Aᴴ)).re := by
    simpa [Matrix.mul_assoc] using
      congrArg Complex.re (Matrix.trace_mul_comm Aᴴ (A * sigma))
  rw [h]
  rw [@norm_sq_eq_re_inner Complex (Matrix (Fin d) (Fin d) Complex) _ _ _ A]
  rfl

/-- The `sigma`-unit ball is convex. -/
theorem sigmaNormSq_average_le_one
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (hsigma : Matrix.PosSemidef sigma)
    (F : G → Matrix (Fin d) (Fin d) Complex)
    (hF : ∀ x, sigmaNormSq sigma (F x) ≤ 1) :
    sigmaNormSq sigma ((Fintype.card G : Complex)⁻¹ • ∑ x : G, F x) ≤ 1 := by
  letI : SeminormedAddCommGroup (Matrix (Fin d) (Fin d) Complex) :=
    Matrix.toMatrixSeminormedAddCommGroup sigma hsigma
  letI : InnerProductSpace Complex (Matrix (Fin d) (Fin d) Complex) :=
    Matrix.toMatrixInnerProductSpace sigma hsigma
  have hcard_ne : (Fintype.card G : Real) ≠ 0 := card_ne_zero_real G
  have hnormF : ∀ x : G, ‖F x‖ ≤ 1 := by
    intro x
    have hsq : ‖F x‖ ^ 2 ≤ 1 := by
      simpa [sigmaNormSq_eq_matrix_norm_sq sigma (F x) hsigma] using hF x
    nlinarith [norm_nonneg (F x)]
  have havg_mem' :
      (∑ x ∈ (Finset.univ : Finset G), ((Fintype.card G : Real)⁻¹) • F x) ∈
        Metric.closedBall (0 : Matrix (Fin d) (Fin d) Complex) 1 := by
    refine (convex_closedBall (0 : Matrix (Fin d) (Fin d) Complex) (1 : Real)).sum_mem
      (t := Finset.univ) (w := fun _ : G => (Fintype.card G : Real)⁻¹)
      (z := F) ?_ ?_ ?_
    · intro _ _
      exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp [hcard_ne]
    · intro x _
      simpa [Metric.mem_closedBall, dist_eq_norm] using hnormF x
  have havg_mem :
      (∑ x : G, ((Fintype.card G : Real)⁻¹) • F x) ∈
        Metric.closedBall (0 : Matrix (Fin d) (Fin d) Complex) 1 := by
    simpa using havg_mem'
  have hsame :
      (∑ x : G, ((Fintype.card G : Real)⁻¹) • F x) =
        (Fintype.card G : Complex)⁻¹ • ∑ x : G, F x := by
    rw [← Finset.smul_sum]
    rw [← algebraMap_smul Complex ((Fintype.card G : Real)⁻¹) (∑ x : G, F x)]
    simp
  have havg_norm :
      ‖((Fintype.card G : Complex)⁻¹ • ∑ x : G, F x)‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm, hsame] using havg_mem
  have hsq_avg : ‖((Fintype.card G : Complex)⁻¹ • ∑ x : G, F x)‖ ^ 2 ≤ 1 := by
    nlinarith [havg_norm,
      norm_nonneg ((Fintype.card G : Complex)⁻¹ • ∑ x : G, F x)]
  simpa [sigmaNormSq_eq_matrix_norm_sq sigma
    ((Fintype.card G : Complex)⁻¹ • ∑ x : G, F x) hsigma] using hsq_avg

/-- Averaging the affine expression `2 - 2 c_x`. -/
theorem average_two_sub_two_mul (c : G → Real) :
    (∑ x : G, (2 - 2 * c x)) / Fintype.card G =
      2 - 2 * ((∑ x : G, c x) / Fintype.card G) := by
  have hcard_ne : (Fintype.card G : Real) ≠ 0 := card_ne_zero_real G
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp [hcard_ne]
  simp [Finset.card_univ]
  rw [← Finset.mul_sum]
  ring

end


/-! ## The right regular representation -/

/-- We index the Hilbert space `L(G, ℂ^d)` as follows. -/
abbrev Index (G : Type u) (d : Nat) := G × Fin d

/-- Right translation on the `G` coordinate. -/
def rightShift (x : G) : Equiv.Perm (Index G d) where
  toFun y := (y.1 * x, y.2)
  invFun y := (y.1 * x⁻¹, y.2)
  left_inv y := by simp [mul_assoc]
  right_inv y := by simp [mul_assoc]

@[simp]
theorem rightShift_one (G : Type*) [Group G] {d : Nat} :
    rightShift (G := G) (d := d) 1 = 1 := by
  ext y <;> simp [rightShift]

/-- Right shifts compose contravariantly, as functions act on the right. -/
theorem rightShift_mul (G : Type*) [Group G] {d : Nat} (x y : G) :
    rightShift (G := G) (d := d) (x * y) =
      rightShift (G := G) (d := d) y * rightShift (G := G) (d := d) x := by
  ext a <;> simp [rightShift, mul_assoc]

/-- The right-regular permutation matrix. -/
def rightRegularMatrix [DecidableEq G] (x : G) :
    Matrix (Index G d) (Index G d) Complex :=
  (rightShift (G := G) (d := d) x).permMatrix Complex

/-- The right-regular matrix is unitary. -/
theorem rightRegularMatrix_unitary [DecidableEq G] (x : G) :
    rightRegularMatrix (G := G) (d := d) x ∈
      Matrix.unitaryGroup (Index G d) Complex := by
  rw [Matrix.mem_unitaryGroup_iff]
  change (rightShift (G := G) (d := d) x).permMatrix Complex *
      ((rightShift (G := G) (d := d) x).permMatrix Complex)ᴴ = 1
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

@[simp]
theorem rightRegularMatrix_one (G : Type*) [Group G] [DecidableEq G] {d : Nat} :
    rightRegularMatrix (G := G) (d := d) 1 = 1 := by
  change (rightShift (G := G) (d := d) 1).permMatrix Complex = 1
  simp

@[simp]
theorem rightRegularMatrix_mul [DecidableEq G] (x y : G) :
    rightRegularMatrix (G := G) (d := d) (x * y) =
      rightRegularMatrix (G := G) (d := d) x *
        rightRegularMatrix (G := G) (d := d) y := by
  change (rightShift (G := G) (d := d) (x * y)).permMatrix Complex =
    (rightShift (G := G) (d := d) x).permMatrix Complex *
      (rightShift (G := G) (d := d) y).permMatrix Complex
  rw [rightShift_mul G x y, Matrix.permMatrix_mul]

/-- The right-regular matrix, bundled as a unitary matrix. -/
def rightRegularUnitary [DecidableEq G] (x : G) :
    Matrix.unitaryGroup (Index G d) Complex :=
  ⟨rightRegularMatrix (G := G) (d := d) x, rightRegularMatrix_unitary (G := G) x⟩

/-- The right regular representation on `L(G, ℂ^d)`. -/
def rightRegular [DecidableEq G] (d : Nat) :
    G →* Matrix.unitaryGroup (Index G d) Complex where
  toFun := rightRegularUnitary G
  map_one' := by
    apply Subtype.ext
    simp [rightRegularUnitary]
  map_mul' x y := by
    apply Subtype.ext
    simp [rightRegularUnitary]

@[simp]
theorem rightRegular_apply [DecidableEq G] (x : G) :
    (rightRegular G d x : Matrix (Index G d) (Index G d) Complex) =
      rightRegularMatrix (G := G) (d := d) x :=
  rfl

/-- Multiplying by a right-regular matrix shifts the `G` coordinate of a column matrix. -/
theorem rightRegularMatrix_mul_apply [DecidableEq G]
    (x : G) (M : Matrix (Index G d) (Fin d) Complex)
    (y : Index G d) (j : Fin d) :
    (rightRegularMatrix (G := G) (d := d) x * M) y j =
      M (y.1 * x, y.2) j := by
  change
    (((rightShift (G := G) (d := d) x).toPEquiv.toMatrix :
        Matrix (Index G d) (Index G d) Complex) * M) y j =
      M ((rightShift (G := G) (d := d) x) y) j
  rw [PEquiv.toMatrix_toPEquiv_mul]
  rfl



end GH
