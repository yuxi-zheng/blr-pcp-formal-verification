/-
Authors: Serhat Emre Coban, Davide Mazzali, Khanh Nguyen, Vincent Palma, Yanting Teng, Thomas Vidick, Yuxi Zheng
-/
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Matrix.Permutation

open scoped Matrix ComplexConjugate ComplexOrder
open BigOperators Finset

/-!
# A finite-dimensional Gowers--Hatami theorem

The file proves `gowers_hatami_abstract`: a unitary-valued approximate
representation, measured by the averaged correlation defect below, is
well-approximated by a finite-dimensional representation.

The proof is organized as follows.

1. We first define the `σ`-weighted Hilbert--Schmidt seminorm and show
   basic identities about it.
2. We build the finite left-regular unitary representation on `G × Fin d`.
3. We introduce the Stinespring isometry. It is indexed inverse to the
   standard mathlib intexing, so as to make the compressed regular
   representation close to `ρ`.
4. We use Jensen convexity to bound the Stinespring compression error by the
   multiplicative defect, and identify that defect with `2 * correlationDefect`.
5. The final theorem follows.
-/

universe u

variable {d : Nat}
variable (G : Type u) [Group G] [Fintype G]

namespace GowersHatami

/-! ## Sigma-Weighted Seminorm

This group defines the `σ`-weighted Hilbert--Schmidt seminorm and proves the
basic algebraic identities used later in the stability estimate.
-/

/-- The `σ`-weighted matrix inner product, linear in the second matrix. -/
noncomputable def sigmaInner {n : ℕ} (σ A B : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  Matrix.trace (Aᴴ * B * σ)

/--
The squared `σ`-seminorm.  We use mathlib's
seminormed group instance attached to `σ`.
-/
noncomputable def sigmaNormSq {n : ℕ} (σ A : Matrix (Fin n) (Fin n) ℂ)
    (hσ : Matrix.PosSemidef σ) : ℝ := by
  classical
  letI : SeminormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.toMatrixSeminormedAddCommGroup σ hσ
  exact ‖A‖ ^ 2

private lemma sigmaNormSq_eq_re_sigmaInner_of_posSemidef {n : ℕ}
    {σ A : Matrix (Fin n) (Fin n) ℂ}
    (hσ : Matrix.PosSemidef σ) :
    sigmaNormSq σ A hσ = (sigmaInner σ A A).re := by
  classical
  unfold sigmaNormSq
  letI : SeminormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.toMatrixSeminormedAddCommGroup σ hσ
  letI : InnerProductSpace ℂ (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.toMatrixInnerProductSpace σ hσ
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) A]
  change (Matrix.trace (A * σ * Aᴴ)).re = (sigmaInner σ A A).re
  unfold sigmaInner
  rw [Matrix.trace_mul_cycle]

private lemma weightedMatrix_inner_eq_sigmaInner {n : ℕ}
    {σ A B : Matrix (Fin n) (Fin n) ℂ}
    (hσ : Matrix.PosSemidef σ) :
    letI : SeminormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
      Matrix.toMatrixSeminormedAddCommGroup σ hσ
    letI : InnerProductSpace ℂ (Matrix (Fin n) (Fin n) ℂ) :=
      Matrix.toMatrixInnerProductSpace σ hσ
    inner ℂ A B = sigmaInner σ A B := by
  letI : SeminormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.toMatrixSeminormedAddCommGroup σ hσ
  letI : InnerProductSpace ℂ (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.toMatrixInnerProductSpace σ hσ
  change Matrix.trace (B * σ * Aᴴ) = sigmaInner σ A B
  unfold sigmaInner
  rw [Matrix.trace_mul_cycle]

private lemma sigmaNormSq_sub_eq {n : ℕ}
    {σ A B : Matrix (Fin n) (Fin n) ℂ}
    (hσ : Matrix.PosSemidef σ) :
    sigmaNormSq σ (A - B) hσ =
      sigmaNormSq σ A hσ - 2 * (sigmaInner σ A B).re + sigmaNormSq σ B hσ := by
  classical
  rw [sigmaNormSq_eq_re_sigmaInner_of_posSemidef hσ]
  rw [sigmaNormSq_eq_re_sigmaInner_of_posSemidef hσ]
  rw [sigmaNormSq_eq_re_sigmaInner_of_posSemidef hσ]
  letI : SeminormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.toMatrixSeminormedAddCommGroup σ hσ
  letI : InnerProductSpace ℂ (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.toMatrixInnerProductSpace σ hσ
  rw [← weightedMatrix_inner_eq_sigmaInner hσ (A := A - B) (B := A - B)]
  rw [← weightedMatrix_inner_eq_sigmaInner hσ (A := A) (B := A)]
  rw [← weightedMatrix_inner_eq_sigmaInner hσ (A := B) (B := B)]
  rw [← weightedMatrix_inner_eq_sigmaInner hσ (A := A) (B := B)]
  simpa [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)] using
    norm_sub_sq (𝕜 := ℂ) A B

private lemma norm_sq_average_le_average_norm_sq
    {ι E : Type*} [Fintype ι] [Nonempty ι]
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ι → E) :
    ‖(∑ i : ι, ((Fintype.card ι : ℝ)⁻¹) • A i)‖ ^ 2 ≤
      ∑ i : ι, ((Fintype.card ι : ℝ)⁻¹) • (‖A i‖ ^ 2) := by
  let hconv : ConvexOn ℝ (Set.univ : Set E) (fun x : E => ‖x‖ ^ 2) := by
    let h : ConvexOn ℝ (Set.univ : Set E) (fun x : E => ‖x‖) :=
      convexOn_norm (s := Set.univ) convex_univ
    simpa using h.pow (by intro x _hx; exact norm_nonneg x) 2
  refine hconv.map_sum_le ?_ ?_ ?_
  · intro i _hi
    positivity
  · simp
  · intro i _hi
    simp

private lemma sigmaNormSq_average_le_average
    {ι : Type*} [Fintype ι] [Nonempty ι] {n : ℕ}
    {σ : Matrix (Fin n) (Fin n) ℂ}
    (hσ : Matrix.PosSemidef σ)
    (A : ι → Matrix (Fin n) (Fin n) ℂ) :
    sigmaNormSq σ (∑ i : ι, ((Fintype.card ι : ℝ)⁻¹) • A i) hσ ≤
      (∑ i : ι, sigmaNormSq σ (A i) hσ) / Fintype.card ι := by
  classical
  letI : SeminormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.toMatrixSeminormedAddCommGroup σ hσ
  letI : InnerProductSpace ℂ (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.toMatrixInnerProductSpace σ hσ
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := by
    infer_instance
  have hleft :
      sigmaNormSq σ (∑ i : ι, ((Fintype.card ι : ℝ)⁻¹) • A i) hσ =
        ‖(∑ i : ι, ((Fintype.card ι : ℝ)⁻¹) • A i)‖ ^ 2 := by
    unfold sigmaNormSq
    rfl
  have hright :
      (∑ i : ι, sigmaNormSq σ (A i) hσ) / Fintype.card ι =
        (∑ i : ι, ‖A i‖ ^ 2) / Fintype.card ι := by
    simp [sigmaNormSq]
  calc
    sigmaNormSq σ (∑ i : ι, ((Fintype.card ι : ℝ)⁻¹) • A i) hσ
        = ‖(∑ i : ι, ((Fintype.card ι : ℝ)⁻¹) • A i)‖ ^ 2 := hleft
    _ ≤ ∑ i : ι, ((Fintype.card ι : ℝ)⁻¹) • (‖A i‖ ^ 2) :=
          norm_sq_average_le_average_norm_sq (E := Matrix (Fin n) (Fin n) ℂ) A
    _ = (∑ i : ι, ‖A i‖ ^ 2) / Fintype.card ι := by
          rw [div_eq_mul_inv, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _hi
          simp [smul_eq_mul, mul_comm]
    _ = (∑ i : ι, sigmaNormSq σ (A i) hσ) / Fintype.card ι := by
          simp [hright]

private lemma conjTranspose_eq_star {n : Type*} [DecidableEq n] (A : Matrix n n Complex) :
    Aᴴ = star A := by
  ext i j
  simp [Matrix.star_apply, Matrix.conjTranspose_apply]

private lemma sigmaNormSq_unitary_of_posSemidef {n : ℕ}
    {σ U : Matrix (Fin n) (Fin n) ℂ}
    (hσ : Matrix.PosSemidef σ)
    (htr : Matrix.trace σ = 1)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
  sigmaNormSq σ U hσ = 1 := by
  rw [sigmaNormSq_eq_re_sigmaInner_of_posSemidef hσ]
  unfold sigmaInner
  have hUU : Uᴴ * U = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    simpa [conjTranspose_eq_star] using Matrix.mem_unitaryGroup_iff'.mp hU
  rw [hUU]
  simp [htr]

private lemma sigmaNormSq_left_unitary_mul
    {n : ℕ}
    {σ U A : Matrix (Fin n) (Fin n) ℂ}
    (hσ : Matrix.PosSemidef σ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
  sigmaNormSq σ (U * A) hσ = sigmaNormSq σ A hσ := by
  rw [sigmaNormSq_eq_re_sigmaInner_of_posSemidef hσ]
  rw [sigmaNormSq_eq_re_sigmaInner_of_posSemidef hσ]
  unfold sigmaInner
  have hUU : Uᴴ * U = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    simpa [conjTranspose_eq_star] using Matrix.mem_unitaryGroup_iff'.mp hU
  rw [Matrix.conjTranspose_mul]
  rw [show Aᴴ * Uᴴ * (U * A) * σ = Aᴴ * (Uᴴ * U) * A * σ by noncomm_ring]
  rw [hUU]
  simp

/-- The `σ`-weighted average distance between two maps `f` and `g`. -/
noncomputable def averageSigmaDistance
    (σ : Matrix (Fin d) (Fin d) ℂ)
    (hσ : Matrix.PosSemidef σ)
    (f g : G → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (∑ x : G, sigmaNormSq σ (f x - g x) hσ) / Fintype.card G

/-- The approximate representation hypothesis used by the final theorem. -/
noncomputable def IsApproxRepresentation
    (σ : Matrix (Fin d) (Fin d) ℂ)
    (f : G → Matrix (Fin d) (Fin d) ℂ)
    (ε : ℝ) : Prop :=
  (∀ x, f x ∈ Matrix.unitaryGroup (Fin d) Complex) ∧
    (∑ x : G, ∑ y : G,
      (sigmaInner σ (f x * f y) (f (x * y))).re) /
      (Fintype.card G ^ 2 : ℝ) ≥ 1 - ε

/-- The `σ`-weighted average correlation of `f`, measuring how multiplicative `f` is. -/
noncomputable def averageCorrelation
    (σ : Matrix (Fin d) (Fin d) ℂ)
    (f : G → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (∑ x : G, ∑ y : G,
    (sigmaInner σ (f x * f y) (f (x * y))).re) /
    (Fintype.card G ^ 2 : ℝ)

/-- How far `f` is from being a homomorphism: `1 - averageCorrelation G σ f`. -/
noncomputable def correlationDefect
    (σ : Matrix (Fin d) (Fin d) ℂ)
    (f : G → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  1 - averageCorrelation G σ f

/-- Predicate asserting that every value of `f` lies in the unitary group. -/
noncomputable def UnitaryValued
    (f : G → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ x, f x ∈ Matrix.unitaryGroup (Fin d) Complex

omit [Group G] [Fintype G] in
private lemma sigmaNormSq_sub_unitary_mul_eq
    {σ : Matrix (Fin d) (Fin d) ℂ}
    {rho : G → Matrix (Fin d) (Fin d) ℂ}
    (hσ : Matrix.PosSemidef σ)
    (hunit : UnitaryValued G rho)
    (a b g : G) :
    sigmaNormSq σ (rho g - (rho a)ᴴ * rho b) hσ =
      sigmaNormSq σ (rho a * rho g - rho b) hσ := by
  rw [← sigmaNormSq_left_unitary_mul (σ := σ) (U := rho a)
    (A := rho g - (rho a)ᴴ * rho b) hσ (hunit a)]
  congr 1
  have haa : rho a * (rho a)ᴴ = (1 : Matrix (Fin d) (Fin d) ℂ) := by
    simpa [conjTranspose_eq_star] using Unitary.mul_star_self_of_mem (hunit a)
  rw [show rho a * (rho g - (rho a)ᴴ * rho b) =
      rho a * rho g - (rho a * (rho a)ᴴ) * rho b by noncomm_ring]
  rw [haa]
  simp

/-! ## Regular Representation

This group builds the finite left-regular unitary representation on `G × Fin d`
that will serve as the enlarged exact representation.
-/

private noncomputable abbrev RegularIndex (G : Type u) (d : Nat) : Type u :=
  G × Fin d

omit [Fintype G] in
private noncomputable def invEquiv : G ≃ G where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv := by intro x; simp
  right_inv := by intro x; simp

private noncomputable def regularNormalization (G : Type u) [Fintype G] : Complex :=
  ((Real.sqrt (Fintype.card G : ℝ) : ℂ))⁻¹

private lemma regularNormalization_mul_star_mul_card :
    regularNormalization G * star (regularNormalization G) * (Fintype.card G : Complex) = 1 := by
  unfold regularNormalization
  have hpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hsqrt_ne_real : Real.sqrt (Fintype.card G : ℝ) ≠ 0 := by positivity
  have hsqrt_ne : (Real.sqrt (Fintype.card G : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt_ne_real
  rw [show star (((Real.sqrt (Fintype.card G : ℝ) : ℂ))⁻¹) =
      ((Real.sqrt (Fintype.card G : ℝ) : ℂ))⁻¹ by simp]
  field_simp [hsqrt_ne]
  have hsq : (Real.sqrt (Fintype.card G : ℝ) : ℂ) ^ 2 = (Fintype.card G : ℂ) := by
    norm_num [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt hpos)]
  rw [← hsq]

private lemma regularNormalization_mul_star_eq_card_inv :
    regularNormalization G * star (regularNormalization G) = ((Fintype.card G : ℂ)⁻¹) := by
  have h := regularNormalization_mul_star_mul_card (G := G)
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hcard] at h ⊢
  exact h

omit [Group G] [Fintype G] in
private lemma unitaryValued_conjTranspose_mul
    {rho : G → Matrix (Fin d) (Fin d) Complex}
    (hunit : UnitaryValued G rho)
    (x : G) :
    (rho x)ᴴ * rho x = 1 := by
  simpa [conjTranspose_eq_star] using Matrix.mem_unitaryGroup_iff'.mp (hunit x)

omit [Group G] in
private lemma stinespring_inner_sum_of_unitaryValued
    {rho : G → Matrix (Fin d) (Fin d) Complex}
    (hunit : UnitaryValued G rho)
    (x : G)
    (i j : Fin d) :
    (∑ k : Fin d,
      regularNormalization G * star (rho x k i) *
        (star (regularNormalization G) * rho x k j)) =
      regularNormalization G * star (regularNormalization G) *
        (1 : Matrix (Fin d) (Fin d) Complex) i j := by
  have hx := congr_fun (congr_fun (unitaryValued_conjTranspose_mul (G := G) hunit x) i) j
  simp [Matrix.mul_apply] at hx
  have hx' :
      (∑ k : Fin d, star (rho x k i) * rho x k j) =
        (1 : Matrix (Fin d) (Fin d) Complex) i j := by
    simpa using hx
  calc
    (∑ k : Fin d,
      regularNormalization G * star (rho x k i) *
        (star (regularNormalization G) * rho x k j)) =
        ∑ k : Fin d,
          (regularNormalization G * star (regularNormalization G)) *
            (star (rho x k i) * rho x k j) := by
          apply Finset.sum_congr rfl
          intro k _hk
          ring
    _ = regularNormalization G * star (regularNormalization G) *
        (∑ k : Fin d, star (rho x k i) * rho x k j) := by
          rw [Finset.mul_sum]
    _ = regularNormalization G * star (regularNormalization G) *
        (1 : Matrix (Fin d) (Fin d) Complex) i j := by
          rw [hx']

private noncomputable def leftRegularPerm (g : G) : Equiv.Perm (RegularIndex G d) :=
  (Equiv.mulLeft g).prodCongr (Equiv.refl (Fin d))

omit [Fintype G] in
private lemma leftRegularPerm_one :
    leftRegularPerm (G := G) (d := d) 1 = 1 := by
  ext x <;> simp [leftRegularPerm]

omit [Fintype G] in
private lemma leftRegularPerm_mul (g h : G) :
    leftRegularPerm (G := G) (d := d) (g * h) =
      leftRegularPerm (G := G) (d := d) g * leftRegularPerm (G := G) (d := d) h := by
  ext x <;> simp [leftRegularPerm, mul_assoc]

private noncomputable def leftRegularMatrix [DecidableEq G] (g : G) :
    Matrix (RegularIndex G d) (RegularIndex G d) Complex :=
  Equiv.Perm.permMatrix Complex (leftRegularPerm (G := G) (d := d) g)

private lemma sum_leftRegular_single [DecidableEq G]
    (g x : G)
    (k : Fin d)
    (F : RegularIndex G d → Complex) :
    (∑ z : RegularIndex G d,
      if (leftRegularPerm (G := G) (d := d) g) z = (x, k) then F z else 0) =
      F (g⁻¹ * x, k) := by
  rw [Fintype.sum_equiv (leftRegularPerm (G := G) (d := d) g)
    (fun z => if (leftRegularPerm (G := G) (d := d) g) z = (x, k) then F z else 0)
    (fun y => if y = (x, k) then F ((leftRegularPerm (G := G) (d := d) g).symm y) else 0)]
  · simp [leftRegularPerm]
  · intro z
    simp

omit [Group G] in
private lemma sum_perm_ite_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (i : α) :
    (∑ x : α, if σ x = i then (1 : Complex) else 0) = 1 := by
  rw [Fintype.sum_equiv σ
    (fun x => if σ x = i then (1 : Complex) else 0)
    (fun y => if y = i then (1 : Complex) else 0)]
  · simp
  · intro x
    simp

omit [Group G] in
private lemma sum_perm_double_ite_eq_zero {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) {i j : α} (hij : i ≠ j) :
    (∑ x : α, if σ x = j then if σ x = i then (1 : Complex) else 0 else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro x _hx
  by_cases hj : σ x = j
  · have hji : ¬j = i := fun h => hij h.symm
    simp [hj, hji]
  · simp [hj]

private lemma leftRegularMatrix_mem_unitary [DecidableEq G] (g : G) :
    leftRegularMatrix (G := G) (d := d) g ∈
      Matrix.unitaryGroup (RegularIndex G d) Complex := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : i = j
  · subst j
    rw [Matrix.one_apply]
    simp [leftRegularMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.star_apply]
    rw [show (∑ x,
        if (leftRegularPerm (G := G) (d := d) g) x = i then
          if (leftRegularPerm (G := G) (d := d) g) x = i then (1 : Complex) else 0
        else 0) =
        ∑ x, if (leftRegularPerm (G := G) (d := d) g) x = i then (1 : Complex) else 0 by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases h : (leftRegularPerm (G := G) (d := d) g) x = i <;> simp [h]]
    exact sum_perm_ite_eq_one (leftRegularPerm (G := G) (d := d) g) i
  · rw [Matrix.one_apply]
    simp [hij, leftRegularMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Matrix.star_apply, sum_perm_double_ite_eq_zero (leftRegularPerm (G := G) (d := d) g) hij]

private noncomputable def leftRegularUnitary [DecidableEq G] (g : G) :
    Matrix.unitaryGroup (RegularIndex G d) Complex :=
  ⟨leftRegularMatrix (G := G) (d := d) g, leftRegularMatrix_mem_unitary (G := G) (d := d) g⟩

private lemma leftRegularMatrix_mul [DecidableEq G] (g h : G) :
    leftRegularMatrix (G := G) (d := d) (g * h) =
      leftRegularMatrix (G := G) (d := d) h *
        leftRegularMatrix (G := G) (d := d) g := by
  simp [leftRegularMatrix, leftRegularPerm_mul]

omit [Fintype G] in
private lemma leftRegularMatrix_one [DecidableEq G] :
    leftRegularMatrix (G := G) (d := d) 1 = 1 := by
  ext i j
  simp [leftRegularMatrix, leftRegularPerm_one, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Matrix.one_apply]

private noncomputable def regularUnitaryRep [DecidableEq G] :
    G →* Matrix.unitaryGroup (RegularIndex G d) Complex where
  toFun g := leftRegularUnitary (G := G) (d := d) g⁻¹
  map_one' := by
    ext i j
    simp [leftRegularUnitary, leftRegularMatrix_one]
  map_mul' g h := by
    ext i j
    change
      leftRegularMatrix (G := G) (d := d) (g * h)⁻¹ i j =
        (leftRegularMatrix (G := G) (d := d) g⁻¹ *
          leftRegularMatrix (G := G) (d := d) h⁻¹) i j
    rw [mul_inv_rev, leftRegularMatrix_mul]

/-! ## Stinespring Construction

This group constructs the Stinespring isometry and proves the formulas relating
its compressed regular representation to group averages of `rho`.
-/

private noncomputable def stinespringMap
    (rho : G → Matrix (Fin d) (Fin d) Complex) :
    Matrix (Fin d) (RegularIndex G d) Complex :=
  fun i xj => regularNormalization G * (rho xj.1)ᴴ i xj.2

private noncomputable def inverseIndexedRho
    (rho : G → Matrix (Fin d) (Fin d) Complex) :
    G → Matrix (Fin d) (Fin d) Complex :=
  fun x => rho x⁻¹

private noncomputable def inverseStinespringMap
    (rho : G → Matrix (Fin d) (Fin d) Complex) :
    Matrix (Fin d) (RegularIndex G d) Complex :=
  stinespringMap G (inverseIndexedRho G rho)

private lemma stinespringMap_mul_leftRegularMatrix_apply [DecidableEq G]
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (g x : G)
    (i k : Fin d) :
    (stinespringMap G rho * leftRegularMatrix (G := G) (d := d) g) i (x, k) =
      regularNormalization G * (rho (g⁻¹ * x))ᴴ i k := by
  rw [Matrix.mul_apply]
  simp [stinespringMap, leftRegularMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  exact sum_leftRegular_single (G := G) (d := d) g x k
    (fun z => regularNormalization G * (starRingEnd ℂ) (rho z.1 z.2 i))

private noncomputable def stinespringCompression [DecidableEq G]
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (g : G) : Matrix (Fin d) (Fin d) Complex :=
  stinespringMap G rho * leftRegularMatrix (G := G) (d := d) g * (stinespringMap G rho)ᴴ

private noncomputable def inverseStinespringCompression [DecidableEq G]
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (g : G) : Matrix (Fin d) (Fin d) Complex :=
  inverseStinespringMap G rho *
    (regularUnitaryRep (G := G) (d := d) g :
      Matrix (RegularIndex G d) (RegularIndex G d) Complex) *
    (inverseStinespringMap G rho)ᴴ

private noncomputable def averagedTranslate
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (g : G) : Matrix (Fin d) (Fin d) Complex :=
  (regularNormalization G * star (regularNormalization G)) •
    ∑ x : G, (rho (g⁻¹ * x))ᴴ * rho x

private noncomputable def StinespringCompressionFormula [DecidableEq G]
    (rho : G → Matrix (Fin d) (Fin d) Complex) : Prop :=
  ∀ g : G, stinespringCompression G rho g = averagedTranslate G rho g

private noncomputable def inverseAveragedTranslate
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (g : G) : Matrix (Fin d) (Fin d) Complex :=
  averagedTranslate G (inverseIndexedRho G rho) g⁻¹

private noncomputable def InverseStinespringCompressionFormula [DecidableEq G]
    (rho : G → Matrix (Fin d) (Fin d) Complex) : Prop :=
  ∀ g : G, inverseStinespringCompression G rho g = inverseAveragedTranslate G rho g

private lemma stinespringCompressionFormula_holds [DecidableEq G]
    (rho : G → Matrix (Fin d) (Fin d) Complex) :
    StinespringCompressionFormula G rho := by
  intro g
  ext i j
  rw [show stinespringCompression G rho g =
      (stinespringMap G rho * leftRegularMatrix (G := G) (d := d) g) *
        (stinespringMap G rho)ᴴ by rfl]
  rw [Matrix.mul_apply]
  calc
    (∑ x : RegularIndex G d,
      ((stinespringMap G rho * leftRegularMatrix (G := G) (d := d) g) i x) *
        ((stinespringMap G rho)ᴴ x j)) =
      ∑ x : G, ∑ k : Fin d,
        (regularNormalization G * (rho (g⁻¹ * x))ᴴ i k) *
          (star (regularNormalization G * (rho x)ᴴ j k)) := by
        simp [Fintype.sum_prod_type, stinespringMap_mul_leftRegularMatrix_apply,
          stinespringMap, Matrix.conjTranspose_apply]
    _ = (averagedTranslate G rho g) i j := by
        rw [averagedTranslate]
        simp [Matrix.smul_apply, smul_eq_mul]
        rw [show ((∑ x : G, (rho (g⁻¹ * x))ᴴ * rho x) i j) =
            ∑ x : G, ((rho (g⁻¹ * x))ᴴ * rho x) i j by
          rw [Finset.sum_apply, Finset.sum_apply]]
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _hx
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring

private lemma inverseStinespringCompression_eq_stinespringCompression [DecidableEq G]
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (g : G) :
    inverseStinespringCompression G rho g =
      stinespringCompression G (inverseIndexedRho G rho) g⁻¹ := by
  rfl

private lemma inverseStinespringCompressionFormula_holds [DecidableEq G]
    (rho : G → Matrix (Fin d) (Fin d) Complex) :
    InverseStinespringCompressionFormula G rho := by
  intro g
  rw [inverseStinespringCompression_eq_stinespringCompression]
  exact stinespringCompressionFormula_holds (G := G) (inverseIndexedRho G rho) g⁻¹

private lemma inverseAveragedTranslate_eq_average
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (g : G) :
    inverseAveragedTranslate G rho g =
      ((Fintype.card G : ℂ)⁻¹) • ∑ y : G, (rho (y * g⁻¹))ᴴ * rho y := by
  rw [inverseAveragedTranslate, averagedTranslate, regularNormalization_mul_star_eq_card_inv]
  congr 1
  rw [Fintype.sum_equiv (invEquiv G)
    (fun x : G => (inverseIndexedRho G rho ((g⁻¹)⁻¹ * x))ᴴ * inverseIndexedRho G rho x)
    (fun y : G => (rho (y * g⁻¹))ᴴ * rho y)]
  · intro x
    simp [invEquiv, inverseIndexedRho]

private lemma inverseCompression_error_eq_average [DecidableEq G]
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (g : G) :
    rho g - inverseStinespringCompression G rho g =
      ∑ y : G, ((Fintype.card G : ℝ)⁻¹) •
        (rho g - (rho (y * g⁻¹))ᴴ * rho y) := by
  rw [inverseStinespringCompressionFormula_holds G rho g]
  rw [inverseAveragedTranslate_eq_average]
  symm
  ext i j
  rw [show ((∑ y : G, ((Fintype.card G : ℝ)⁻¹) •
        (rho g - (rho (y * g⁻¹))ᴴ * rho y)) i j) =
        ∑ y : G, (((Fintype.card G : ℝ)⁻¹) •
        (rho g - (rho (y * g⁻¹))ᴴ * rho y)) i j by
      rw [Finset.sum_apply, Finset.sum_apply]]
  simp only [Matrix.sub_apply, Matrix.smul_apply]
  rw [show ((∑ y : G, (rho (y * g⁻¹))ᴴ * rho y) i j) =
        ∑ y : G, ((rho (y * g⁻¹))ᴴ * rho y) i j by
      rw [Finset.sum_apply, Finset.sum_apply]]
  simp
  calc
    (∑ x : G, (↑(Fintype.card G))⁻¹ *
        (rho g i j - ((rho (x * g⁻¹))ᴴ * rho x) i j)) =
        ∑ x : G, ((↑(Fintype.card G))⁻¹ * rho g i j -
          (↑(Fintype.card G))⁻¹ * ((rho (x * g⁻¹))ᴴ * rho x) i j) := by
          apply Finset.sum_congr rfl
          intro x _hx
          ring
    _ = rho g i j - (↑(Fintype.card G))⁻¹ *
          ∑ y : G, ((rho (y * g⁻¹))ᴴ * rho y) i j := by
          rw [Finset.sum_sub_distrib]
          rw [Finset.sum_const]
          simp only [nsmul_eq_mul]
          rw [Finset.mul_sum]
          simp

private noncomputable def StinespringIsometry
    (rho : G → Matrix (Fin d) (Fin d) Complex) : Prop :=
  stinespringMap G rho * (stinespringMap G rho)ᴴ = 1

private noncomputable def InverseStinespringIsometry
    (rho : G → Matrix (Fin d) (Fin d) Complex) : Prop :=
  inverseStinespringMap G rho * (inverseStinespringMap G rho)ᴴ = 1

private lemma stinespring_isometry_of_unitaryValued
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (hunit : UnitaryValued G rho) :
    StinespringIsometry G rho := by
  ext i j
  rw [Matrix.mul_apply]
  simp [stinespringMap, Fintype.sum_prod_type]
  calc
    (∑ x : G, ∑ x_1 : Fin d,
      regularNormalization G * (starRingEnd ℂ) (rho x x_1 i) *
        ((starRingEnd ℂ) (regularNormalization G) * rho x x_1 j)) =
        ∑ x : G,
          regularNormalization G * star (regularNormalization G) *
            (1 : Matrix (Fin d) (Fin d) Complex) i j := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact stinespring_inner_sum_of_unitaryValued (G := G) hunit x i j
    _ = (Fintype.card G : Complex) *
        (regularNormalization G * star (regularNormalization G) *
          (1 : Matrix (Fin d) (Fin d) Complex) i j) := by
          simp
    _ = (1 : Matrix (Fin d) (Fin d) Complex) i j := by
      by_cases hij : i = j
      · subst j
        simp
        calc
          (Fintype.card G : Complex) *
              (regularNormalization G * star (regularNormalization G)) =
              regularNormalization G * star (regularNormalization G) *
                (Fintype.card G : Complex) := by
            ring
          _ = 1 := regularNormalization_mul_star_mul_card (G := G)
      · simp [hij]

omit [Fintype G] in
private lemma inverseIndexedRho_unitaryValued
    {rho : G → Matrix (Fin d) (Fin d) Complex}
    (hunit : UnitaryValued G rho) :
    UnitaryValued G (inverseIndexedRho G rho) := by
  intro x
  exact hunit x⁻¹

private lemma inverseStinespring_isometry_of_unitaryValued
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (hunit : UnitaryValued G rho) :
    InverseStinespringIsometry G rho := by
  dsimp [InverseStinespringIsometry, inverseStinespringMap]
  exact stinespring_isometry_of_unitaryValued G (inverseIndexedRho G rho)
    (inverseIndexedRho_unitaryValued (G := G) hunit)

/-! ## Stability Estimate

This group bounds the inverse Stinespring compression error by the averaged
multiplicative defect, then by the correlation defect.
-/

private noncomputable def InverseStinespringCloseToInput [DecidableEq G]
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (eps : Real)
    (hσ : Matrix.PosSemidef sigma) : Prop :=
  averageSigmaDistance G sigma hσ rho (inverseStinespringCompression G rho) ≤ 2 * eps

private lemma inverseStinespring_pointwise_error_le_average [DecidableEq G]
    {σ : Matrix (Fin d) (Fin d) ℂ}
    {rho : G → Matrix (Fin d) (Fin d) ℂ}
    (hσ : Matrix.PosSemidef σ)
    (hunit : UnitaryValued G rho)
    (g : G) :
    sigmaNormSq σ (rho g - inverseStinespringCompression G rho g) hσ ≤
      (∑ y : G, sigmaNormSq σ (rho (y * g⁻¹) * rho g - rho y) hσ) /
        Fintype.card G := by
  rw [inverseCompression_error_eq_average]
  calc
    sigmaNormSq σ
        (∑ y : G, ((Fintype.card G : ℝ)⁻¹) •
          (rho g - (rho (y * g⁻¹))ᴴ * rho y)) hσ ≤
        (∑ y : G, sigmaNormSq σ (rho g - (rho (y * g⁻¹))ᴴ * rho y) hσ) /
          Fintype.card G :=
      sigmaNormSq_average_le_average hσ
        (fun y : G => rho g - (rho (y * g⁻¹))ᴴ * rho y)
    _ = (∑ y : G, sigmaNormSq σ (rho (y * g⁻¹) * rho g - rho y) hσ) /
          Fintype.card G := by
        congr 1
        apply Finset.sum_congr rfl
        intro y _hy
        rw [sigmaNormSq_sub_unitary_mul_eq (G := G) hσ hunit (y * g⁻¹) y g]

private lemma sum_div_reindex_mul_inv_right (F : G → G → ℝ) :
    (∑ g : G, (∑ y : G, F (y * g⁻¹) g) / Fintype.card G) =
      (∑ x : G, ∑ y : G, F x y) / Fintype.card G := by
  calc
    (∑ g : G, (∑ y : G, F (y * g⁻¹) g) / Fintype.card G) =
        (∑ g : G, ∑ y : G, F (y * g⁻¹) g) / Fintype.card G := by
      rw [Finset.sum_div]
    _ = (∑ x : G, ∑ y : G, F x y) / Fintype.card G := by
      congr 1
      calc
        (∑ g : G, ∑ y : G, F (y * g⁻¹) g) = ∑ g : G, ∑ x : G, F x g := by
          apply Finset.sum_congr rfl
          intro g _hg
          rw [Fintype.sum_equiv (Equiv.mulRight g⁻¹)
            (fun y : G => F (y * g⁻¹) g) (fun x : G => F x g)]
          · intro x
            rfl
        _ = ∑ x : G, ∑ y : G, F x y := by
          rw [Finset.sum_comm]

private lemma inverseStinespring_error_sum_le_defect_sum [DecidableEq G]
    {σ : Matrix (Fin d) (Fin d) ℂ}
    {rho : G → Matrix (Fin d) (Fin d) ℂ}
    (hσ : Matrix.PosSemidef σ)
    (hunit : UnitaryValued G rho) :
    (∑ g : G, sigmaNormSq σ (rho g - inverseStinespringCompression G rho g) hσ) ≤
      (∑ x : G, ∑ y : G, sigmaNormSq σ (rho x * rho y - rho (x * y)) hσ) /
        Fintype.card G := by
  calc
    (∑ g : G, sigmaNormSq σ (rho g - inverseStinespringCompression G rho g) hσ) ≤
        ∑ g : G,
          (∑ y : G, sigmaNormSq σ (rho (y * g⁻¹) * rho g - rho y) hσ) /
            Fintype.card G := by
          apply Finset.sum_le_sum
          intro g _hg
          exact inverseStinespring_pointwise_error_le_average (G := G) hσ hunit g
    _ = (∑ x : G, ∑ y : G, sigmaNormSq σ (rho x * rho y - rho (x * y)) hσ) /
          Fintype.card G := by
      simpa [mul_assoc] using
        sum_div_reindex_mul_inv_right (G := G)
          (fun x y => sigmaNormSq σ (rho x * rho y - rho (x * y)) hσ)

private lemma inverseStinespringDistance_le_multiplicativeDefect [DecidableEq G]
    {σ : Matrix (Fin d) (Fin d) ℂ}
    {rho : G → Matrix (Fin d) (Fin d) ℂ}
    (hσ : Matrix.PosSemidef σ)
    (hunit : UnitaryValued G rho) :
    averageSigmaDistance G σ hσ rho (inverseStinespringCompression G rho) ≤
      (∑ x : G, ∑ y : G, sigmaNormSq σ (rho x * rho y - rho (x * y)) hσ) /
        (Fintype.card G ^ 2 : ℝ) := by
  unfold averageSigmaDistance
  have hcard_pos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  calc
    (∑ x : G, sigmaNormSq σ (rho x - inverseStinespringCompression G rho x) hσ) /
        Fintype.card G ≤
        ((∑ x : G, ∑ y : G, sigmaNormSq σ (rho x * rho y - rho (x * y)) hσ) /
          Fintype.card G) / Fintype.card G :=
        div_le_div_of_nonneg_right
          (inverseStinespring_error_sum_le_defect_sum (G := G) hσ hunit)
          (le_of_lt hcard_pos)
    _ = (∑ x : G, ∑ y : G, sigmaNormSq σ (rho x * rho y - rho (x * y)) hσ) /
        (Fintype.card G ^ 2 : ℝ) := by
        field_simp [ne_of_gt hcard_pos, pow_two]

omit [Group G] [Fintype G] in
private lemma sigmaNormSq_mul_unitary_of_posSemidef
    {σ : Matrix (Fin d) (Fin d) ℂ}
    {rho : G → Matrix (Fin d) (Fin d) ℂ}
    (hσ : Matrix.PosSemidef σ)
    (htr : Matrix.trace σ = 1)
    (hunit : UnitaryValued G rho)
    (x y : G) :
    sigmaNormSq σ (rho x * rho y) hσ = 1 :=
  sigmaNormSq_unitary_of_posSemidef hσ htr (mul_mem (hunit x) (hunit y))

private lemma averageMultiplicativeDefect_eq_two_correlationDefect
    {σ : Matrix (Fin d) (Fin d) ℂ}
    {rho : G → Matrix (Fin d) (Fin d) ℂ}
    (hσ : Matrix.PosSemidef σ)
    (htr : Matrix.trace σ = 1)
    (hunit : UnitaryValued G rho) :
    (∑ x : G, ∑ y : G, sigmaNormSq σ (rho x * rho y - rho (x * y)) hσ) /
      (Fintype.card G ^ 2 : ℝ) =
        2 * correlationDefect G σ rho := by
  let S : ℝ := ∑ x : G, ∑ y : G, (sigmaInner σ (rho x * rho y) (rho (x * y))).re
  have hsum :
      (∑ x : G, ∑ y : G, sigmaNormSq σ (rho x * rho y - rho (x * y)) hσ) =
        2 * (Fintype.card G ^ 2 : ℝ) - 2 * S := by
    calc
      (∑ x : G, ∑ y : G, sigmaNormSq σ (rho x * rho y - rho (x * y)) hσ) =
          ∑ x : G,
            ∑ y : G, (2 - 2 * (sigmaInner σ (rho x * rho y) (rho (x * y))).re) := by
            apply Finset.sum_congr rfl
            intro x _hx
            apply Finset.sum_congr rfl
            intro y _hy
            rw [sigmaNormSq_sub_eq hσ]
            rw [sigmaNormSq_mul_unitary_of_posSemidef G hσ htr hunit]
            rw [sigmaNormSq_unitary_of_posSemidef hσ htr (hunit (x * y))]
            ring
      _ = 2 * (Fintype.card G ^ 2 : ℝ) - 2 * S := by
            simp [S, Finset.sum_sub_distrib, Finset.mul_sum, pow_two]
            ring
  rw [hsum]
  unfold correlationDefect averageCorrelation
  change (2 * (Fintype.card G ^ 2 : ℝ) - 2 * S) / (Fintype.card G ^ 2 : ℝ) =
    2 * (1 - S / (Fintype.card G ^ 2 : ℝ))
  have hcard : (Fintype.card G ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp [hcard]

private lemma inverseStinespringCloseToInput_of_correlationDefect [DecidableEq G]
    {σ : Matrix (Fin d) (Fin d) ℂ}
    {rho : G → Matrix (Fin d) (Fin d) ℂ}
    {eps : ℝ}
    (hσ : Matrix.PosSemidef σ)
    (htr : Matrix.trace σ = 1)
    (hunit : UnitaryValued G rho)
    (hdef : correlationDefect G σ rho ≤ eps) :
    InverseStinespringCloseToInput G σ rho eps hσ := by
  dsimp [InverseStinespringCloseToInput]
  have hdist := inverseStinespringDistance_le_multiplicativeDefect (G := G) hσ hunit
  rw [averageMultiplicativeDefect_eq_two_correlationDefect (G := G) hσ htr hunit] at hdist
  exact le_trans hdist (by nlinarith)

/-! ## Approximation Hypothesis

This group repackages the approximation hypothesis into unitary-valuedness and
a correlation-defect bound.
-/

/-- Repackage the original approximation hypothesis in terms of `correlationDefect`. -/
lemma isApproxRepresentation_iff
    (σ : Matrix (Fin d) (Fin d) ℂ)
    (f : G → Matrix (Fin d) (Fin d) ℂ)
    (ε : ℝ) :
    IsApproxRepresentation G σ f ε ↔
      UnitaryValued G f ∧ correlationDefect G σ f ≤ ε := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    dsimp [correlationDefect, averageCorrelation]
    linarith [h.2]
  · intro h
    refine ⟨h.1, ?_⟩
    dsimp [correlationDefect, averageCorrelation] at h
    linarith [h.2]

/-- An approximate representation is unitary-valued. -/
lemma IsApproxRepresentation.unitaryValued
    {σ : Matrix (Fin d) (Fin d) ℂ}
    {f : G → Matrix (Fin d) (Fin d) ℂ}
    {ε : ℝ}
    (h : IsApproxRepresentation G σ f ε) :
    UnitaryValued G f :=
  h.1

/-- An approximate representation has correlation defect at most `ε`. -/
lemma IsApproxRepresentation.correlationDefect_le
    {σ : Matrix (Fin d) (Fin d) ℂ}
    {f : G → Matrix (Fin d) (Fin d) ℂ}
    {ε : ℝ}
    (h : IsApproxRepresentation G σ f ε) :
    correlationDefect G σ f ≤ ε :=
  (isApproxRepresentation_iff G σ f ε).mp h |>.2

/-! ## Finite Witness

This group packages the Stinespring construction into the finite Hilbert-space
witness used by the abstract theorem.
-/

/-- The compression of a unitary representation `rho0` by an isometry `V`. -/
noncomputable def compression {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix (Fin d) ι Complex)
    (rho0 : G →* Matrix.unitaryGroup ι Complex)
    (x : G) : Matrix (Fin d) (Fin d) Complex :=
  V * (rho0 x : Matrix ι ι Complex) * Vᴴ

/--
The target conclusion: a finite Hilbert space, an isometry `V`, and a genuine
unitary representation whose compression is close to the original map.
-/
noncomputable def HasFiniteHilbertWitness
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (hσ : Matrix.PosSemidef sigma)
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (eps : Real) : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι)
    (V : Matrix (Fin d) ι Complex)
    (_hV : V * Vᴴ = 1)
    (rho0 : G →* Matrix.unitaryGroup ι Complex),
    (∑ x : G, sigmaNormSq sigma (rho x - compression G V rho0 x) hσ) /
      Fintype.card G ≤ 2 * eps

private lemma inverse_stinespring_close_has_witness [DecidableEq G]
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (hσ : Matrix.PosSemidef sigma)
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (eps : Real)
    (hV : InverseStinespringIsometry G rho)
    (hclose : InverseStinespringCloseToInput G sigma rho eps hσ) :
    HasFiniteHilbertWitness G sigma hσ rho eps := by
  refine ⟨RegularIndex G d, inferInstance, inferInstance, inverseStinespringMap G rho,
    hV, regularUnitaryRep (G := G) (d := d), ?_⟩
  dsimp [InverseStinespringCloseToInput, averageSigmaDistance] at hclose
  dsimp [compression, inverseStinespringCompression, averageSigmaDistance] at hclose ⊢
  simpa using hclose

/--
Abstract Gowers--Hatami stability in this finite-dimensional formulation.
The proof builds the inverse-indexed Stinespring isometry and applies the
defect-to-compression estimate proved above.
-/
theorem gowers_hatami_abstract [DecidableEq G]
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (hsigma : Matrix.PosSemidef sigma) (hsigmatr : Matrix.trace sigma = 1)
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (eps : Real) (_heps : 0 ≤ eps)
    (hApprox : IsApproxRepresentation G sigma rho eps) :
    HasFiniteHilbertWitness G sigma hsigma rho eps :=
  inverse_stinespring_close_has_witness G sigma hsigma rho eps
    (inverseStinespring_isometry_of_unitaryValued G rho hApprox.unitaryValued)
    (inverseStinespringCloseToInput_of_correlationDefect (G := G)
      hsigma hsigmatr hApprox.unitaryValued hApprox.correlationDefect_le)
