import BlrPcp.FnFiniteFIelds.Basic

open scoped BigOperators

namespace BlrPcp

variable {F Idx : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]

/-- The linear scalar function `ℓ_a(x) = ⟪ a, x ⟫ᵥ`. -/
def linearFn (a : Vec F Idx) : ScalarFn F Idx :=
  fun x => ⟪ a, x ⟫ᵥ

/-- A function is linear if there exists a vector `a` such that `f(x)= ⟪ a, x ⟫ᵥ` -/
def IsLinear (f : ScalarFn F Idx) : Prop :=
  ∃ a : Vec F Idx, ∀ x, f x = linearFn a x

/-- The finite set of all linear scalar functions. -/
def LinearSet : Finset (ScalarFn F Idx) := by
  letI : DecidablePred fun f : ScalarFn F Idx => IsLinear f := fun f => by
    unfold IsLinear
    exact Fintype.decidableExistsFintype
  exact Finset.univ.filter fun f => IsLinear f

section Phases

omit [DecidableEq F] [DecidableEq Idx] [Nonempty Idx] in
/-- The `c`-phase of the linear function `ℓ_α` is the character `χ_{cα}`. -/
lemma phaseLift_linearFn (α : Vec F Idx) (c : F) :
    phaseLift (linearFn α) c = charFn (fun i => c * α i) := by
  classical
  funext x
  simp [phaseLift, charFn, linearFn, dotProduct, Finset.mul_sum, mul_assoc]

omit [Nonempty Idx] in
/-- Fourier expansion of a linear function: the `c`-phase of `ℓ_α` has a
single non-zero Fourier coefficient, at `cα`. -/
lemma fourierCoeff_phaseLift_linearFn (α β : Vec F Idx) (c : F) :
    fourierCoeff (phaseLift (linearFn α) c) β =
      if β = (fun i => c * α i) then 1 else 0 := by
  rw [phaseLift_linearFn]
  simpa [fourierCoeff, eq_comm] using
    (characters_orthonormal_basis (F := F) (Idx := Idx)).1 (fun i => c * α i) β

end Phases

section DistanceToLinear

omit [Nonempty Idx] in
/-- the set of linear function is non-empty,
which is needed to define distance to `LinearSet`
as the minimum distance across all linear functions -/
private lemma LinearSet_nonempty :
    (LinearSet (F := F) (Idx := Idx)).Nonempty := by
  refine ⟨linearFn (F := F) (Idx := Idx) 0, ?_⟩
  simp only [LinearSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨0, fun x => rfl⟩

/-- The distance from a scalar function to linearity, namely the minimum of
`distance f g` over all `g ∈ LinearSet`. -/
noncomputable def distanceToLinear (f : ScalarFn F Idx) : Real := by
  classical
  exact
    (LinearSet (F := F) (Idx := Idx)).inf'
      (LinearSet_nonempty (F := F) (Idx := Idx)) fun g => distance f g

omit [Nonempty Idx] in
/-- Rewrites the minimum over the finite set `LinearSet` as a minimum over
coefficient vectors `α`, using the parametrization `α ↦ linearFn α` of all
linear scalar functions. -/
lemma distanceToLinear_eq_inf_linearFn (f : ScalarFn F Idx) :
    distanceToLinear f =
      (Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Vec F Idx)).Nonempty)
        fun α => distance f (linearFn α)) := by
  classical
  unfold distanceToLinear
  let linearFns := LinearSet (F := F) (Idx := Idx)
  let hlinearFns := LinearSet_nonempty (F := F) (Idx := Idx)
  change linearFns.inf' hlinearFns (fun g => distance f g) =
    (Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Vec F Idx)).Nonempty)
      fun α => distance f (linearFn α))
  apply le_antisymm
  · apply Finset.le_inf'
    intro α _
    have hmem : linearFn α ∈ linearFns := by
      simp [linearFns, LinearSet, IsLinear]
      exact ⟨α, fun x => rfl⟩
    rw [Finset.inf'_le_iff]
    exact ⟨linearFn α, hmem, le_rfl⟩
  · apply Finset.le_inf'
    intro g hg
    have hg_linear : IsLinear g := by
      simpa [linearFns, LinearSet] using hg
    rcases hg_linear with ⟨α, hα⟩
    have hdist : distance f g = distance f (linearFn α) := by
      simp [distance, hα]
    have hle :
        (Finset.univ.inf'
          (Finset.univ_nonempty : (Finset.univ : Finset (Vec F Idx)).Nonempty)
          fun α => distance f (linearFn α)) ≤
            distance f (linearFn α) :=
      by
        rw [Finset.inf'_le_iff]
        exact ⟨α, by simp, le_rfl⟩
    simpa [hdist] using hle

/-- Complex Fourier score measuring how much `f` correlates with the linear
function `ℓ_α` across all nonzero phase lifts. The public real score below is
its real part, and the distance formula proves that this complex number is
real. -/
noncomputable def linearFourierScoreC (f : ScalarFn F Idx) (α : Vec F Idx) : ℂ :=
  ∑ c ∈ (nonzeroF (F := F)), fourierCoeff (phaseLift f c) (fun i => c * α i)

/-- The real Fourier score of `f` against the linear function `ℓ_α`. -/
noncomputable def linearFourierScore (f : ScalarFn F Idx) (α : Vec F Idx) : Real :=
  (linearFourierScoreC f α).re

/-- Complex-valued fixed-linear-function distance formula before taking real
parts. -/
private lemma distance_linearFn_fourierC (f : ScalarFn F Idx) (α : Vec F Idx) :
    (distance f (linearFn α) : ℂ) =
      1 - (Fintype.card F : ℂ)⁻¹ * (1 + linearFourierScoreC f α) := by
  rw [distance_formula_via_phase_fourier_coefficients]
  congr 2
  congr 1
  simp only [linearFourierScoreC]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_eq_single (fun i => c * α i)]
  · simp [fourierCoeff_phaseLift_linearFn]
  · intro β _ hβ
    rw [fourierCoeff_phaseLift_linearFn]
    simp [hβ]
  · intro hβ
    simp at hβ

/-- The distance from `f` to the fixed linear function `ℓ_α`, expressed through
the real linear Fourier score. -/
lemma distance_linearFn_fourier (f : ScalarFn F Idx) (α : Vec F Idx) :
    distance f (linearFn α) =
      1 - (Fintype.card F : Real)⁻¹ * (1 + linearFourierScore f α) := by
  have h := congrArg Complex.re (distance_linearFn_fourierC (F := F) (Idx := Idx) f α)
  simpa [linearFourierScore] using h

omit [Field F] [Nonempty Idx] in
/-- Hamming distance is nonnegative. -/
private lemma distance_nonneg (f g : ScalarFn F Idx) : 0 ≤ distance f g := by
  classical
  unfold distance
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun x _ => by
      by_cases hx : f x ≠ g x <;> simp [hx])

/-- Hamming distance is at most one. -/
private lemma distance_le_one (f g : ScalarFn F Idx) : distance f g ≤ 1 := by
  classical
  unfold distance
  have hsum :
      (∑ x : Vec F Idx, if f x ≠ g x then (1 : Real) else 0) ≤
        ∑ _x : Vec F Idx, (1 : Real) := by
    exact Finset.sum_le_sum fun x _ => by
      by_cases hx : f x ≠ g x <;> simp [hx]
  calc
    (Fintype.card (Vec F Idx) : Real)⁻¹ *
        (∑ x : Vec F Idx, if f x ≠ g x then (1 : Real) else 0) ≤
      (Fintype.card (Vec F Idx) : Real)⁻¹ * (∑ _x : Vec F Idx, (1 : Real)) := by
        exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = 1 := by
      simp

/-- The complex linear Fourier score is determined by the distance from `f` to
the corresponding linear function. -/
private lemma linearFourierScoreC_eq_card_mul_one_sub_distance (f : ScalarFn F Idx)
    (α : Vec F Idx) :
    linearFourierScoreC f α =
      (((Fintype.card F : Real) * (1 - distance f (linearFn α)) - 1 : Real) : ℂ) := by
  have hcard0 : (Fintype.card F : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have h := distance_linearFn_fourierC (F := F) (Idx := Idx) f α
  have h' :
      (Fintype.card F : ℂ) * (1 - (distance f (linearFn α) : ℂ)) =
        1 + linearFourierScoreC f α := by
    rw [h]
    field_simp [hcard0]
    ring
  calc
    linearFourierScoreC f α = (1 + linearFourierScoreC f α) - 1 := by ring
    _ = (Fintype.card F : ℂ) * (1 - (distance f (linearFn α) : ℂ)) - 1 := by
      rw [← h']
    _ = (((Fintype.card F : Real) * (1 - distance f (linearFn α)) - 1 : Real) : ℂ) := by
      norm_num

/-- The complex linear Fourier score has zero imaginary part. -/
private lemma linearFourierScoreC_im_eq_zero (f : ScalarFn F Idx) (α : Vec F Idx) :
    (linearFourierScoreC f α).im = 0 := by
  rw [linearFourierScoreC_eq_card_mul_one_sub_distance]
  simp

/-- The complex linear Fourier score is the complex coercion of the real public
score. -/
lemma linearFourierScoreC_eq_ofReal_score (f : ScalarFn F Idx)
    (α : Vec F Idx) :
    linearFourierScoreC f α = (linearFourierScore f α : ℂ) := by
  apply Complex.ext
  · simp [linearFourierScore]
  · simp [linearFourierScore,
      linearFourierScoreC_im_eq_zero (F := F) (Idx := Idx) f α]

/-- The real linear Fourier score is an affine rescaling of agreement with
`ℓ_α`. -/
lemma linearFourierScore_eq_card_mul_one_sub_distance (f : ScalarFn F Idx)
    (α : Vec F Idx) :
    linearFourierScore f α =
      (Fintype.card F : Real) * (1 - distance f (linearFn α)) - 1 := by
  have h := congrArg Complex.re
    (linearFourierScoreC_eq_card_mul_one_sub_distance (F := F) (Idx := Idx) f α)
  simpa [linearFourierScore] using h

/-- Every real linear Fourier score lies in the interval `[-1, |F| - 1]`. -/
lemma linearFourierScore_bounds (f : ScalarFn F Idx) (α : Vec F Idx) :
    -1 ≤ linearFourierScore f α ∧
      linearFourierScore f α ≤ (Fintype.card F : Real) - 1 := by
  have hd0 : 0 ≤ distance f (linearFn α) := distance_nonneg (F := F) (Idx := Idx) f (linearFn α)
  have hd1 : distance f (linearFn α) ≤ 1 := distance_le_one (F := F) (Idx := Idx) f (linearFn α)
  have hcard_nonneg : 0 ≤ (Fintype.card F : Real) := Nat.cast_nonneg _
  have hscore :=
    linearFourierScore_eq_card_mul_one_sub_distance (F := F) (Idx := Idx) f α
  constructor
  · rw [hscore]
    have hprod_nonneg :
        0 ≤ (Fintype.card F : Real) * (1 - distance f (linearFn α)) :=
      mul_nonneg hcard_nonneg (sub_nonneg.mpr hd1)
    linarith
  · rw [hscore]
    have hprod_le :
        (Fintype.card F : Real) * (1 - distance f (linearFn α)) ≤
          (Fintype.card F : Real) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) hcard_nonneg
    linarith

/-- Distance to linearity in Fourier form. -/
lemma distanceToLinear_fourier (f : ScalarFn F Idx) :
    distanceToLinear f =
      1 - (Fintype.card F : Real)⁻¹ *
        (1 + (Finset.univ.sup'
          (Finset.univ_nonempty : (Finset.univ : Finset (Vec F Idx)).Nonempty)
          (linearFourierScore f))) := by
  classical
  rw [distanceToLinear_eq_inf_linearFn]
  let score := linearFourierScore (F := F) (Idx := Idx) f
  let coeffs := (Finset.univ : Finset (Vec F Idx))
  let hcoeffs : coeffs.Nonempty := Finset.univ_nonempty
  let maxScore := coeffs.sup' hcoeffs score
  change coeffs.inf' hcoeffs (fun α => distance f (linearFn α)) =
    1 - (Fintype.card F : Real)⁻¹ * (1 + maxScore)
  apply le_antisymm
  · rcases Finset.exists_mem_eq_sup' (s := coeffs) (H := hcoeffs) score with
      ⟨α, hα_mem, hα_eq⟩
    have hdist := distance_linearFn_fourier (F := F) (Idx := Idx) f α
    have hle : coeffs.inf' hcoeffs (fun α => distance f (linearFn α)) ≤
        distance f (linearFn α) := by
      rw [Finset.inf'_le_iff]
      exact ⟨α, hα_mem, le_rfl⟩
    refine hle.trans_eq ?_
    rw [hdist]
    dsimp [maxScore]
    change 1 - (Fintype.card F : Real)⁻¹ * (1 + score α) =
      1 - (Fintype.card F : Real)⁻¹ * (1 + coeffs.sup' hcoeffs score)
    rw [← hα_eq]
  · apply Finset.le_inf'
    intro α hα_mem
    have hscore_le : score α ≤ maxScore :=
      Finset.le_sup' (s := coeffs) (f := score) hα_mem
    have hinv_nonneg : 0 ≤ (Fintype.card F : Real)⁻¹ :=
      inv_nonneg.mpr (Nat.cast_nonneg _)
    have hterm :
        1 - (Fintype.card F : Real)⁻¹ * (1 + maxScore) ≤
          1 - (Fintype.card F : Real)⁻¹ * (1 + score α) := by
      have hmul :
          (Fintype.card F : Real)⁻¹ * (1 + score α) ≤
            (Fintype.card F : Real)⁻¹ * (1 + maxScore) :=
        mul_le_mul_of_nonneg_left (by linarith) hinv_nonneg
      linarith
    simpa [distance_linearFn_fourier (F := F) (Idx := Idx) f α] using hterm

/-- Distance to linearity in Fourier form, together with the range of each
real linear Fourier score. -/
lemma distance_to_linearity_fourier (f : ScalarFn F Idx) :
    distanceToLinear f =
        1 - (Fintype.card F : Real)⁻¹ *
          (1 + (Finset.univ.sup'
            (Finset.univ_nonempty : (Finset.univ : Finset (Vec F Idx)).Nonempty)
            (linearFourierScore f))) ∧
      ∀ α : Vec F Idx,
        -1 ≤ linearFourierScore f α ∧
          linearFourierScore f α ≤ (Fintype.card F : Real) - 1 := by
  refine ⟨distanceToLinear_fourier (F := F) (Idx := Idx) f, ?_⟩
  intro α
  exact linearFourierScore_bounds (F := F) (Idx := Idx) f α

end DistanceToLinear

section ErrorCorrectionDiamater

/-- Distinct linear scalar functions are separated by exactly
`1 - 1 / |F|` in relative Hamming distance. -/
theorem linearSet_wellSeparated {f g : ScalarFn F Idx}
    (hf : f ∈ LinearSet (F := F) (Idx := Idx))
    (hg : g ∈ LinearSet (F := F) (Idx := Idx)) (hfg : f ≠ g) :
    distance f g = 1 - (Fintype.card F : Real)⁻¹ := by
  classical
  have hf_linear : IsLinear f := by
    simpa [LinearSet] using hf
  have hg_linear : IsLinear g := by
    simpa [LinearSet] using hg
  rcases hf_linear with ⟨a, ha⟩
  rcases hg_linear with ⟨b, hb⟩
  let c : Vec F Idx := a - b
  have hc : c ≠ 0 := by
    intro hc0
    apply hfg
    ext x
    rw [ha x, hb x]
    have hab : a = b := sub_eq_zero.mp hc0
    rw [hab]
  have hfiber_mul :
      ((Finset.univ.filter fun x : Vec F Idx => linearFn c x = 0).card) *
        Fintype.card F = Fintype.card (Vec F Idx) := by
    let L : Vec F Idx →+ F := {
      toFun := linearFn c
      map_zero' := by simp [linearFn, dotProduct]
      map_add' x y := by
        simp [linearFn, dotProduct, mul_add, Finset.sum_add_distrib]
    }
    have hsurj : Function.Surjective L := by
      obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
        by_contra h
        apply hc
        ext i
        by_contra hi
        exact h ⟨i, hi⟩
      intro t
      refine ⟨Pi.single i (t * (c i)⁻¹), ?_⟩
      change linearFn c (Pi.single i (t * (c i)⁻¹)) = t
      rw [linearFn, dotProduct, Finset.sum_eq_single i]
      · simp [Pi.single_eq_same]
        field_simp [hi]
      · intro j _ hij
        simp [Pi.single_eq_of_ne hij]
      · intro hi_univ
        simp at hi_univ
    have hfibers : ∀ u : F,
        (Finset.univ.filter fun x : Vec F Idx => L x = u).card =
          (Finset.univ.filter fun x : Vec F Idx => L x = 0).card := by
      intro u
      exact AddMonoidHom.card_fiber_eq_of_mem_range L (hsurj u) (hsurj 0)
    have hpartition :
        (∑ u : F, (Finset.univ.filter fun x : Vec F Idx => L x = u).card) =
          Fintype.card (Vec F Idx) := by
      simpa using
        (Finset.card_eq_sum_card_fiberwise
          (s := (Finset.univ : Finset (Vec F Idx)))
          (t := (Finset.univ : Finset F))
          (f := fun x : Vec F Idx => L x)
          (by intro x _; simp)).symm
    calc
      ((Finset.univ.filter fun x : Vec F Idx => linearFn c x = 0).card) *
          Fintype.card F =
        ((Finset.univ.filter fun x : Vec F Idx => L x = 0).card) *
          Fintype.card F := by rfl
      _ = ∑ _u : F, (Finset.univ.filter fun x : Vec F Idx => L x = 0).card := by
          simp [mul_comm]
      _ = ∑ u : F, (Finset.univ.filter fun x : Vec F Idx => L x = u).card := by
          apply Finset.sum_congr rfl
          intro u _
          exact (hfibers u).symm
      _ = Fintype.card (Vec F Idx) := hpartition
  have hagreement :
      (∑ x : Vec F Idx, (if f x = g x then (1 : Real) else 0)) =
        ((Finset.univ.filter fun x : Vec F Idx => linearFn c x = 0).card : Real) := by
    calc
      (∑ x : Vec F Idx, (if f x = g x then (1 : Real) else 0)) =
          ∑ x : Vec F Idx, (if linearFn a x = linearFn b x then (1 : Real) else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [ha x, hb x]
      _ = ∑ x : Vec F Idx, (if linearFn c x = 0 then (1 : Real) else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          have hiff : (linearFn a x = linearFn b x) ↔ linearFn c x = 0 := by
            rw [← sub_eq_zero]
            simp [c, linearFn, dotProduct, sub_mul, Finset.sum_sub_distrib]
          by_cases hx : linearFn a x = linearFn b x
          · simp [hx, hiff.mp hx]
          · have hcx : linearFn c x ≠ 0 := fun hcx => hx (hiff.mpr hcx)
            simp [hx, hcx]
      _ = ((Finset.univ.filter fun x : Vec F Idx => linearFn c x = 0).card : Real) := by
          simp
  have hN0 : (Fintype.card (Vec F Idx) : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hq0 : (Fintype.card F : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hfiber_mul_real :
      ((Finset.univ.filter fun x : Vec F Idx => linearFn c x = 0).card : Real) *
        (Fintype.card F : Real) = (Fintype.card (Vec F Idx) : Real) := by
    exact_mod_cast hfiber_mul
  have hfiber_ne :
      ((Finset.univ.filter fun x : Vec F Idx => linearFn c x = 0).card : Real) ≠ 0 := by
    intro hzero
    have hNzero : (Fintype.card (Vec F Idx) : Real) = 0 := by
      rw [← hfiber_mul_real, hzero, zero_mul]
    exact hN0 hNzero
  have hratio :
      (Fintype.card (Vec F Idx) : Real)⁻¹ *
          ((Finset.univ.filter fun x : Vec F Idx => linearFn c x = 0).card : Real) =
        (Fintype.card F : Real)⁻¹ := by
    rw [← hfiber_mul_real]
    field_simp [hfiber_ne, hq0]
  calc
    distance f g =
        (Fintype.card (Vec F Idx) : Real)⁻¹ *
          ∑ x : Vec F Idx, (if f x ≠ g x then (1 : Real) else 0) := by
          rfl
    _ = (Fintype.card (Vec F Idx) : Real)⁻¹ *
        ∑ x : Vec F Idx, (1 - (if f x = g x then (1 : Real) else 0)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : f x = g x <;> simp [hx]
    _ = 1 - (Fintype.card (Vec F Idx) : Real)⁻¹ *
        ∑ x : Vec F Idx, (if f x = g x then (1 : Real) else 0) := by
        simp [Finset.sum_sub_distrib, mul_sub]
    _ = 1 - (Fintype.card F : Real)⁻¹ := by
        rw [hagreement, hratio]

end ErrorCorrectionDiamater

end BlrPcp
