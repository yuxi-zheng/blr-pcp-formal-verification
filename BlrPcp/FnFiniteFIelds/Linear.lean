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
