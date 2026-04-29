import BlrPcp.Basic
-- TODO: move the following definitions to Basic.lean

/-- The linear scalar function `ℓ_a(x) = a ⬝ᵥ x`. -/
def linearFn {F : Type} [Field F] {n : ℕ} (a : (Fin n → F)) :
    (Fin n → F) → F :=
  fun x => a ⬝ᵥ x

/-- The relative Hamming distance between `f` and the linear function `linearFn a`. -/
noncomputable def distanceToLinearFn {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (f : (Fin n → F) → F) (a : Fin n → F) : ENNReal :=
  (Fintype.card (Fin n → F) : ENNReal)⁻¹ *
    ((Finset.univ.filter fun x => f x ≠ linearFn a x).card : ENNReal)

/-- The distance from `f` to the closest linear function. -/
noncomputable def distanceToLin {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (f : (Fin n → F) → F) : ENNReal :=
  (Finset.univ : Finset (Fin n → F)).inf' ⟨0, by simp⟩ fun a => distanceToLinearFn f a

/-- The pointwise acceptance predicate for the additive BLR test. -/
def BLRAcceptsAt {F : Type} [Add F] {n : ℕ}
    (f : (Fin n → F) → F) (x y : Fin n → F) : Prop :=
  f x + f y = f (x + y)

/-- The uniform acceptance probability of the additive BLR test over `F^n`. -/
noncomputable def acceptanceProbabilityBLR {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (f : (Fin n → F) → F) : ENNReal := by
  classical
  exact ((Finset.univ.filter fun xy : (Fin n → F) × (Fin n → F) =>
      BLRAcceptsAt f xy.1 xy.2).card : ENNReal) *
    (Fintype.card ((Fin n → F) × (Fin n → F)) : ENNReal)⁻¹

noncomputable def rejectionProbabilityBLR {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (f : (Fin n → F) → F) : ENNReal :=
  1 - acceptanceProbabilityBLR f

theorem blrSoundnessAnalytical {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (f : (Fin n → F) → F) : rejectionProbabilityBLR f ≥ distanceToLin f := by
  sorry
