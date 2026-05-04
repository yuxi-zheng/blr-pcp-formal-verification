import BlrPcp.Basic

/-!
# Bridges from the analytical BLR theorem to oracle probabilities

The analytical development in `Basic.lean` uses real-valued probabilities.  The
oracle-computation side uses `ENNReal`, so this file keeps the conversion in one
place.
-/

/-- The `ENNReal` version of the analytical distance from `f` to linearity. -/
noncomputable def distanceToLin {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    [Nonempty (Fin n)] (f : (Fin n → F) → F) : ENNReal :=
  ENNReal.ofReal (BlrPcp.distanceToLinear (F := F) (Idx := Fin n) f)

/-- The `ENNReal` version of the analytical finite-field BLR acceptance probability. -/
noncomputable def acceptanceProbabilityBLR {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} [Nonempty (Fin n)] (f : (Fin n → F) → F) : ENNReal :=
  ENNReal.ofReal (BlrPcp.acceptanceProbabilityBLR (F := F) (Idx := Fin n) f)

/-- The `ENNReal` rejection probability corresponding to the analytical finite-field BLR test. -/
noncomputable def rejectionProbabilityBLR {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} [Nonempty (Fin n)] (f : (Fin n → F) → F) : ENNReal :=
  1 - acceptanceProbabilityBLR f

/-- The analytical finite-field BLR soundness theorem, converted to `ENNReal`. -/
theorem blrSoundnessAnalytical {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    [Nonempty (Fin n)] (f : (Fin n → F) → F) :
    distanceToLin f ≤ rejectionProbabilityBLR f := by
  classical
  have hAcceptNonneg :
      0 ≤ BlrPcp.acceptanceProbabilityBLR (F := F) (Idx := Fin n) f := by
    unfold BlrPcp.acceptanceProbabilityBLR
    positivity
  have hReal :
      BlrPcp.distanceToLinear (F := F) (Idx := Fin n) f ≤
        1 - BlrPcp.acceptanceProbabilityBLR (F := F) (Idx := Fin n) f := by
    have hSound := BlrPcp.finite_field_blr_soundness (F := F) (Idx := Fin n) f
    nlinarith
  rw [distanceToLin, rejectionProbabilityBLR, acceptanceProbabilityBLR]
  rw [← ENNReal.ofReal_one]
  rw [← ENNReal.ofReal_sub (1 : ℝ) hAcceptNonneg]
  exact ENNReal.ofReal_le_ofReal hReal
