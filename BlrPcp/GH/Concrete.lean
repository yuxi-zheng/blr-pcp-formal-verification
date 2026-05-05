/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
import BlrPcp.GH3

import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Concrete finite-dimensional corollary of the abstract Gowers-Hatami theorem

This file converts the abstract finite-coordinate witness from `BlrPcp.GH3`
into the traditional `Fin d'` formulation.

The only mathematical work here is bookkeeping: an abstract finite index type
`ι` is reindexed to `Fin (Fintype.card ι)` using Mathlib's finite-type
bijections, and matrices/unitary representations are transported along this
bijection.  The main Gowers-Hatami proof remains in `BlrPcp.GH3`.
-/
open scoped Matrix ComplexConjugate ComplexOrder
open BigOperators Finset

universe u

variable {d : Nat}
variable (G : Type u) [Group G] [Fintype G]

namespace GH3

noncomputable section
/-! ## Reindexing an abstract witness to a numeric dimension -/

/-- Reindexing a unitary matrix along an equivalence gives a unitary matrix. -/
def reindexUnitary
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (U : Matrix.unitaryGroup ι Complex) :
    Matrix.unitaryGroup κ Complex where
  val := Matrix.reindex e e (U : Matrix ι ι Complex)
  property := by
    rw [Matrix.mem_unitaryGroup_iff]
    have hU : (U : Matrix ι ι Complex) * (U : Matrix ι ι Complex)ᴴ = 1 :=
      Matrix.mem_unitaryGroup_iff.mp U.property
    calc
      Matrix.reindex e e (U : Matrix ι ι Complex) *
          (Matrix.reindex e e (U : Matrix ι ι Complex))ᴴ
          = Matrix.reindex e e
              ((U : Matrix ι ι Complex) * (U : Matrix ι ι Complex)ᴴ) := by
              rw [Matrix.conjTranspose_reindex]
              exact Matrix.reindexLinearEquiv_mul Complex Complex e e e
                (U : Matrix ι ι Complex) ((U : Matrix ι ι Complex)ᴴ)
      _ = 1 := by simp [hU]

@[simp]
theorem reindexUnitary_coe
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (U : Matrix.unitaryGroup ι Complex) :
    (reindexUnitary e U : Matrix κ κ Complex) =
      Matrix.reindex e e (U : Matrix ι ι Complex) :=
  rfl

/-- Reindexing is a multiplicative equivalence on unitary groups. -/
def reindexUnitaryEquiv
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) :
    Matrix.unitaryGroup ι Complex ≃* Matrix.unitaryGroup κ Complex where
  toFun := reindexUnitary e
  invFun := reindexUnitary e.symm
  left_inv U := by
    apply Subtype.ext
    ext i j
    simp [reindexUnitary]
  right_inv U := by
    apply Subtype.ext
    ext i j
    simp [reindexUnitary]
  map_mul' U V := by
    apply Subtype.ext
    change Matrix.reindex e e
        ((U : Matrix ι ι Complex) * (V : Matrix ι ι Complex)) =
      Matrix.reindex e e (U : Matrix ι ι Complex) *
        Matrix.reindex e e (V : Matrix ι ι Complex)
    exact (Matrix.reindexLinearEquiv_mul Complex Complex e e e
      (U : Matrix ι ι Complex) (V : Matrix ι ι Complex)).symm

/-- Reindex a unitary representation along an equivalence of index types. -/
def reindexUnitaryRep
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ)
    (rho0 : G →* Matrix.unitaryGroup ι Complex) :
    G →* Matrix.unitaryGroup κ Complex :=
  (reindexUnitaryEquiv e).toMonoidHom.comp rho0

omit [Fintype G] in
@[simp]
theorem reindexUnitaryRep_apply
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (rho0 : G →* Matrix.unitaryGroup ι Complex) (x : G) :
    (reindexUnitaryRep G e rho0 x : Matrix κ κ Complex) =
      Matrix.reindex e e (rho0 x : Matrix ι ι Complex) := by
  simp [reindexUnitaryRep, reindexUnitaryEquiv, reindexUnitary]

/-- Reindexing the enlarged space preserves compressed operators. -/
@[simp]
theorem reindex_compression
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ)
    (V : Matrix (Fin d) ι Complex)
    (R : Matrix ι ι Complex) :
    Matrix.reindex (Equiv.refl (Fin d)) e V *
      Matrix.reindex e e R *
      (Matrix.reindex (Equiv.refl (Fin d)) e V)ᴴ =
        V * R * Vᴴ := by
  have hVR :
      Matrix.reindex (Equiv.refl (Fin d)) e V * Matrix.reindex e e R =
        Matrix.reindex (Equiv.refl (Fin d)) e (V * R) :=
    Matrix.reindexLinearEquiv_mul Complex Complex (Equiv.refl (Fin d)) e e V R
  have hVRV :
      Matrix.reindex (Equiv.refl (Fin d)) e (V * R) *
          Matrix.reindex e (Equiv.refl (Fin d)) Vᴴ =
        Matrix.reindex (Equiv.refl (Fin d)) (Equiv.refl (Fin d)) ((V * R) * Vᴴ) :=
    Matrix.reindexLinearEquiv_mul Complex Complex (Equiv.refl (Fin d)) e
      (Equiv.refl (Fin d)) (V * R) Vᴴ
  calc
    Matrix.reindex (Equiv.refl (Fin d)) e V * Matrix.reindex e e R *
        (Matrix.reindex (Equiv.refl (Fin d)) e V)ᴴ
        = Matrix.reindex (Equiv.refl (Fin d)) e (V * R) *
            Matrix.reindex e (Equiv.refl (Fin d)) Vᴴ := by
              rw [Matrix.conjTranspose_reindex, hVR]
    _ = Matrix.reindex (Equiv.refl (Fin d)) (Equiv.refl (Fin d)) ((V * R) * Vᴴ) :=
          hVRV
    _ = V * R * Vᴴ := by simp [Matrix.mul_assoc]

/-- Reindexing the enlarged space preserves the isometry equation. -/
theorem reindex_isometry
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ)
    (V : Matrix (Fin d) ι Complex)
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

omit [Fintype G] in
/-- Reindexing the middle space in a represented compression preserves the compression. -/
theorem reindexUnitaryRep_compression
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ)
    (V : Matrix (Fin d) ι Complex)
    (rho0 : G →* Matrix.unitaryGroup ι Complex)
    (x : G) :
    Matrix.reindex (Equiv.refl (Fin d)) e V *
      (reindexUnitaryRep G e rho0 x : Matrix κ κ Complex) *
      (Matrix.reindex (Equiv.refl (Fin d)) e V)ᴴ =
        V * (rho0 x : Matrix ι ι Complex) * Vᴴ := by
  rw [reindexUnitaryRep_apply]
  exact reindex_compression e V (rho0 x : Matrix ι ι Complex)

/-- An isometry adjoint `V : Fin d → ι` forces `d ≤ Fintype.card ι`. -/
theorem le_card_of_isometry
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix (Fin d) ι Complex)
    (hV : V * Vᴴ = 1) :
    d ≤ Fintype.card ι := by
  have hrank : V.rank = d := by
    calc
      V.rank = (V * Vᴴ).rank := (Matrix.rank_self_mul_conjTranspose V).symm
      _ = (1 : Matrix (Fin d) (Fin d) Complex).rank := by rw [hV]
      _ = d := by simp
  exact hrank ▸ Matrix.rank_le_card_width V

/-- Transport a Gowers-Hatami witness along an equivalence of enlarged index types. -/
theorem witness_reindex
    {ι : Type u} [Fintype ι] [DecidableEq ι] {d' : Nat}
    (e : ι ≃ Fin d')
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (eps : Real)
    (V : Matrix (Fin d) ι Complex)
    (hV : V * Vᴴ = 1)
    (rho0 : G →* Matrix.unitaryGroup ι Complex)
    (hprox :
      (∑ x : G,
        sigmaNormSq sigma
          (rho x - V * (rho0 x : Matrix ι ι Complex) * Vᴴ)) /
        Fintype.card G ≤ 2 * eps) :
    ∃ (d' : Nat) (_ : d ≤ d')
      (V' : Matrix (Fin d) (Fin d') Complex)
      (_hV' : V' * V'ᴴ = 1)
      (rho0' : G →* Matrix.unitaryGroup (Fin d') Complex),
      (∑ x : G,
        sigmaNormSq sigma
          (rho x - V' * (rho0' x : Matrix (Fin d') (Fin d') Complex) * V'ᴴ)) /
        Fintype.card G ≤ 2 * eps := by
  let V' := Matrix.reindex (Equiv.refl (Fin d)) e V
  let rho0' := reindexUnitaryRep G e rho0
  have hd_le : d ≤ d' := by
    have hcard : Fintype.card ι = d' := by
      simpa using Fintype.card_congr e
    simpa [hcard] using le_card_of_isometry V hV
  refine ⟨d', hd_le, V', reindex_isometry e V hV, rho0', ?_⟩
  have hsum :
      (∑ x : G,
        sigmaNormSq sigma
          (rho x - V' * (rho0' x : Matrix (Fin d') (Fin d') Complex) * V'ᴴ)) =
        ∑ x : G,
          sigmaNormSq sigma
            (rho x - V * (rho0 x : Matrix ι ι Complex) * Vᴴ) := by
    apply Finset.sum_congr rfl
    intro x _hx
    simp only [V', rho0']
    rw [reindexUnitaryRep_compression]
  rw [hsum]
  exact hprox

/--
Gowers-Hatami in the dimensional format used by `GowersHatami.gowers_hatami`.

This is just the abstract finite-coordinate theorem followed by a single
Mathlib reindexing step from the witness index type to `Fin d'`.
-/
theorem gowers_hatami [DecidableEq G]
    (sigma : Matrix (Fin d) (Fin d) Complex)
    (hsigma : Matrix.PosSemidef sigma) (hsigmatr : Matrix.trace sigma = 1)
    (rho : G → Matrix (Fin d) (Fin d) Complex)
    (eps : Real) (heps : 0 ≤ eps)
    (hrho : ∀ x, rho x ∈ Matrix.unitaryGroup (Fin d) Complex)
    (hApprox : IsApproxRepresentation G sigma rho eps) :
    ∃ (d' : Nat) (_ : d ≤ d')
      (V : Matrix (Fin d) (Fin d') Complex)
      (_hV : V * Vᴴ = 1)
      (rho0 : G →* Matrix.unitaryGroup (Fin d') Complex),
      (∑ x : G,
        sigmaNormSq sigma
          (rho x - V * (rho0 x : Matrix (Fin d') (Fin d') Complex) * Vᴴ)) /
        Fintype.card G ≤ 2 * eps := by
  classical
  obtain ⟨ι, hι, hιdec, V, hV, rho0, hprox⟩ :=
    gowers_hatami_abstract G sigma hsigma hsigmatr rho eps heps hrho hApprox
  letI : Fintype ι := hι
  letI : DecidableEq ι := hιdec
  exact witness_reindex G (Fintype.equivFin ι) sigma rho eps V hV rho0 hprox


end

end GH3
