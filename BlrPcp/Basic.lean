import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.FieldTheory.Finite.Trace
import Architect

open scoped BigOperators

open scoped BigOperators

namespace BlrPcp

variable {F Idx : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Idx] [DecidableEq Idx]

abbrev Vec (F : Type*) (Idx : Type*) := Idx → F
abbrev ScalarFn (F : Type*) (Idx : Type*) := Vec F Idx → F
abbrev ComplexFn (F : Type*) (Idx : Type*) := Vec F Idx → Complex

def IsLinear (f : ScalarFn F Idx) : Prop :=
  ∃ a : Vec F Idx, ∀ x, f x = ∑ i, a i * x i

def LinearSet : Set (ScalarFn F Idx) := {f | IsLinear f}

def BLRAcceptsAt (f : ScalarFn F Idx) (a b : F) (x y : Vec F Idx) : Prop :=
  a * f x + b * f y = f (fun i => a * x i + b * y i)

axiom acceptanceProbabilityBLR : ScalarFn F Idx → Real

@[blueprint "def:ff-blr-reject-prob"
  (statement := /-- The rejection probability of the finite-field BLR test is
  \[
    \Pr[V_{BLR}^f = 0] = 1 - \Pr[V_{BLR}^f = 1].
  \] -/)]
noncomputable def rejectionProbabilityBLR (f : ScalarFn F Idx) : Real :=
  1 - acceptanceProbabilityBLR f

axiom distance : ScalarFn F Idx → ScalarFn F Idx → Real
axiom distanceToLinear : ScalarFn F Idx → Real

axiom phaseLift : ScalarFn F Idx → F → ComplexFn F Idx

/-- The standard bilinear pairing on `F^Idx`. -/
def dotProduct (a x : Vec F Idx) : F :=
  ∑ i, a i * x i

/-- Notation for the standard bilinear pairing on `F^Idx`. -/
scoped notation "⟪" a ", " x "⟫ᵥ" => dotProduct a x

/-- The uniform expectation of a complex-valued function on `F^Idx`. -/
noncomputable def expectation (f : ComplexFn F Idx) : Complex :=
  (Fintype.card (Vec F Idx) : Complex)⁻¹ * ∑ x, f x

/-- The expectation-based Hermitian inner product on complex-valued functions on `F^Idx`. -/
noncomputable def fnInner (f g : ComplexFn F Idx) : Complex :=
  expectation fun x => f x * star (g x)

/-- The squared `L²` norm associated to `fnInner`. -/
noncomputable def fnNormSq (f : ComplexFn F Idx) : Real :=
  (Fintype.card (Vec F Idx) : Real)⁻¹ * ∑ x, ‖f x‖ ^ 2

/-- The `L²` norm associated to the expectation inner product. -/
noncomputable def fnNorm (f : ComplexFn F Idx) : Real :=
  Real.sqrt (fnNormSq f)

/-- Notation for the expectation-based Hermitian inner product on `F^Idx → ℂ`. -/
scoped notation "⟪" f ", " g "⟫" => fnInner f g

/-- Notation for the expectation-based `L²` norm on `F^Idx → ℂ`. -/
scoped notation "‖" f "‖₂" => fnNorm f

/-- The additive character indexed by `α : F^Idx`, defined by
`χ_α(x) = ω_p^{Tr(∑ i, α i * x i)}` where `p = ringChar F`. -/
noncomputable def charFn (α : Vec F Idx) : ComplexFn F Idx := by
  classical
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  letI : NeZero (ringChar F) := ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  exact fun x =>
    ZMod.stdAddChar (N := ringChar F) (Algebra.trace (ZMod (ringChar F)) F ⟪α, x⟫ᵥ)

axiom fourierCoeff : ComplexFn F Idx → Vec F Idx → Complex


lemma characters_orthonormal_basis :
    (∀ α β : Vec F Idx, ⟪charFn α, charFn β⟫ = if α = β then 1 else 0) ∧
      Submodule.span ℂ (Set.range (charFn (F := F) (Idx := Idx))) = ⊤ := by
  sorry

lemma fourier_expansion (g : ComplexFn F Idx) : True := by
  sorry

lemma parseval_plancherel (g h : ComplexFn F Idx) : True := by
  sorry

def HasFourierSet (f : ScalarFn F Idx) : Prop := True

lemma distance_formula_via_fourier_sets (f g : ScalarFn F Idx) : True := by
  sorry


lemma distance_to_linearity_formula (f : ScalarFn F Idx) : True := by
  sorry

lemma spectral_lower_bound (f : ScalarFn F Idx) :
    distanceToLinear f ≤ rejectionProbabilityBLR f := by
  sorry

lemma improved_analysis_finite_fields (f : ScalarFn F Idx) :
    distanceToLinear f ≤ rejectionProbabilityBLR f := by
  exact spectral_lower_bound f

lemma almost_linear_of_high_acceptance (f : ScalarFn F Idx) {ε : Real}
    (h : 1 - ε ≤ acceptanceProbabilityBLR f) :
    distanceToLinear f ≤ ε := by
  have hmain : distanceToLinear f ≤ rejectionProbabilityBLR f :=
    improved_analysis_finite_fields f
  dsimp [rejectionProbabilityBLR] at hmain
  linarith

lemma boolean_special_case : True := by
  sorry

end BlrPcp
