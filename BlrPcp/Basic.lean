import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
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

noncomputable def rejectionProbabilityBLR (f : ScalarFn F Idx) : Real :=
  1 - acceptanceProbabilityBLR f

axiom distance : ScalarFn F Idx → ScalarFn F Idx → Real
axiom distanceToLinear : ScalarFn F Idx → Real

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

/-- The `c`-phase of `f : F^Idx → F`, defined by
`f_c(x) = ω_p^{Tr(c * f(x))}` where `p = ringChar F`. -/
noncomputable def phaseLift (f : ScalarFn F Idx) (c : F) : ComplexFn F Idx := by
  classical
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  letI : NeZero (ringChar F) := ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  exact fun x =>
    ZMod.stdAddChar (N := ringChar F) (Algebra.trace (ZMod (ringChar F)) F (c * f x))

/-- The Fourier coefficient `\hat f(\alpha)` is the expectation inner product
of `f` with the character `χ_α`. -/
noncomputable def fourierCoeff (f : ComplexFn F Idx) (α : Vec F Idx) : Complex :=
  ⟪f, charFn α⟫

/-- Postfix notation for the Fourier transform `f ↦ \hat f`. -/
scoped postfix:max "̂" => fourierCoeff

/-- Application notation for Fourier coefficients, allowing `f̂(α)`. -/
scoped notation:max f:max "̂(" α:max ")" => fourierCoeff f α

/-- Identifier-style notation for the `c`-phase, allowing terms such as `f_c`. -/
scoped macro_rules
  | `($id:ident) =>
      let parts := id.getId.toString.splitOn "_"
      match parts with
      | [f, c] =>
          if c.length = 1 then
            `(phaseLift $(Lean.mkIdent <| Lean.Name.mkSimple f)
              $(Lean.mkIdent <| Lean.Name.mkSimple c))
          else
            Lean.Macro.throwUnsupported
      | _ => Lean.Macro.throwUnsupported


private lemma dotProduct_single (a : Vec F Idx) (i : Idx) (t : F) :
    dotProduct a (Pi.single i t) = a i * t := by
  classical
  rw [dotProduct, Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    simp [Pi.single_eq_of_ne hij]
  · intro hi
    simp at hi

private lemma dotProduct_sub_left (a b x : Vec F Idx) :
    dotProduct (a - b) x = dotProduct a x - dotProduct b x := by
  simp [dotProduct, sub_mul, Finset.sum_sub_distrib]

private noncomputable def dotProductAddMonoidHom (a : Vec F Idx) : Vec F Idx →+ F where
  toFun := dotProduct a
  map_zero' := by simp [dotProduct]
  map_add' x y := by
    simp [dotProduct, mul_add, Finset.sum_add_distrib]

private noncomputable def baseChar : AddChar F ℂ := by
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  letI : NeZero (ringChar F) := ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  exact (ZMod.stdAddChar (N := ringChar F)).compAddMonoidHom
    (Algebra.trace (ZMod (ringChar F)) F).toAddMonoidHom

private noncomputable def charAddChar (a : Vec F Idx) : AddChar (Vec F Idx) ℂ :=
  (baseChar (F := F)).compAddMonoidHom (dotProductAddMonoidHom (F := F) (Idx := Idx) a)

@[simp] private lemma charAddChar_apply (a x : Vec F Idx) :
    charAddChar (F := F) (Idx := Idx) a x = charFn a x := rfl

private lemma charAddChar_injective :
    Function.Injective (charAddChar (F := F) (Idx := Idx)) := by
  classical
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  letI : NeZero (ringChar F) := ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  intro a b hab
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨i, hi⟩ : ∃ i, (a - b) i ≠ 0 := by
    by_contra h
    apply hsub
    ext j
    by_contra hj
    exact h ⟨j, hj⟩
  obtain ⟨t, ht⟩ := FiniteField.trace_to_zmod_nondegenerate F (a := (a - b) i) hi
  let x : Vec F Idx := Pi.single i t
  have hEval : charFn a x = charFn b x := by
    simpa using congr_fun (congrArg DFunLike.coe hab) x
  have hTraceEq :
      Algebra.trace (ZMod (ringChar F)) F (dotProduct a x) =
        Algebra.trace (ZMod (ringChar F)) F (dotProduct b x) := by
    exact ZMod.injective_stdAddChar (N := ringChar F) hEval
  have hTraceSub :
      Algebra.trace (ZMod (ringChar F)) F (dotProduct (a - b) x) = 0 := by
    have : Algebra.trace (ZMod (ringChar F)) F (dotProduct a x - dotProduct b x) = 0 := by
      simpa [LinearMap.map_sub] using sub_eq_zero.mpr hTraceEq
    simpa [dotProduct_sub_left] using this
  have : Algebra.trace (ZMod (ringChar F)) F ((a - b) i * t) = 0 := by
    simpa [x, dotProduct_single] using hTraceSub
  exact ht this


lemma characters_orthonormal_basis :
    (∀ α β : Vec F Idx, ⟪charFn α, charFn β⟫ = if α = β then 1 else 0) ∧
      Submodule.span ℂ (Set.range (charFn (F := F) (Idx := Idx))) = ⊤ := by
  classical
  have horth : ∀ α β : Vec F Idx, ⟪charFn α, charFn β⟫ = if α = β then 1 else 0 := by
    intro α β
    simpa [fnInner, expectation, RCLike.wInner_cWeight_eq_expect, Fintype.expect_eq_sum_div_card,
      div_eq_mul_inv, RCLike.inner_apply, charAddChar_injective.eq_iff, eq_comm, mul_comm,
      mul_left_comm, mul_assoc] using
      (AddChar.wInner_cWeight_eq_boole (ψ₁ := charAddChar (F := F) (Idx := Idx) β)
        (ψ₂ := charAddChar (F := F) (Idx := Idx) α)).symm
  have hbij : Function.Bijective (charAddChar (F := F) (Idx := Idx)) := by
    refine (Fintype.bijective_iff_injective_and_card
      (charAddChar (F := F) (Idx := Idx))).2 ?_
    exact ⟨charAddChar_injective (F := F) (Idx := Idx),
      (AddChar.card_eq (α := Vec F Idx)).symm⟩
  have hrange :
      Set.range (charFn (F := F) (Idx := Idx)) =
        Set.range (((↑) : AddChar (Vec F Idx) ℂ → Vec F Idx → ℂ)) := by
    ext f
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨charAddChar (F := F) (Idx := Idx) a, rfl⟩
    · rintro ⟨ψ, rfl⟩
      rcases hbij.surjective ψ with ⟨a, rfl⟩
      exact ⟨a, rfl⟩
  have hspan :
      Submodule.span ℂ (Set.range (((↑) : AddChar (Vec F Idx) ℂ → Vec F Idx → ℂ))) = ⊤ := by
    simpa [AddChar.coe_complexBasis (α := Vec F Idx)] using
      (AddChar.complexBasis (α := Vec F Idx)).span_eq
  exact ⟨horth, hrange ▸ hspan⟩

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
