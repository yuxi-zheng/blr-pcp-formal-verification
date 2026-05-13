import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Basis.SMul
import Architect

open scoped BigOperators

namespace BlrPcp

/- `F` is the finite field we work with,
`Idx` is the finite non-empty set of coordinates of the vector space `F^Idx`.
We assume equality is decidable over both `F` and `Idx` -/

variable {F Idx : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]

/-- Vectors in the finite-dimensional space `F^Idx`. -/
abbrev Vec (F : Type*) (Idx : Type*) := Idx → F

/-- Scalar-valued functions on `F^Idx`. -/
abbrev ScalarFn (F : Type*) (Idx : Type*) := Vec F Idx → F

/-- Complex-valued functions on `F^Idx`. -/
abbrev ComplexFn (F : Type*) (Idx : Type*) := Vec F Idx → Complex

/-- The nonzero elements of the finite field `F`. -/
def nonzeroF : Finset F := Finset.univ.filter fun a => a ≠ 0

/-- The standard dot product between vectors in `F^Idx`. -/
def dotProduct (x y : Vec F Idx) : F :=
  ∑ i, x i * y i

/-- Notation for dot product in `F^Idx`. -/
scoped notation "⟪" a ", " x "⟫ᵥ" => dotProduct a x

omit [Fintype F] [DecidableEq F] [DecidableEq Idx] [Nonempty Idx] in
/-- The dot product on `F^Idx` is symmetric. -/
lemma dotProduct_comm (x y : Vec F Idx) :
    ⟪x, y⟫ᵥ = ⟪y, x⟫ᵥ := by
  simp [dotProduct, mul_comm]

omit [Fintype F] [DecidableEq F] [DecidableEq Idx] [Nonempty Idx] in
/-- The dot product is linear in its first argument. -/
lemma dotProduct_linearity (lambda mu : F) (a b x : Vec F Idx) :
    ⟪lambda • a + mu • b, x⟫ᵥ =
      lambda * ⟪a, x⟫ᵥ + mu * ⟪b, x⟫ᵥ := by
  calc
    ⟪lambda • a + mu • b, x⟫ᵥ =
        ∑ i, (lambda * (a i * x i) + mu * (b i * x i)) := by
          simp [dotProduct, add_mul, mul_assoc]
    _ = (∑ i, lambda * (a i * x i)) + ∑ i, mu * (b i * x i) := by
          rw [Finset.sum_add_distrib]
    _ = lambda * ⟪a, x⟫ᵥ + mu * ⟪b, x⟫ᵥ := by
          rw [dotProduct, dotProduct, Finset.mul_sum, Finset.mul_sum]

/-- The relative Hamming distance between two functions `F^Idx → F`, i.e. the
uniform probability that they disagree on a point of `F^Idx`. -/
noncomputable def distance (f g : ScalarFn F Idx) : Real :=
  (Fintype.card (Vec F Idx) : Real)⁻¹ *
    ∑ x : Vec F Idx, if f x ≠ g x then (1 : Real) else 0

/-- The uniform expectation of a complex-valued function on `F^Idx`. -/
noncomputable def expectation (f : ComplexFn F Idx) : Complex :=
  (Fintype.card (Vec F Idx) : Real)⁻¹ * ∑ x, f x

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

/-- The base additive character of the finite field `F`, built from the trace to
the prime field followed by the standard character of `ZMod (ringChar F)`. -/
noncomputable def baseChar : AddChar F ℂ := by
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  letI : NeZero (ringChar F) := ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  exact (ZMod.stdAddChar (N := ringChar F)).compAddMonoidHom
    (Algebra.trace (ZMod (ringChar F)) F).toAddMonoidHom

/-- The additive character indexed by `α : F^Idx`,
defined as `χ_α(x) = ω_p^{Tr(∑ i, α i * x i)}`, where:
- `p = ringChar F` is the characteristic of `F`
- `ω_p` is `exp(2 π i / p)`
- `Tr: F_q → F_p` is the field trace -/
noncomputable def charFn (α : Vec F Idx) : ComplexFn F Idx :=
  fun x => baseChar (F := F) ⟪α, x⟫ᵥ

/-- The `c`-phase of `f : F^Idx → F`, defined by
`f_c(x) = ω_p^{Tr(c * f(x))}` where `p = ringChar F` is the characteristic of `F`. -/
noncomputable def phaseLift (f : ScalarFn F Idx) (c : F) : ComplexFn F Idx :=
  fun x => baseChar (F := F) (c * f x)

/-- The Fourier coefficient `\hat f(\alpha)` is the expectation inner product
of `f` with the character `χ_α`. -/
noncomputable def fourierCoeff (f : ComplexFn F Idx) (α : Vec F Idx) : Complex :=
  ⟪f, charFn α⟫

section CharacterBasis

omit [Fintype F] [DecidableEq F] [Nonempty Idx] in
/-- Dot product against a vector supported only at coordinate `i`.
This extracts the `i`-th coordinate of the left vector and multiplies it by
the value `t` at that coordinate. -/
lemma dotProduct_single (a : Vec F Idx) (i : Idx) (t : F) :
    ⟪a, Pi.single i t⟫ᵥ = a i * t := by
  classical
  rw [dotProduct, Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    simp [Pi.single_eq_of_ne hij]
  · intro hi
    simp at hi

/-- The map `x ↦ ⟪a, x⟫ᵥ` as an additive monoid homomorphism. -/
private noncomputable def dotProductAddMonoidHom (a : Vec F Idx) : Vec F Idx →+ F where
  toFun := dotProduct a
  map_zero' := by simp [dotProduct]
  map_add' x y := by
    simp [dotProduct, mul_add, Finset.sum_add_distrib]

/-- The character of the additive group of `F^Idx` induced by dot product with `a`. -/
private noncomputable def charAddChar (a : Vec F Idx) : AddChar (Vec F Idx) ℂ :=
  (baseChar (F := F)).compAddMonoidHom (dotProductAddMonoidHom (F := F) (Idx := Idx) a)

omit [DecidableEq F] [DecidableEq Idx] [Nonempty Idx] in
/-- Evaluating the additive character induced by `a` agrees with `charFn a`. -/
@[simp] private lemma charAddChar_apply (a x : Vec F Idx) :
    charAddChar (F := F) (Idx := Idx) a x = charFn a x := rfl

omit [Nonempty Idx] in
/-- Distinct vectors induce distinct additive characters on `F^Idx`. -/
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
    have hdot : ⟪a - b, x⟫ᵥ = ⟪a, x⟫ᵥ - ⟪b, x⟫ᵥ := by
      simpa [sub_eq_add_neg] using
        (dotProduct_linearity (F := F) (Idx := Idx) (1 : F) (-1 : F) a b x)
    simpa [hdot] using this
  have : Algebra.trace (ZMod (ringChar F)) F ((a - b) i * t) = 0 := by
    simpa [x, dotProduct_single] using hTraceSub
  exact ht this

omit [Nonempty Idx] in
/-- The Fourier characters `χ_α` form an orthonormal basis of all complex-valued
functions on `F^Idx`: distinct characters have zero inner product, each
character has unit norm, and their span is the whole function space. -/
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

end CharacterBasis

section HilbertSpaceTranslation

omit [DecidableEq F] [Nonempty Idx] in
/-- The finite vector space `F^Idx` has positive cardinality. -/
lemma card_vec_pos : 0 < Fintype.card (Vec F Idx) := Fintype.card_pos

omit [Field F] [DecidableEq F] [Nonempty Idx] in
/-- The expectation-normalized squared norm is the `PiLp` norm squared divided
by the number of points of `F^Idx`. -/
private lemma fnNormSq_eq_card_inv_mul_norm_sq (g : ComplexFn F Idx) :
    fnNormSq g = (Fintype.card (Vec F Idx) : ℝ)⁻¹ * ‖WithLp.toLp 2 g‖ ^ 2 := by
  simp [fnNormSq, PiLp.norm_sq_eq_of_L2]

omit [DecidableEq F] [Nonempty Idx] in
/-- The square root of `|F^Idx|`, viewed in `ℂ`, is nonzero. -/
private lemma sqrt_card_ne_zero :
    (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 card_vec_pos))

omit [DecidableEq F] [Nonempty Idx] in
/-- Multiplying `|F^Idx|` by the inverse of its square root gives the square root. -/
private lemma sqrt_card_mul_inv_sqrt_card :
    (((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)⁻¹) *
      (Fintype.card (Vec F Idx) : ℂ)) =
        (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) := by
  field_simp [sqrt_card_ne_zero (F := F) (Idx := Idx)]
  exact_mod_cast (Real.sq_sqrt (Nat.cast_nonneg (Fintype.card (Vec F Idx)) : (0 : ℝ) ≤ _)).symm

omit [Field F] [DecidableEq F] [Nonempty Idx] in
/-- The square of the square root of `|F^Idx|`, viewed in `ℂ`, is `|F^Idx|`. -/
private lemma sqrt_card_mul_sqrt_card :
    (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) *
      (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) =
        (Fintype.card (Vec F Idx) : ℂ) := by
  rw [← Complex.ofReal_mul, ← sq]
  exact_mod_cast (Real.sq_sqrt
    (Nat.cast_nonneg (Fintype.card (Vec F Idx)) : (0 : ℝ) ≤ _))

omit [DecidableEq F] [Nonempty Idx] in
/-- The normalization factor for characters has squared norm `1 / |F^Idx|`. -/
private lemma inv_sqrt_card_sq_mul_card :
    (((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)⁻¹) *
      (((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)⁻¹) * (Fintype.card (Vec F Idx) : ℂ))) = 1 := by
  field_simp [sqrt_card_ne_zero (F := F) (Idx := Idx)]
  exact_mod_cast (Real.sq_sqrt (Nat.cast_nonneg (Fintype.card (Vec F Idx)) : (0 : ℝ) ≤ _)).symm

omit [DecidableEq F] in
/-- The unnormalized `PiLp` inner product is `|F^Idx|` times the expectation inner product. -/
private lemma toLp_inner_eq_card_mul_fnInner (f g : ComplexFn F Idx) :
    inner ℂ (WithLp.toLp 2 g) (WithLp.toLp 2 f) =
      (Fintype.card (Vec F Idx) : ℂ) * fnInner f g := by
  rw [← RCLike.wInner_one_eq_inner g f]
  simp [RCLike.wInner, fnInner, expectation, RCLike.inner_apply]

/-- The `PiLp` version of `χ_α`, scaled to have norm one. -/
noncomputable def normalizedCharLp (α : Vec F Idx) : PiLp 2 fun _ : Vec F Idx => ℂ :=
  ((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)⁻¹) • WithLp.toLp 2 (charFn α)

/-- The normalized Fourier characters form an orthonormal family in `PiLp`. -/
lemma normalizedCharLp_orthonormal :
    Orthonormal ℂ (normalizedCharLp (F := F) (Idx := Idx)) := by
  classical
  rw [orthonormal_iff_ite]
  intro α β
  rw [normalizedCharLp, normalizedCharLp, inner_smul_left, inner_smul_right,
    toLp_inner_eq_card_mul_fnInner]
  by_cases h : α = β
  · subst h
    have horthα : fnInner (charFn α) (charFn α) = (1 : ℂ) := by
      simpa using (characters_orthonormal_basis (F := F) (Idx := Idx)).1 α α
    simp [horthα]
    simpa using (inv_sqrt_card_sq_mul_card (F := F) (Idx := Idx))
  · have horth := (characters_orthonormal_basis (F := F) (Idx := Idx)).1 β α
    have h' : β ≠ α := by simpa [eq_comm] using h
    simp [horth, h, h']

omit [DecidableEq F] in
/-- Inner product against a normalized character equals the Fourier inner product
scaled by `sqrt |F^Idx|`. -/
lemma normalizedCharLp_inner_eq_sqrt_card_mul_fnInner (g : ComplexFn F Idx)
    (α : Vec F Idx) :
    inner ℂ (normalizedCharLp (F := F) (Idx := Idx) α) (WithLp.toLp 2 g) =
      (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) * fnInner g (charFn α) := by
  have hstarinv : (starRingEnd ℂ) ((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)⁻¹) =
      ((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)⁻¹) := by simp
  rw [normalizedCharLp, inner_smul_left,
    toLp_inner_eq_card_mul_fnInner (f := g) (g := charFn α), hstarinv]
  calc
    ((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)⁻¹) *
        ((Fintype.card (Vec F Idx) : ℂ) * fnInner g (charFn α)) =
      ((((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)⁻¹) * (Fintype.card (Vec F Idx) : ℂ)) *
        fnInner g (charFn α)) := by ring
    _ = (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) * fnInner g (charFn α) := by
      rw [sqrt_card_mul_inv_sqrt_card]

omit [DecidableEq F] in
/-- The conjugate-oriented version of `normalizedCharLp_inner_eq_sqrt_card_mul_fnInner`. -/
private lemma toLp_inner_normalizedCharLp_eq_sqrt_card_mul_star_fnInner (g : ComplexFn F Idx)
    (α : Vec F Idx) :
    inner ℂ (WithLp.toLp 2 g) (normalizedCharLp (F := F) (Idx := Idx) α) =
      (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) * star (fnInner g (charFn α)) := by
  calc
    inner ℂ (WithLp.toLp 2 g) (normalizedCharLp (F := F) (Idx := Idx) α) =
        star (inner ℂ (normalizedCharLp (F := F) (Idx := Idx) α) (WithLp.toLp 2 g)) := by
          exact (inner_conj_symm (WithLp.toLp 2 g)
            (normalizedCharLp (F := F) (Idx := Idx) α)).symm
    _ = star ((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) * fnInner g (charFn α)) := by
          rw [normalizedCharLp_inner_eq_sqrt_card_mul_fnInner]
    _ = (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) * star (fnInner g (charFn α)) := by
          simp

omit [DecidableEq F] in
/-- The squared norm of a normalized-character coefficient is `|F^Idx|` times
the squared norm of the corresponding expectation inner product. -/
private lemma norm_sq_normalizedCharLp_inner (g : ComplexFn F Idx) (α : Vec F Idx) :
    ‖inner ℂ (normalizedCharLp (F := F) (Idx := Idx) α) (WithLp.toLp 2 g)‖ ^ 2 =
      (Fintype.card (Vec F Idx) : ℝ) * ‖fnInner g (charFn α)‖ ^ 2 := by
  rw [normalizedCharLp_inner_eq_sqrt_card_mul_fnInner, norm_mul]
  simp only [Complex.norm_real]
  calc
    (|√(Fintype.card (Vec F Idx) : ℝ)| * ‖fnInner g (charFn α)‖) ^ 2 =
        |√(Fintype.card (Vec F Idx) : ℝ)| ^ 2 * ‖fnInner g (charFn α)‖ ^ 2 := by ring
    _ = (√(Fintype.card (Vec F Idx) : ℝ)) ^ 2 * ‖fnInner g (charFn α)‖ ^ 2 := by
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    _ = (Fintype.card (Vec F Idx) : ℝ) * ‖fnInner g (charFn α)‖ ^ 2 := by
        rw [Real.sq_sqrt (Nat.cast_nonneg _)]

omit [Nonempty Idx] in
/-- Transporting the character basis into `PiLp` still spans all functions. -/
private lemma toLp_charFn_span_top :
    Submodule.span ℂ (Set.range fun α : Vec F Idx => WithLp.toLp 2 (charFn α)) = ⊤ := by
  let e : WithLp 2 (ComplexFn F Idx) ≃ₗ[ℂ] ComplexFn F Idx :=
    WithLp.linearEquiv 2 ℂ (ComplexFn F Idx)
  have hspan : Submodule.span ℂ (Set.range (charFn (F := F) (Idx := Idx))) = ⊤ :=
    (characters_orthonormal_basis (F := F) (Idx := Idx)).2
  calc
    Submodule.span ℂ (Set.range fun α : Vec F Idx => WithLp.toLp 2 (charFn α)) =
        (Submodule.span ℂ (Set.range (charFn (F := F) (Idx := Idx)))).map e.symm.toLinearMap := by
          change Submodule.span ℂ (Set.range (e.symm.toLinearMap ∘ charFn (F := F) (Idx := Idx))) =
            (Submodule.span ℂ (Set.range (charFn (F := F) (Idx := Idx)))).map e.symm.toLinearMap
          rw [Set.range_comp, Submodule.span_image]
    _ = ⊤ := by simp [hspan]

omit [Nonempty Idx] in
/-- The normalized character family spans the whole `PiLp` function space. -/
lemma normalizedCharLp_span_top :
    Submodule.span ℂ (Set.range (normalizedCharLp (F := F) (Idx := Idx))) = ⊤ := by
  let u : Vec F Idx → ℂˣ := fun _ =>
    Units.mk0 ((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)⁻¹)
      (inv_ne_zero (sqrt_card_ne_zero (F := F) (Idx := Idx)))
  have hu : u • (fun α : Vec F Idx => WithLp.toLp 2 (charFn α)) =
      normalizedCharLp (F := F) (Idx := Idx) := by
    funext α
    simp [normalizedCharLp, u]
  rw [← hu]
  exact Module.Basis.units_smul_span_eq_top
    (toLp_charFn_span_top (F := F) (Idx := Idx))

/-- The normalized Fourier characters packaged as an orthonormal basis of `PiLp`. -/
noncomputable def normalizedCharOrthonormalBasis :
    OrthonormalBasis (Vec F Idx) ℂ (PiLp 2 fun _ : Vec F Idx => ℂ) :=
  OrthonormalBasis.mk (normalizedCharLp_orthonormal (F := F) (Idx := Idx))
    (normalizedCharLp_span_top (F := F) (Idx := Idx)).ge

end HilbertSpaceTranslation

section FourierInversion

/-- Pointwise Fourier inversion in the character basis `χ_α`. -/
lemma fourier_inversion (g : ComplexFn F Idx) (x : Vec F Idx) :
    g x = ∑ α, fourierCoeff g α * charFn α x := by
  classical
  let b : OrthonormalBasis (Vec F Idx) ℂ (PiLp 2 fun _ : Vec F Idx => ℂ) :=
    normalizedCharOrthonormalBasis (F := F) (Idx := Idx)
  have hb := b.sum_repr' (WithLp.toLp 2 g)
  have hpoint := congrArg (fun v : PiLp 2 fun _ : Vec F Idx => ℂ => v x) hb
  calc
    g x = (WithLp.toLp 2 g : PiLp 2 fun _ : Vec F Idx => ℂ) x := rfl
    _ = (∑ α, inner ℂ (b α) (WithLp.toLp 2 g) • b α) x := hpoint.symm
    _ = ∑ α, fourierCoeff g α * charFn α x := by
      simp only [b, normalizedCharOrthonormalBasis, OrthonormalBasis.coe_mk,
        WithLp.ofLp_sum, WithLp.ofLp_smul]
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      change (∑ α, inner ℂ (normalizedCharLp (F := F) (Idx := Idx) α)
        (WithLp.toLp 2 g) * (normalizedCharLp (F := F) (Idx := Idx) α x)) =
          ∑ α, fourierCoeff g α * charFn α x
      apply Finset.sum_congr rfl
      intro α _
      rw [normalizedCharLp_inner_eq_sqrt_card_mul_fnInner]
      rw [fourierCoeff]
      simp only [normalizedCharLp, PiLp.smul_apply, smul_eq_mul]
      have hsqrt0 : (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 card_vec_pos))
      field_simp [hsqrt0]

end FourierInversion

section ParsevaPlancharel

/-- Parseval's identity for the finite-field Fourier transform. -/
lemma parseval_identity (g : ComplexFn F Idx) :
    ∑ α, ‖fourierCoeff g α‖ ^ 2 = fnNormSq g := by
  classical
  let b : OrthonormalBasis (Vec F Idx) ℂ (PiLp 2 fun _ : Vec F Idx => ℂ) :=
    normalizedCharOrthonormalBasis (F := F) (Idx := Idx)
  have hb : ∑ α, ‖inner ℂ (b α) (WithLp.toLp 2 g)‖ ^ 2 = ‖WithLp.toLp 2 g‖ ^ 2 :=
    OrthonormalBasis.sum_sq_norm_inner_right b (WithLp.toLp 2 g)
  have hb' : (Fintype.card (Vec F Idx) : ℝ) * ∑ α, ‖fnInner g (charFn α)‖ ^ 2 =
      ‖WithLp.toLp 2 g‖ ^ 2 := by
    simpa [b, normalizedCharOrthonormalBasis, Finset.mul_sum, norm_sq_normalizedCharLp_inner] using hb
  have hcard0 : (Fintype.card (Vec F Idx) : ℝ) ≠ 0 := by
    exact_mod_cast card_vec_pos.ne'
  calc
    ∑ α, ‖fourierCoeff g α‖ ^ 2 = ∑ α, ‖fnInner g (charFn α)‖ ^ 2 := by
      simp [fourierCoeff]
    _ = (Fintype.card (Vec F Idx) : ℝ)⁻¹ *
        ((Fintype.card (Vec F Idx) : ℝ) * ∑ α, ‖fnInner g (charFn α)‖ ^ 2) := by
          field_simp [hcard0]
    _ = (Fintype.card (Vec F Idx) : ℝ)⁻¹ * ‖WithLp.toLp 2 g‖ ^ 2 := by rw [hb']
    _ = fnNormSq g := by rw [fnNormSq_eq_card_inv_mul_norm_sq]

/-- Plancherel's identity for the finite-field Fourier transform. -/
lemma fourier_plancherel (f g : ComplexFn F Idx) :
    ∑ α, fourierCoeff f α * star (fourierCoeff g α) = fnInner f g := by
  classical
  let b : OrthonormalBasis (Vec F Idx) ℂ (PiLp 2 fun _ : Vec F Idx => ℂ) :=
    normalizedCharOrthonormalBasis (F := F) (Idx := Idx)
  have hb := OrthonormalBasis.sum_inner_mul_inner b (WithLp.toLp 2 g) (WithLp.toLp 2 f)
  have hterm : ∀ α : Vec F Idx,
      inner ℂ (WithLp.toLp 2 g) (b α) * inner ℂ (b α) (WithLp.toLp 2 f) =
        (Fintype.card (Vec F Idx) : ℂ) *
          (fourierCoeff f α * star (fourierCoeff g α)) := by
    intro α
    have hcalc :
        inner ℂ (WithLp.toLp 2 g) (normalizedCharLp (F := F) (Idx := Idx) α) *
            inner ℂ (normalizedCharLp (F := F) (Idx := Idx) α) (WithLp.toLp 2 f) =
          (Fintype.card (Vec F Idx) : ℂ) *
            (fourierCoeff f α * star (fourierCoeff g α)) := by
      rw [toLp_inner_normalizedCharLp_eq_sqrt_card_mul_star_fnInner,
        normalizedCharLp_inner_eq_sqrt_card_mul_fnInner]
      rw [fourierCoeff]
      calc
        ((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) * star (fnInner g (charFn α))) *
            ((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) * fnInner f (charFn α)) =
          ((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) *
            (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)) *
              (fnInner f (charFn α) * star (fnInner g (charFn α))) := by
            ring
        _ = (Fintype.card (Vec F Idx) : ℂ) *
            (fnInner f (charFn α) * star (fnInner g (charFn α))) := by
            rw [sqrt_card_mul_sqrt_card]
    simpa [b, normalizedCharOrthonormalBasis] using hcalc
  have hb' :
      (Fintype.card (Vec F Idx) : ℂ) *
          ∑ α, fourierCoeff f α * star (fourierCoeff g α) =
        (Fintype.card (Vec F Idx) : ℂ) * fnInner f g := by
    calc
      (Fintype.card (Vec F Idx) : ℂ) *
          ∑ α, fourierCoeff f α * star (fourierCoeff g α) =
        ∑ α, (Fintype.card (Vec F Idx) : ℂ) *
          (fourierCoeff f α * star (fourierCoeff g α)) := by
            rw [Finset.mul_sum]
      _ = ∑ α, inner ℂ (WithLp.toLp 2 g) (b α) *
          inner ℂ (b α) (WithLp.toLp 2 f) := by
            exact Finset.sum_congr rfl fun α _ => (hterm α).symm
      _ = inner ℂ (WithLp.toLp 2 g) (WithLp.toLp 2 f) := hb
      _ = (Fintype.card (Vec F Idx) : ℂ) * fnInner f g := by
            rw [toLp_inner_eq_card_mul_fnInner]
  have hcard0 : (Fintype.card (Vec F Idx) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact mul_left_cancel₀ hcard0 hb'

end ParsevaPlancharel

section DistanceViaPhaseCoeff

/-- Split a sum over all field elements into the zero term and the sum over nonzero elements. -/
lemma sum_univ_eq_zero_add_sum_nonzero (h : F → ℂ) :
    ∑ c : F, h c = h 0 + ∑ c ∈ (nonzeroF (F := F)), h c := by
  classical
  rw [← Finset.add_sum_erase Finset.univ h (by simp : (0 : F) ∈ Finset.univ)]
  congr 1
  apply Finset.sum_congr
  · ext c
    simp [nonzeroF]
  · intro c _
    rfl

/-- The equality indicator in `F` as an average of additive characters. -/
lemma character_sum_indicator_eq (u v : F) :
    (if u = v then (1 : ℂ) else 0) =
      (Fintype.card F : ℂ)⁻¹ * ∑ c : F, baseChar (F := F) (c * (u - v)) := by
  classical
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  letI : NeZero (ringChar F) := ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  by_cases huv : u = v
  · have hcard : (Fintype.card F : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [huv, hcard]
  · let ψt : AddChar F ℂ :=
      (baseChar (F := F)).compAddMonoidHom (AddMonoidHom.mulRight (u - v))
    have ht : u - v ≠ 0 := sub_ne_zero.mpr huv
    have hψt_ne_zero : ψt ≠ 0 := by
      obtain ⟨c, hc⟩ := FiniteField.trace_to_zmod_nondegenerate F (a := u - v) ht
      intro hψt
      have hval : baseChar (F := F) (c * (u - v)) = 1 := by
        simpa [ψt] using congrArg (fun ψ : AddChar F ℂ => ψ c) hψt
      have htrace_zero :
          Algebra.trace (ZMod (ringChar F)) F (c * (u - v)) = 0 := by
        exact ZMod.injective_stdAddChar (N := ringChar F) (by
          simpa [baseChar] using hval)
      exact hc (by simpa [mul_comm] using htrace_zero)
    have hsum_zero : (∑ c : F, baseChar (F := F) (c * (u - v))) = 0 := by
      have hsumψ : (∑ c : F, ψt c) = 0 := by
        rw [AddChar.sum_eq_ite ψt]
        simp [hψt_ne_zero]
      simpa [ψt] using hsumψ
    simp [huv, hsum_zero]

omit [DecidableEq F] [Fintype Idx] [DecidableEq Idx] [Nonempty Idx] in
/-- Multiplying one phase lift by the conjugate of another collapses to the phase
of the pointwise difference. -/
private lemma phaseLift_mul_star (f g : ScalarFn F Idx) (c : F) (x : Vec F Idx) :
    phaseLift f c x * star (phaseLift g c x) =
      baseChar (F := F) (c * (f x - g x)) := by
  classical
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  letI : NeZero (ringChar F) := ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  let ψ : AddChar F ℂ := baseChar (F := F)
  have hstar : star (ψ (c * g x)) = (ψ (c * g x))⁻¹ := by
    exact (Complex.inv_eq_conj (AddChar.norm_apply ψ (c * g x))).symm
  calc
    phaseLift f c x * star (phaseLift g c x)
        = ψ (c * f x) * star (ψ (c * g x)) := by
            simp [phaseLift, baseChar, ψ]
    _ = ψ (c * f x) * (ψ (c * g x))⁻¹ := by rw [hstar]
    _ = ψ (c * f x) / ψ (c * g x) := by rw [div_eq_mul_inv]
    _ = ψ (c * f x - c * g x) := by
            rw [← AddChar.map_sub_eq_div]
    _ = ψ (c * (f x - g x)) := by rw [mul_sub]
    _ = baseChar (F := F) (c * (f x - g x)) := rfl

omit [DecidableEq F] [Nonempty Idx] in
/-- The phase-lift inner product is the average of the character of pointwise differences. -/
private lemma fnInner_phaseLift_eq_character_average (f g : ScalarFn F Idx) (c : F) :
    fnInner (phaseLift f c) (phaseLift g c) =
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, baseChar (F := F) (c * (f x - g x)) := by
  unfold fnInner expectation
  congr 1
  · norm_num
  · exact Finset.sum_congr rfl fun x _ => phaseLift_mul_star f g c x

/-- The agreement probability of two scalar functions as an average of phase-lift inner products. -/
private lemma agreement_probability_eq_phase_inner (f g : ScalarFn F Idx) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, (if f x = g x then (1 : ℂ) else 0) =
      (Fintype.card F : ℂ)⁻¹ *
        (1 + ∑ c ∈ (nonzeroF (F := F)),
          fnInner (phaseLift f c) (phaseLift g c)) := by
  classical
  calc
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, (if f x = g x then (1 : ℂ) else 0) =
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx,
          (Fintype.card F : ℂ)⁻¹ *
            ∑ c : F, baseChar (F := F) (c * (f x - g x)) := by
        congr 1
        exact Finset.sum_congr rfl fun x _ => character_sum_indicator_eq (f x) (g x)
    _ = (Fintype.card F : ℂ)⁻¹ *
        ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          ∑ x : Vec F Idx, ∑ c : F, baseChar (F := F) (c * (f x - g x))) := by
        simp [Finset.mul_sum, mul_left_comm]
    _ = (Fintype.card F : ℂ)⁻¹ *
        ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          ∑ x : Vec F Idx,
            (1 + ∑ c ∈ (nonzeroF (F := F)),
              baseChar (F := F) (c * (f x - g x)))) := by
        congr 2
        apply Finset.sum_congr rfl
        intro x _
        rw [sum_univ_eq_zero_add_sum_nonzero]
        simp [baseChar]
    _ = (Fintype.card F : ℂ)⁻¹ *
        (1 + ∑ c ∈ (nonzeroF (F := F)),
          fnInner (phaseLift f c) (phaseLift g c)) := by
        congr 1
        calc
          (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              ∑ x : Vec F Idx,
                (1 + ∑ c ∈ (nonzeroF (F := F)),
                  baseChar (F := F) (c * (f x - g x))) =
            1 + (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              ∑ x : Vec F Idx, ∑ c ∈ (nonzeroF (F := F)),
                baseChar (F := F) (c * (f x - g x)) := by
              simp [Finset.sum_add_distrib, mul_add, Finset.mul_sum]
          _ = 1 + (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              ∑ c ∈ (nonzeroF (F := F)), ∑ x : Vec F Idx,
                baseChar (F := F) (c * (f x - g x)) := by
              rw [Finset.sum_comm]
          _ = 1 + ∑ c ∈ (nonzeroF (F := F)),
              (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                ∑ x : Vec F Idx, baseChar (F := F) (c * (f x - g x)) := by
              rw [Finset.mul_sum]
          _ = 1 + ∑ c ∈ (nonzeroF (F := F)),
              fnInner (phaseLift f c) (phaseLift g c) := by
              congr 1
              apply Finset.sum_congr rfl
              intro c _
              rw [fnInner_phaseLift_eq_character_average]

/-- Distance is one minus the complex-valued agreement probability. -/
private lemma distance_eq_one_sub_agreement (f g : ScalarFn F Idx) :
    (distance f g : ℂ) =
      1 - (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, (if f x = g x then (1 : ℂ) else 0) := by
  classical
  calc
    (distance f g : ℂ) =
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, (if f x ≠ g x then (1 : ℂ) else 0) := by
        simp [distance]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : f x = g x <;> simp [hx]
    _ = (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, (1 - (if f x = g x then (1 : ℂ) else 0)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : f x = g x <;> simp [hx]
    _ = 1 - (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, (if f x = g x then (1 : ℂ) else 0) := by
        simp [Finset.sum_sub_distrib, mul_sub]

/-- Relative Hamming distance in terms of the Fourier coefficients of the
nonzero phase lifts of `f` and `g`. -/
lemma distance_formula_via_phase_fourier_coefficients (f g : ScalarFn F Idx) :
    (distance f g : ℂ) =
      1 - (Fintype.card F : ℂ)⁻¹ *
        (1 + ∑ c ∈ (nonzeroF (F := F)), ∑ α : Vec F Idx,
          fourierCoeff (phaseLift f c) α * star (fourierCoeff (phaseLift g c) α)) := by
  calc
    (distance f g : ℂ) =
      1 - (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, (if f x = g x then (1 : ℂ) else 0) := by
        rw [distance_eq_one_sub_agreement]
    _ = 1 - (Fintype.card F : ℂ)⁻¹ *
        (1 + ∑ c ∈ (nonzeroF (F := F)),
          fnInner (phaseLift f c) (phaseLift g c)) := by
        rw [agreement_probability_eq_phase_inner]
    _ = 1 - (Fintype.card F : ℂ)⁻¹ *
        (1 + ∑ c ∈ (nonzeroF (F := F)), ∑ α : Vec F Idx,
          fourierCoeff (phaseLift f c) α * star (fourierCoeff (phaseLift g c) α)) := by
        congr 2
        congr 1
        apply Finset.sum_congr rfl
        intro c _
        rw [← fourier_plancherel (phaseLift f c) (phaseLift g c)]

end DistanceViaPhaseCoeff

end BlrPcp
