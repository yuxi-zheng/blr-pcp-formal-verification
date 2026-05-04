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

variable {F Idx : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]

abbrev Vec (F : Type*) (Idx : Type*) := Idx → F
abbrev ScalarFn (F : Type*) (Idx : Type*) := Vec F Idx → F
abbrev ComplexFn (F : Type*) (Idx : Type*) := Vec F Idx → Complex

/-- The linear scalar function `ℓ_a(x) = ∑ i, a i * x i`. -/
def linearFn (a : Vec F Idx) : ScalarFn F Idx :=
  fun x => ∑ i, a i * x i

def IsLinear (f : ScalarFn F Idx) : Prop :=
  ∃ a : Vec F Idx, ∀ x, f x = linearFn a x

def LinearSet : Set (ScalarFn F Idx) := {f | IsLinear f}

/-- The real-valued indicator of membership in the set of linear scalar functions. -/
noncomputable def linearSetIndicator (f : ScalarFn F Idx) : Real := by
  classical
  exact if f ∈ LinearSet (F := F) (Idx := Idx) then 1 else 0

def BLRAcceptsAt (f : ScalarFn F Idx) (a b : F) (x y : Vec F Idx) : Prop :=
  a * f x + b * f y = f (fun i => a * x i + b * y i)

/-- The nonzero field elements used as BLR scalar samples. -/
def nonzeroScalars : Finset F :=
  Finset.univ.filter fun a => a ≠ 0

private lemma sum_univ_eq_zero_add_sum_nonzero (h : F → ℂ) :
    ∑ c : F, h c = h 0 + ∑ c ∈ (nonzeroScalars (F := F)), h c := by
  classical
  rw [← Finset.add_sum_erase Finset.univ h (by simp : (0 : F) ∈ Finset.univ)]
  congr 1
  apply Finset.sum_congr
  · ext c
    simp [nonzeroScalars]
  · intro c _
    rfl

/-- The uniform acceptance probability of the finite-field BLR test:
`a,b` are sampled uniformly from `F \ {0}` and `x,y` from `F^Idx`. -/
noncomputable def acceptanceProbabilityBLR (f : ScalarFn F Idx) : Real := by
  classical
  exact
    ((nonzeroScalars (F := F)).card : Real)⁻¹ *
      ((nonzeroScalars (F := F)).card : Real)⁻¹ *
        (Fintype.card (Vec F Idx) : Real)⁻¹ *
          (Fintype.card (Vec F Idx) : Real)⁻¹ *
            ∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
              ∑ x : Vec F Idx, ∑ y : Vec F Idx,
                if BLRAcceptsAt f a b x y then (1 : Real) else 0

noncomputable def rejectionProbabilityBLR (f : ScalarFn F Idx) : Real :=
  1 - acceptanceProbabilityBLR f

/-- The relative Hamming distance between two scalar functions, i.e. the
uniform probability that they disagree on a point of `F^Idx`. -/
noncomputable def distance (f g : ScalarFn F Idx) : Real :=
  (Fintype.card (Vec F Idx) : Real)⁻¹ *
    ∑ x : Vec F Idx, if f x ≠ g x then (1 : Real) else 0

private noncomputable def linearFunctionsFinset : Finset (ScalarFn F Idx) := by
  classical
  exact Finset.univ.filter fun g => g ∈ LinearSet (F := F) (Idx := Idx)

omit [Nonempty Idx] in
private lemma linearFunctionsFinset_nonempty :
    (linearFunctionsFinset (F := F) (Idx := Idx)).Nonempty := by
  refine ⟨linearFn (F := F) (Idx := Idx) 0, ?_⟩
  simp only [linearFunctionsFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    LinearSet, Set.mem_setOf_eq]
  exact ⟨0, fun x => rfl⟩

/-- The distance from a scalar function to linearity, namely the minimum of
`distance f g` over all `g ∈ LinearSet`. -/
noncomputable def distanceToLinear (f : ScalarFn F Idx) : Real := by
  classical
  exact
    (linearFunctionsFinset (F := F) (Idx := Idx)).inf'
      (linearFunctionsFinset_nonempty (F := F) (Idx := Idx)) fun g => distance f g

section BLRPointwise

omit [Fintype F] [DecidableEq F] [DecidableEq Idx] [Nonempty Idx]

/-- A linear function passes the BLR check for every choice of randomness. -/
lemma BLRAcceptsAt_linearFn (α : Vec F Idx) (a b : F) (x y : Vec F Idx) :
    BLRAcceptsAt (linearFn α) a b x y := by
  classical
  simp [BLRAcceptsAt, linearFn, Finset.mul_sum, Finset.sum_add_distrib, mul_add,
    mul_left_comm]

/-- Every member of `LinearSet` passes the BLR check pointwise. -/
lemma BLRAcceptsAt_of_mem_linearSet {f : ScalarFn F Idx}
    (hf : f ∈ LinearSet (F := F) (Idx := Idx)) (a b : F) (x y : Vec F Idx) :
    BLRAcceptsAt f a b x y := by
  rcases hf with ⟨α, hα⟩
  unfold BLRAcceptsAt
  rw [hα x, hα y, hα (fun i => a * x i + b * y i)]
  exact BLRAcceptsAt_linearFn (F := F) (Idx := Idx) α a b x y

end BLRPointwise

omit [Nonempty Idx] in
/-- Completeness of the finite-field BLR verifier: linear functions are accepted
with probability one. -/
lemma blr_completeness {f : ScalarFn F Idx}
    (hf : f ∈ LinearSet (F := F) (Idx := Idx)) :
    acceptanceProbabilityBLR f = 1 := by
  classical
  have hnz_nonempty : (nonzeroScalars (F := F)).Nonempty := by
    exact ⟨1, by simp [nonzeroScalars]⟩
  have hnz_card : ((nonzeroScalars (F := F)).card : Real) ≠ 0 := by
    exact_mod_cast hnz_nonempty.card_pos.ne'
  have hF_card : (Fintype.card F : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hvec_card_pow : ((Fintype.card F : Real) ^ Fintype.card Idx) ≠ 0 :=
    pow_ne_zero _ hF_card
  simp [acceptanceProbabilityBLR, BLRAcceptsAt_of_mem_linearSet (F := F) (Idx := Idx) hf,
    mul_assoc]
  field_simp [hnz_card, hvec_card_pow]

/-- The standard bilinear pairing on `F^Idx`. -/
def dotProduct (a x : Vec F Idx) : F :=
  ∑ i, a i * x i

/-- Notation for the standard bilinear pairing on `F^Idx`. -/
scoped notation "⟪" a ", " x "⟫ᵥ" => dotProduct a x

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


omit [Fintype F] [DecidableEq F] [Nonempty Idx] in
private lemma dotProduct_single (a : Vec F Idx) (i : Idx) (t : F) :
    dotProduct a (Pi.single i t) = a i * t := by
  classical
  rw [dotProduct, Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    simp [Pi.single_eq_of_ne hij]
  · intro hi
    simp at hi

omit [Fintype F] [DecidableEq F] [Nonempty Idx] in
private lemma dotProduct_single_left (x : Vec F Idx) (i : Idx) (t : F) :
    dotProduct (Pi.single i t) x = t * x i := by
  classical
  rw [dotProduct, Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    simp [Pi.single_eq_of_ne hij]
  · intro hi
    simp at hi

omit [Fintype F] [DecidableEq F] [DecidableEq Idx] [Nonempty Idx] in
private lemma dotProduct_sub_left (a b x : Vec F Idx) :
    dotProduct (a - b) x = dotProduct a x - dotProduct b x := by
  simp [dotProduct, sub_mul, Finset.sum_sub_distrib]

private noncomputable def dotProductAddMonoidHom (a : Vec F Idx) : Vec F Idx →+ F where
  toFun := dotProduct a
  map_zero' := by simp [dotProduct]
  map_add' x y := by
    simp [dotProduct, mul_add, Finset.sum_add_distrib]

private noncomputable def dotProductLeftAddMonoidHom (x : Vec F Idx) : Vec F Idx →+ F where
  toFun := fun a => dotProduct a x
  map_zero' := by simp [dotProduct]
  map_add' a b := by
    simp [dotProduct, add_mul, Finset.sum_add_distrib]

omit [Fintype F] [Nonempty Idx] in
private lemma dotProductLeftAddMonoidHom_surjective {x : Vec F Idx}
    (hx : x ≠ 0) :
    Function.Surjective (dotProductLeftAddMonoidHom (F := F) (Idx := Idx) x) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    ext i
    by_contra hi
    exact h ⟨i, hi⟩
  intro t
  refine ⟨Pi.single i (t * (x i)⁻¹), ?_⟩
  change dotProduct (Pi.single i (t * (x i)⁻¹)) x = t
  rw [dotProduct_single_left]
  field_simp [hi]

omit [Nonempty Idx] in
private lemma dotProduct_left_fiber_card_mul_card {x : Vec F Idx}
    (hx : x ≠ 0) (t : F) :
    ((Finset.univ.filter fun a : Vec F Idx => dotProduct a x = t).card) *
      Fintype.card F = Fintype.card (Vec F Idx) := by
  classical
  let L : Vec F Idx →+ F := dotProductLeftAddMonoidHom (F := F) (Idx := Idx) x
  have hsurj : Function.Surjective L :=
    dotProductLeftAddMonoidHom_surjective (F := F) (Idx := Idx) hx
  have hfibers : ∀ u : F,
      (Finset.univ.filter fun a : Vec F Idx => L a = u).card =
        (Finset.univ.filter fun a : Vec F Idx => L a = t).card := by
    intro u
    exact AddMonoidHom.card_fiber_eq_of_mem_range L (hsurj u) (hsurj t)
  have hpartition :
      (∑ u : F, (Finset.univ.filter fun a : Vec F Idx => L a = u).card) =
        Fintype.card (Vec F Idx) := by
    simpa using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (Vec F Idx)))
        (t := (Finset.univ : Finset F))
        (f := fun a : Vec F Idx => L a)
        (by intro a _; simp)).symm
  calc
    ((Finset.univ.filter fun a : Vec F Idx => dotProduct a x = t).card) *
        Fintype.card F =
      ((Finset.univ.filter fun a : Vec F Idx => L a = t).card) *
        Fintype.card F := by rfl
    _ = ∑ _u : F, (Finset.univ.filter fun a : Vec F Idx => L a = t).card := by
        simp [mul_comm]
    _ = ∑ u : F, (Finset.univ.filter fun a : Vec F Idx => L a = u).card := by
        apply Finset.sum_congr rfl
        intro u _
        exact (hfibers u).symm
    _ = Fintype.card (Vec F Idx) := hpartition

private def agreementCount (f : ScalarFn F Idx) (α : Vec F Idx) : ℕ :=
  (Finset.univ.filter fun x : Vec F Idx => f x = linearFn α x).card

omit [Nonempty Idx] in
private lemma sum_agreementCount_eq_sum_dotProduct_fibers (f : ScalarFn F Idx) :
    ∑ α : Vec F Idx, agreementCount f α =
      ∑ x : Vec F Idx,
        (Finset.univ.filter fun α : Vec F Idx => dotProduct α x = f x).card := by
  classical
  unfold agreementCount
  calc
    ∑ α : Vec F Idx, (Finset.univ.filter fun x : Vec F Idx =>
        f x = linearFn α x).card =
      ∑ α : Vec F Idx, ∑ x : Vec F Idx,
        if f x = linearFn α x then (1 : ℕ) else 0 := by
        simp
    _ = ∑ x : Vec F Idx, ∑ α : Vec F Idx,
        if f x = linearFn α x then (1 : ℕ) else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ x : Vec F Idx,
        (Finset.univ.filter fun α : Vec F Idx => dotProduct α x = f x).card := by
        apply Finset.sum_congr rfl
        intro x _
        simp [linearFn, dotProduct, eq_comm]

omit [Nonempty Idx] in
private lemma nonzero_vec_card :
    (Finset.univ.filter fun x : Vec F Idx => x ≠ 0).card =
      Fintype.card (Vec F Idx) - 1 := by
  classical
  have h0 : (0 : Vec F Idx) ∈ (Finset.univ : Finset (Vec F Idx)) := by simp
  change (Finset.univ.filter fun x : Vec F Idx => x ≠ 0).card =
    (Finset.univ : Finset (Vec F Idx)).card - 1
  rw [← Finset.card_erase_of_mem h0]
  congr 1
  ext x
  simp

omit [Nonempty Idx] in
private lemma sum_agreementCount_lower (f : ScalarFn F Idx) :
    (Fintype.card (Vec F Idx) - 1) *
        (Fintype.card (Vec F Idx) / Fintype.card F) ≤
      ∑ α : Vec F Idx, agreementCount f α := by
  classical
  let N := Fintype.card (Vec F Idx)
  let q := Fintype.card F
  let k := N / q
  have hq0 : q ≠ 0 := by
    dsimp [q]
    exact Fintype.card_ne_zero
  have hfiber_ge : ∀ x : Vec F Idx,
      (if x = 0 then 0 else k) ≤
        (Finset.univ.filter fun α : Vec F Idx => dotProduct α x = f x).card := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have hmul := dotProduct_left_fiber_card_mul_card (F := F) (Idx := Idx) hx (f x)
      have hfiber :
          (Finset.univ.filter fun α : Vec F Idx => dotProduct α x = f x).card = k := by
        dsimp [k, N, q]
        exact Nat.eq_div_of_mul_eq_right hq0 (by simpa [mul_comm] using hmul)
      simp [hx, hfiber]
  have hsum_nonzero :
      (∑ x : Vec F Idx, if x = 0 then 0 else k) = (N - 1) * k := by
    calc
      (∑ x : Vec F Idx, if x = 0 then 0 else k) =
          ∑ x : Vec F Idx, if x ≠ 0 then k else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = 0 <;> simp [hx]
      _ = ∑ x ∈ (Finset.univ.filter fun x : Vec F Idx => x ≠ 0), k := by
          exact (Finset.sum_filter (s := (Finset.univ : Finset (Vec F Idx)))
            (p := fun x : Vec F Idx => x ≠ 0) (f := fun _ => k)).symm
      _ = (N - 1) * k := by
          simp [N, nonzero_vec_card]
  calc
    (Fintype.card (Vec F Idx) - 1) *
        (Fintype.card (Vec F Idx) / Fintype.card F) =
        (N - 1) * k := rfl
    _ = ∑ x : Vec F Idx, if x = 0 then 0 else k := hsum_nonzero.symm
    _ ≤ ∑ x : Vec F Idx,
        (Finset.univ.filter fun α : Vec F Idx => dotProduct α x = f x).card := by
        exact Finset.sum_le_sum fun x _ => hfiber_ge x
    _ = ∑ α : Vec F Idx, agreementCount f α :=
        (sum_agreementCount_eq_sum_dotProduct_fibers (F := F) (Idx := Idx) f).symm

omit [DecidableEq F] [Nonempty Idx] in
private lemma card_vec_div_card_field_pos [Nonempty Idx] :
    0 < Fintype.card (Vec F Idx) / Fintype.card F := by
  classical
  let q := Fintype.card F
  let m := Fintype.card Idx
  have hq : 1 < q := by
    dsimp [q]
    exact Fintype.one_lt_card
  have hm : 0 < m := by
    dsimp [m]
    exact Fintype.card_pos_iff.mpr inferInstance
  have hcard : Fintype.card (Vec F Idx) = q ^ m := by
    dsimp [q, m]
    simp
  have hdiv : Fintype.card (Vec F Idx) / q = q ^ (m - 1) := by
    calc
      Fintype.card (Vec F Idx) / q = q ^ m / q := by rw [hcard]
      _ = q ^ (m - 1) := by
          rw [← Nat.succ_pred_eq_of_pos hm, pow_succ, Nat.succ_sub_one]
          exact Nat.mul_div_left _ (Nat.zero_lt_of_lt hq)
  rw [hdiv]
  exact pow_pos (Nat.zero_lt_of_lt hq) _

omit [DecidableEq F] [Nonempty Idx] in
private lemma card_vec_div_card_field_lt_card_vec [Nonempty Idx] :
    Fintype.card (Vec F Idx) / Fintype.card F < Fintype.card (Vec F Idx) := by
  classical
  let q := Fintype.card F
  let m := Fintype.card Idx
  have hq : 1 < q := by
    dsimp [q]
    exact Fintype.one_lt_card
  have hm : 0 < m := by
    dsimp [m]
    exact Fintype.card_pos_iff.mpr inferInstance
  have hcard : Fintype.card (Vec F Idx) = q ^ m := by
    dsimp [q, m]
    simp
  have hdiv : q ^ m / q = q ^ (m - 1) := by
    rw [← Nat.succ_pred_eq_of_pos hm, pow_succ, Nat.succ_sub_one]
    exact Nat.mul_div_left _ (Nat.zero_lt_of_lt hq)
  rw [hcard]
  have hqeq : Fintype.card F = q := rfl
  rw [hqeq]
  rw [hdiv]
  exact Nat.pow_lt_pow_right hq (Nat.pred_lt hm.ne')

omit [Nonempty Idx] in
private lemma exists_agreementCount_ge [Nonempty Idx] (f : ScalarFn F Idx) :
    ∃ α : Vec F Idx,
      Fintype.card (Vec F Idx) / Fintype.card F ≤ agreementCount f α := by
  classical
  let N := Fintype.card (Vec F Idx)
  let k := Fintype.card (Vec F Idx) / Fintype.card F
  have hkpos : 0 < k := by
    dsimp [k]
    exact card_vec_div_card_field_pos (F := F) (Idx := Idx)
  have hkltN : k < N := by
    dsimp [k, N]
    exact card_vec_div_card_field_lt_card_vec (F := F) (Idx := Idx)
  have hstrict : (∑ _α : Vec F Idx, (k - 1)) <
      ∑ α : Vec F Idx, agreementCount f α := by
    have hlower := sum_agreementCount_lower (F := F) (Idx := Idx) f
    have hnum :
        (∑ _α : Vec F Idx, (k - 1)) < (N - 1) * k := by
      have hNpos : 0 < N := by
        dsimp [N]
        exact Fintype.card_pos
      have hnum' : N * (k - 1) < (N - 1) * k := by
        have hk1 : 1 ≤ k := Nat.succ_le_of_lt hkpos
        have hN1 : 1 ≤ N := Nat.succ_le_of_lt hNpos
        have hleft :
            ((N * (k - 1) : ℕ) : ℤ) = (N : ℤ) * ((k : ℤ) - 1) := by
          rw [Nat.cast_mul, Nat.cast_sub hk1, Nat.cast_one]
        have hright :
            (((N - 1) * k : ℕ) : ℤ) = ((N : ℤ) - 1) * (k : ℤ) := by
          rw [Nat.cast_mul, Nat.cast_sub hN1, Nat.cast_one]
        have hnum_int :
            ((N * (k - 1) : ℕ) : ℤ) < (((N - 1) * k : ℕ) : ℤ) := by
          rw [hleft, hright]
          have hkltN_int : (k : ℤ) < (N : ℤ) := by exact_mod_cast hkltN
          nlinarith
        exact_mod_cast hnum_int
      simpa [N] using hnum'
    exact hnum.trans_le (by simpa [N, k] using hlower)
  have hstrict' :
      (∑ α ∈ (Finset.univ : Finset (Vec F Idx)), (k - 1)) <
        ∑ α ∈ (Finset.univ : Finset (Vec F Idx)), agreementCount f α := by
    simpa using hstrict
  rcases Finset.exists_lt_of_sum_lt
      (s := (Finset.univ : Finset (Vec F Idx)))
      (f := fun _α : Vec F Idx => k - 1)
      (g := agreementCount f) hstrict' with ⟨α, _, hα⟩
  refine ⟨α, ?_⟩
  exact Nat.le_of_pred_lt (by simpa [Nat.pred_eq_sub_one, k] using hα)

private noncomputable def baseChar : AddChar F ℂ := by
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  letI : NeZero (ringChar F) := ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  exact (ZMod.stdAddChar (N := ringChar F)).compAddMonoidHom
    (Algebra.trace (ZMod (ringChar F)) F).toAddMonoidHom

/-- Character-sum indicator for equality in `F`: `baseChar` is the Lean
encoding of `ω_p^{Tr(·)}`. -/
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
private lemma fnInner_phaseLift_eq_character_average (f g : ScalarFn F Idx) (c : F) :
    fnInner (phaseLift f c) (phaseLift g c) =
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, baseChar (F := F) (c * (f x - g x)) := by
  unfold fnInner expectation
  congr 1
  · norm_num
  · exact Finset.sum_congr rfl fun x _ => phaseLift_mul_star f g c x

private noncomputable def charAddChar (a : Vec F Idx) : AddChar (Vec F Idx) ℂ :=
  (baseChar (F := F)).compAddMonoidHom (dotProductAddMonoidHom (F := F) (Idx := Idx) a)

omit [DecidableEq F] [DecidableEq Idx] [Nonempty Idx] in
@[simp] private lemma charAddChar_apply (a x : Vec F Idx) :
    charAddChar (F := F) (Idx := Idx) a x = charFn a x := rfl

omit [Nonempty Idx] in
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


omit [Nonempty Idx] in
lemma characters_orthogonal_basis :
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

omit [DecidableEq F] [DecidableEq Idx] [Nonempty Idx] in
/-- The `c`-phase of the linear function `ℓ_α` is the character `χ_{cα}`. -/
lemma phaseLift_linearFn (α : Vec F Idx) (c : F) :
    phaseLift (linearFn α) c = charFn (fun i => c * α i) := by
  classical
  funext x
  simp [phaseLift, charFn, linearFn, dotProduct, Finset.mul_sum, mul_assoc]

omit [Nonempty Idx] in
/-- Fourier expansion of a linear function: the `c`-phase of `ℓ_α` has a
single Fourier coefficient, at `cα`. -/
lemma fourierCoeff_phaseLift_linearFn (α β : Vec F Idx) (c : F) :
    (phaseLift (linearFn α) c)̂(β) =
      if β = (fun i => c * α i) then 1 else 0 := by
  rw [phaseLift_linearFn]
  simpa [fourierCoeff, eq_comm] using
    (characters_orthogonal_basis (F := F) (Idx := Idx)).1 (fun i => c * α i) β

omit [DecidableEq F] [Nonempty Idx] in
private lemma card_vec_pos : 0 < Fintype.card (Vec F Idx) := Fintype.card_pos

omit [Field F] [DecidableEq F] [Nonempty Idx] in
private lemma fnNormSq_eq_card_inv_mul_norm_sq (g : ComplexFn F Idx) :
    fnNormSq g = (Fintype.card (Vec F Idx) : ℝ)⁻¹ * ‖WithLp.toLp 2 g‖ ^ 2 := by
  simp [fnNormSq, PiLp.norm_sq_eq_of_L2]

omit [DecidableEq F] [Nonempty Idx] in
private lemma sqrt_card_mul_inv_sqrt_card :
    (((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)⁻¹) *
      (Fintype.card (Vec F Idx) : ℂ)) =
        (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) := by
  have hsqrt0 : (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 card_vec_pos))
  field_simp [hsqrt0]
  exact_mod_cast (Real.sq_sqrt (Nat.cast_nonneg (Fintype.card (Vec F Idx)) : (0 : ℝ) ≤ _)).symm

omit [Field F] [DecidableEq F] [Nonempty Idx] in
private lemma sqrt_card_mul_sqrt_card :
    (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) *
      (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) =
        (Fintype.card (Vec F Idx) : ℂ) := by
  rw [← Complex.ofReal_mul, ← sq]
  exact_mod_cast (Real.sq_sqrt
    (Nat.cast_nonneg (Fintype.card (Vec F Idx)) : (0 : ℝ) ≤ _))

omit [Field F] [DecidableEq F] [Nonempty Idx] in
private lemma sqrt_card_mul_sqrt_card_mul (z : ℂ) :
    (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) *
      ((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) * z) =
        (Fintype.card (Vec F Idx) : ℂ) * z := by
  rw [← mul_assoc, sqrt_card_mul_sqrt_card]

omit [DecidableEq F] [Nonempty Idx] in
private lemma inv_sqrt_card_sq_mul_card :
    (((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)⁻¹) *
      (((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)⁻¹) * (Fintype.card (Vec F Idx) : ℂ))) = 1 := by
  have hsqrt0 : (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 card_vec_pos))
  field_simp [hsqrt0]
  exact_mod_cast (Real.sq_sqrt (Nat.cast_nonneg (Fintype.card (Vec F Idx)) : (0 : ℝ) ≤ _)).symm

omit [DecidableEq F] in
private lemma toLp_charFn_inner_eq_card_mul_fnInner (g : ComplexFn F Idx) (α : Vec F Idx) :
    inner ℂ (WithLp.toLp 2 (charFn α)) (WithLp.toLp 2 g) =
      (Fintype.card (Vec F Idx) : ℂ) * fnInner g (charFn α) := by
  rw [← RCLike.wInner_one_eq_inner (charFn α) g]
  simp [RCLike.wInner, fnInner, expectation, RCLike.inner_apply]

omit [DecidableEq F] in
private lemma toLp_inner_eq_card_mul_fnInner (f g : ComplexFn F Idx) :
    inner ℂ (WithLp.toLp 2 g) (WithLp.toLp 2 f) =
      (Fintype.card (Vec F Idx) : ℂ) * fnInner f g := by
  rw [← RCLike.wInner_one_eq_inner g f]
  simp [RCLike.wInner, fnInner, expectation, RCLike.inner_apply]

private noncomputable def normalizedCharLp (α : Vec F Idx) : PiLp 2 fun _ : Vec F Idx => ℂ :=
  ((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)⁻¹) • WithLp.toLp 2 (charFn α)

private lemma normalizedCharLp_orthonormal :
    Orthonormal ℂ (normalizedCharLp (F := F) (Idx := Idx)) := by
  classical
  rw [orthonormal_iff_ite]
  intro α β
  rw [normalizedCharLp, normalizedCharLp, inner_smul_left, inner_smul_right,
    toLp_charFn_inner_eq_card_mul_fnInner]
  by_cases h : α = β
  · subst h
    have horthα : fnInner (charFn α) (charFn α) = (1 : ℂ) := by
      simpa using (characters_orthogonal_basis (F := F) (Idx := Idx)).1 α α
    simp [horthα]
    simpa using (inv_sqrt_card_sq_mul_card (F := F) (Idx := Idx))
  · have horth := (characters_orthogonal_basis (F := F) (Idx := Idx)).1 β α
    have h' : β ≠ α := by simpa [eq_comm] using h
    simp [horth, h, h']

omit [DecidableEq F] in
private lemma normalizedCharLp_inner_eq_sqrt_card_mul_fnInner (g : ComplexFn F Idx)
    (α : Vec F Idx) :
    inner ℂ (normalizedCharLp (F := F) (Idx := Idx) α) (WithLp.toLp 2 g) =
      (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) * fnInner g (charFn α) := by
  have hstarinv : (starRingEnd ℂ) ((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)⁻¹) =
      ((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)⁻¹) := by simp
  rw [normalizedCharLp, inner_smul_left, toLp_charFn_inner_eq_card_mul_fnInner, hstarinv]
  calc
    ((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)⁻¹) *
        ((Fintype.card (Vec F Idx) : ℂ) * fnInner g (charFn α)) =
      ((((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)⁻¹) * (Fintype.card (Vec F Idx) : ℂ)) *
        fnInner g (charFn α)) := by ring
    _ = (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) * fnInner g (charFn α) := by
      rw [sqrt_card_mul_inv_sqrt_card]

omit [DecidableEq F] in
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
private lemma toLp_charFn_span_top :
    Submodule.span ℂ (Set.range fun α : Vec F Idx => WithLp.toLp 2 (charFn α)) = ⊤ := by
  let e : WithLp 2 (ComplexFn F Idx) ≃ₗ[ℂ] ComplexFn F Idx :=
    WithLp.linearEquiv 2 ℂ (ComplexFn F Idx)
  have hspan : Submodule.span ℂ (Set.range (charFn (F := F) (Idx := Idx))) = ⊤ :=
    (characters_orthogonal_basis (F := F) (Idx := Idx)).2
  calc
    Submodule.span ℂ (Set.range fun α : Vec F Idx => WithLp.toLp 2 (charFn α)) =
        (Submodule.span ℂ (Set.range (charFn (F := F) (Idx := Idx)))).map e.symm.toLinearMap := by
          change Submodule.span ℂ (Set.range (e.symm.toLinearMap ∘ charFn (F := F) (Idx := Idx))) =
            (Submodule.span ℂ (Set.range (charFn (F := F) (Idx := Idx)))).map e.symm.toLinearMap
          rw [Set.range_comp, Submodule.span_image]
    _ = ⊤ := by simp [hspan]

omit [Nonempty Idx] in
private lemma normalizedCharLp_span_top :
    Submodule.span ℂ (Set.range (normalizedCharLp (F := F) (Idx := Idx))) = ⊤ := by
  have hsqrt0 : (Real.sqrt (Fintype.card (Vec F Idx)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 card_vec_pos))
  let u : Vec F Idx → ℂˣ := fun _ =>
    Units.mk0 ((Real.sqrt (Fintype.card (Vec F Idx)) : ℂ)⁻¹) (inv_ne_zero hsqrt0)
  have hu : u • (fun α : Vec F Idx => WithLp.toLp 2 (charFn α)) =
      normalizedCharLp (F := F) (Idx := Idx) := by
    funext α
    simp [normalizedCharLp, u]
  rw [← hu]
  exact Module.Basis.units_smul_span_eq_top
    (toLp_charFn_span_top (F := F) (Idx := Idx))

lemma parseval_identity (g : ComplexFn F Idx) :
    ∑ α, ‖fourierCoeff g α‖ ^ 2 = fnNormSq g := by
  classical
  let b : OrthonormalBasis (Vec F Idx) ℂ (PiLp 2 fun _ : Vec F Idx => ℂ) :=
    OrthonormalBasis.mk (normalizedCharLp_orthonormal (F := F) (Idx := Idx))
      (normalizedCharLp_span_top (F := F) (Idx := Idx)).ge
  have hb : ∑ α, ‖inner ℂ (b α) (WithLp.toLp 2 g)‖ ^ 2 = ‖WithLp.toLp 2 g‖ ^ 2 :=
    OrthonormalBasis.sum_sq_norm_inner_right b (WithLp.toLp 2 g)
  have hb' : (Fintype.card (Vec F Idx) : ℝ) * ∑ α, ‖fnInner g (charFn α)‖ ^ 2 =
      ‖WithLp.toLp 2 g‖ ^ 2 := by
    simpa [b, Finset.mul_sum, norm_sq_normalizedCharLp_inner] using hb
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

lemma fourier_plancherel (f g : ComplexFn F Idx) :
    ∑ α, fourierCoeff f α * star (fourierCoeff g α) = fnInner f g := by
  classical
  let b : OrthonormalBasis (Vec F Idx) ℂ (PiLp 2 fun _ : Vec F Idx => ℂ) :=
    OrthonormalBasis.mk (normalizedCharLp_orthonormal (F := F) (Idx := Idx))
      (normalizedCharLp_span_top (F := F) (Idx := Idx)).ge
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
    simpa [b] using hcalc
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

/-- Pointwise Fourier inversion for the character basis `χ_α`. -/
lemma fourier_inversion (g : ComplexFn F Idx) (x : Vec F Idx) :
    g x = ∑ α, fourierCoeff g α * charFn α x := by
  classical
  let b : OrthonormalBasis (Vec F Idx) ℂ (PiLp 2 fun _ : Vec F Idx => ℂ) :=
    OrthonormalBasis.mk (normalizedCharLp_orthonormal (F := F) (Idx := Idx))
      (normalizedCharLp_span_top (F := F) (Idx := Idx)).ge
  have hb := b.sum_repr' (WithLp.toLp 2 g)
  have hpoint := congrArg (fun v : PiLp 2 fun _ : Vec F Idx => ℂ => v x) hb
  calc
    g x = (WithLp.toLp 2 g : PiLp 2 fun _ : Vec F Idx => ℂ) x := rfl
    _ = (∑ α, inner ℂ (b α) (WithLp.toLp 2 g) • b α) x := hpoint.symm
    _ = ∑ α, fourierCoeff g α * charFn α x := by
      simp only [b, OrthonormalBasis.coe_mk, WithLp.ofLp_sum, WithLp.ofLp_smul]
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

omit [DecidableEq F] [DecidableEq Idx] [Nonempty Idx] in
private lemma charFn_eq_baseChar (α : Vec F Idx) (x : Vec F Idx) :
    charFn α x = baseChar (F := F) ⟪α, x⟫ᵥ := by
  rfl

omit [DecidableEq F] [DecidableEq Idx] [Nonempty Idx] in
private lemma charFn_add_apply (α β : Vec F Idx) (x : Vec F Idx) :
    charFn (α + β) x = charFn α x * charFn β x := by
  classical
  rw [charFn_eq_baseChar, charFn_eq_baseChar, charFn_eq_baseChar]
  rw [dotProduct, dotProduct, dotProduct]
  simp [add_mul, Finset.sum_add_distrib, AddChar.map_add_eq_mul]

omit [DecidableEq F] [DecidableEq Idx] [Nonempty Idx] in
private lemma charFn_zero_apply (x : Vec F Idx) :
    charFn (F := F) (Idx := Idx) 0 x = 1 := by
  simp [charFn_eq_baseChar, dotProduct]

omit [DecidableEq F] [DecidableEq Idx] [Nonempty Idx] in
private lemma charFn_mul_arg_apply (γ : Vec F Idx) (a : F) (x : Vec F Idx) :
    charFn γ (fun i => a * x i) = charFn (fun i => a * γ i) x := by
  classical
  rw [charFn_eq_baseChar, charFn_eq_baseChar]
  congr 1
  simp [dotProduct, mul_left_comm, mul_comm]

omit [DecidableEq F] [DecidableEq Idx] [Nonempty Idx] in
private lemma charFn_add_arg_apply (γ : Vec F Idx) (a b : F) (x y : Vec F Idx) :
    charFn γ (fun i => a * x i + b * y i) =
      charFn (fun i => a * γ i) x * charFn (fun i => b * γ i) y := by
  classical
  rw [charFn_eq_baseChar, charFn_eq_baseChar, charFn_eq_baseChar]
  simp [dotProduct, mul_add, Finset.sum_add_distrib, mul_left_comm, mul_comm,
    AddChar.map_add_eq_mul]

omit [Nonempty Idx] in
private lemma expectation_charFn (α : Vec F Idx) :
    expectation (charFn α) = if α = 0 then 1 else 0 := by
  have h := (characters_orthogonal_basis (F := F) (Idx := Idx)).1 α 0
  simpa [fnInner, expectation, charFn_zero_apply] using h

omit [Nonempty Idx] in
private lemma charFn_mul_expectation (α β : Vec F Idx) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      ∑ x : Vec F Idx, charFn α x * charFn β x =
        if α + β = 0 then 1 else 0 := by
  classical
  calc
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, charFn α x * charFn β x =
      expectation (charFn (α + β)) := by
        simp [expectation, charFn_add_apply]
    _ = if α + β = 0 then 1 else 0 := expectation_charFn (α + β)

omit [Nonempty Idx] in
private lemma fourier_sum_mul_char_average (A : Vec F Idx → ℂ) (β : Vec F Idx) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      ∑ x : Vec F Idx, (∑ α : Vec F Idx, A α * charFn α x) * charFn β x =
        A (-β) := by
  classical
  calc
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, (∑ α : Vec F Idx, A α * charFn α x) * charFn β x =
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, ∑ α : Vec F Idx, (A α * charFn α x) * charFn β x := by
        simp [Finset.sum_mul]
    _ = (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ α : Vec F Idx, ∑ x : Vec F Idx, (A α * charFn α x) * charFn β x := by
        rw [Finset.sum_comm]
    _ = ∑ α : Vec F Idx,
        A α * ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          ∑ x : Vec F Idx, charFn α x * charFn β x) := by
        simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = ∑ α : Vec F Idx, A α * (if α + β = 0 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro α _
        rw [charFn_mul_expectation]
    _ = A (-β) := by
        rw [Finset.sum_eq_single (-β)]
        · simp
        · intro α _ hα
          have hneq : α + β ≠ 0 := by
            intro hzero
            exact hα (add_eq_zero_iff_eq_neg.mp hzero)
          simp [hneq]
        · intro hnot
          simp at hnot

omit [Field F] [DecidableEq F] [Nonempty Idx] in
private lemma double_vec_average_left_factor (A : Vec F Idx → ℂ)
    (K : Vec F Idx → Vec F Idx → ℂ) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, ∑ y : Vec F Idx, A x * K x y =
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx,
          A x * ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            ∑ y : Vec F Idx, K x y) := by
  classical
  calc
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          ∑ x : Vec F Idx, ∑ y : Vec F Idx, A x * K x y =
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx,
          (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            ∑ y : Vec F Idx, A x * K x y := by
        simp [Finset.mul_sum, mul_assoc]
    _ = (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx,
          A x * ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            ∑ y : Vec F Idx, K x y) := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        calc
          (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              ∑ y : Vec F Idx, A x * K x y =
            ∑ y : Vec F Idx,
              (Fintype.card (Vec F Idx) : ℂ)⁻¹ * (A x * K x y) := by
              rw [Finset.mul_sum]
          _ = ∑ y : Vec F Idx,
              A x * ((Fintype.card (Vec F Idx) : ℂ)⁻¹ * K x y) := by
              apply Finset.sum_congr rfl
              intro y _
              ring
          _ = A x * ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              ∑ y : Vec F Idx, K x y) := by
              rw [Finset.mul_sum, Finset.mul_sum]

omit [Nonempty Idx] in
private lemma y_average_fourier_char_product (B C : Vec F Idx → ℂ) (a b : F)
    (x : Vec F Idx) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      ∑ y : Vec F Idx,
        (∑ β : Vec F Idx, B β * charFn β y) *
          (∑ γ : Vec F Idx,
            C γ * charFn (fun i => a * γ i) x *
              charFn (fun i => b * γ i) y) =
      ∑ γ : Vec F Idx,
        C γ * charFn (fun i => a * γ i) x *
          B (fun i => -b * γ i) := by
  classical
  calc
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ y : Vec F Idx,
          (∑ β : Vec F Idx, B β * charFn β y) *
            (∑ γ : Vec F Idx,
              C γ * charFn (fun i => a * γ i) x *
                charFn (fun i => b * γ i) y) =
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ y : Vec F Idx, ∑ γ : Vec F Idx,
          (C γ * charFn (fun i => a * γ i) x) *
            ((∑ β : Vec F Idx, B β * charFn β y) *
              charFn (fun i => b * γ i) y) := by
        congr 1
        apply Finset.sum_congr rfl
        intro y _
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro γ _
        ring
    _ = (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ γ : Vec F Idx, ∑ y : Vec F Idx,
          (C γ * charFn (fun i => a * γ i) x) *
            ((∑ β : Vec F Idx, B β * charFn β y) *
              charFn (fun i => b * γ i) y) := by
        rw [Finset.sum_comm]
    _ = ∑ γ : Vec F Idx,
        (C γ * charFn (fun i => a * γ i) x) *
          ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            ∑ y : Vec F Idx,
              (∑ β : Vec F Idx, B β * charFn β y) *
                charFn (fun i => b * γ i) y) := by
        simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = ∑ γ : Vec F Idx,
        C γ * charFn (fun i => a * γ i) x *
          B (fun i => -b * γ i) := by
        apply Finset.sum_congr rfl
        intro γ _
        rw [fourier_sum_mul_char_average]
        have hγ : -(fun i => b * γ i) = fun i => -b * γ i := by
          ext i
          simp
        rw [hγ]

omit [Nonempty Idx] in
private lemma x_average_fourier_char_product (A B C : Vec F Idx → ℂ) (a b : F) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      ∑ x : Vec F Idx,
        (∑ α : Vec F Idx, A α * charFn α x) *
          (∑ γ : Vec F Idx,
            C γ * charFn (fun i => a * γ i) x *
              B (fun i => -b * γ i)) =
      ∑ γ : Vec F Idx,
        A (fun i => -a * γ i) * B (fun i => -b * γ i) * C γ := by
  classical
  calc
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx,
          (∑ α : Vec F Idx, A α * charFn α x) *
            (∑ γ : Vec F Idx,
              C γ * charFn (fun i => a * γ i) x *
                B (fun i => -b * γ i)) =
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, ∑ γ : Vec F Idx,
          (C γ * B (fun i => -b * γ i)) *
            ((∑ α : Vec F Idx, A α * charFn α x) *
              charFn (fun i => a * γ i) x) := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro γ _
        ring
    _ = (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ γ : Vec F Idx, ∑ x : Vec F Idx,
          (C γ * B (fun i => -b * γ i)) *
            ((∑ α : Vec F Idx, A α * charFn α x) *
              charFn (fun i => a * γ i) x) := by
        rw [Finset.sum_comm]
    _ = ∑ γ : Vec F Idx,
        (C γ * B (fun i => -b * γ i)) *
          ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            ∑ x : Vec F Idx,
              (∑ α : Vec F Idx, A α * charFn α x) *
                charFn (fun i => a * γ i) x) := by
        simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = ∑ γ : Vec F Idx,
        A (fun i => -a * γ i) * B (fun i => -b * γ i) * C γ := by
        apply Finset.sum_congr rfl
        intro γ _
        rw [fourier_sum_mul_char_average]
        have haγ : -(fun i => a * γ i) = fun i => -a * γ i := by
          ext i
          simp
        rw [haγ]
        ring

omit [Nonempty Idx] in
private lemma triple_char_average (A B C : Vec F Idx → ℂ) (a b : F) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, ∑ y : Vec F Idx,
          (∑ α : Vec F Idx, A α * charFn α x) *
            (∑ β : Vec F Idx, B β * charFn β y) *
              (∑ γ : Vec F Idx, C γ * charFn γ (fun i => a * x i + b * y i)) =
      ∑ γ : Vec F Idx, A (fun i => -a * γ i) * B (fun i => -b * γ i) * C γ := by
  classical
  calc
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          ∑ x : Vec F Idx, ∑ y : Vec F Idx,
            (∑ α : Vec F Idx, A α * charFn α x) *
              (∑ β : Vec F Idx, B β * charFn β y) *
                (∑ γ : Vec F Idx, C γ * charFn γ (fun i => a * x i + b * y i)) =
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, (∑ α : Vec F Idx, A α * charFn α x) *
          ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            ∑ y : Vec F Idx,
              (∑ β : Vec F Idx, B β * charFn β y) *
                (∑ γ : Vec F Idx,
                  C γ * charFn (fun i => a * γ i) x *
                    charFn (fun i => b * γ i) y)) := by
        let Ax : Vec F Idx → ℂ := fun x =>
          ∑ α : Vec F Idx, A α * charFn α x
        let K : Vec F Idx → Vec F Idx → ℂ := fun x y =>
          (∑ β : Vec F Idx, B β * charFn β y) *
            (∑ γ : Vec F Idx,
              C γ * charFn (fun i => a * γ i) x *
                charFn (fun i => b * γ i) y)
        have hterm :
            ∀ x y : Vec F Idx,
              (∑ α : Vec F Idx, A α * charFn α x) *
                  (∑ β : Vec F Idx, B β * charFn β y) *
                    (∑ γ : Vec F Idx,
                      C γ * charFn γ (fun i => a * x i + b * y i)) =
                Ax x * K x y := by
          intro x y
          dsimp [Ax, K]
          have hsum :
              (∑ γ : Vec F Idx,
                C γ * charFn γ (fun i => a * x i + b * y i)) =
              ∑ γ : Vec F Idx,
                C γ * charFn (fun i => a * γ i) x *
                  charFn (fun i => b * γ i) y := by
            apply Finset.sum_congr rfl
            intro γ _
            rw [charFn_add_arg_apply]
            ring
          rw [hsum]
          ring
        calc
          (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                ∑ x : Vec F Idx, ∑ y : Vec F Idx,
                  (∑ α : Vec F Idx, A α * charFn α x) *
                    (∑ β : Vec F Idx, B β * charFn β y) *
                      (∑ γ : Vec F Idx,
                        C γ * charFn γ (fun i => a * x i + b * y i)) =
            (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                ∑ x : Vec F Idx, ∑ y : Vec F Idx, Ax x * K x y := by
              have hsum :
                  (∑ x : Vec F Idx, ∑ y : Vec F Idx,
                    (∑ α : Vec F Idx, A α * charFn α x) *
                      (∑ β : Vec F Idx, B β * charFn β y) *
                        (∑ γ : Vec F Idx,
                          C γ * charFn γ (fun i => a * x i + b * y i))) =
                  ∑ x : Vec F Idx, ∑ y : Vec F Idx, Ax x * K x y := by
                apply Finset.sum_congr rfl
                intro x _
                apply Finset.sum_congr rfl
                intro y _
                exact hterm x y
              rw [hsum]
          _ = (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              ∑ x : Vec F Idx, Ax x *
                ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                  ∑ y : Vec F Idx, K x y) := by
              rw [double_vec_average_left_factor]
          _ = (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              ∑ x : Vec F Idx,
                (∑ α : Vec F Idx, A α * charFn α x) *
                  ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                    ∑ y : Vec F Idx,
                      (∑ β : Vec F Idx, B β * charFn β y) *
                        (∑ γ : Vec F Idx,
                          C γ * charFn (fun i => a * γ i) x *
                            charFn (fun i => b * γ i) y)) := by
              rfl
    _ = (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, (∑ α : Vec F Idx, A α * charFn α x) *
          (∑ γ : Vec F Idx, C γ * charFn (fun i => a * γ i) x *
            B (fun i => -b * γ i)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        rw [y_average_fourier_char_product]
    _ = ∑ γ : Vec F Idx, A (fun i => -a * γ i) * B (fun i => -b * γ i) * C γ := by
        rw [x_average_fourier_char_product]

private lemma agreement_probability_eq_phase_inner (f g : ScalarFn F Idx) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, (if f x = g x then (1 : ℂ) else 0) =
      (Fintype.card F : ℂ)⁻¹ *
        (1 + ∑ c ∈ (nonzeroScalars (F := F)),
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
            (1 + ∑ c ∈ (nonzeroScalars (F := F)),
              baseChar (F := F) (c * (f x - g x)))) := by
        congr 2
        apply Finset.sum_congr rfl
        intro x _
        rw [sum_univ_eq_zero_add_sum_nonzero]
        simp [baseChar]
    _ = (Fintype.card F : ℂ)⁻¹ *
        (1 + ∑ c ∈ (nonzeroScalars (F := F)),
          fnInner (phaseLift f c) (phaseLift g c)) := by
        congr 1
        calc
          (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              ∑ x : Vec F Idx,
                (1 + ∑ c ∈ (nonzeroScalars (F := F)),
                  baseChar (F := F) (c * (f x - g x))) =
            1 + (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              ∑ x : Vec F Idx, ∑ c ∈ (nonzeroScalars (F := F)),
                baseChar (F := F) (c * (f x - g x)) := by
              simp [Finset.sum_add_distrib, mul_add, Finset.mul_sum]
          _ = 1 + (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              ∑ c ∈ (nonzeroScalars (F := F)), ∑ x : Vec F Idx,
                baseChar (F := F) (c * (f x - g x)) := by
              rw [Finset.sum_comm]
          _ = 1 + ∑ c ∈ (nonzeroScalars (F := F)),
              (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                ∑ x : Vec F Idx, baseChar (F := F) (c * (f x - g x)) := by
              rw [Finset.mul_sum]
          _ = 1 + ∑ c ∈ (nonzeroScalars (F := F)),
              fnInner (phaseLift f c) (phaseLift g c) := by
              congr 1
              apply Finset.sum_congr rfl
              intro c _
              rw [fnInner_phaseLift_eq_character_average]

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

private lemma distance_eq_one_sub_agreement_real (f g : ScalarFn F Idx) :
    distance f g =
      1 - (Fintype.card (Vec F Idx) : Real)⁻¹ *
        ∑ x : Vec F Idx, (if f x = g x then (1 : Real) else 0) := by
  classical
  calc
    distance f g =
      (Fintype.card (Vec F Idx) : Real)⁻¹ *
        ∑ x : Vec F Idx, (if f x ≠ g x then (1 : Real) else 0) := by
        simp [distance]
    _ = (Fintype.card (Vec F Idx) : Real)⁻¹ *
        ∑ x : Vec F Idx, (1 - (if f x = g x then (1 : Real) else 0)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : f x = g x <;> simp [hx]
    _ = 1 - (Fintype.card (Vec F Idx) : Real)⁻¹ *
        ∑ x : Vec F Idx, (if f x = g x then (1 : Real) else 0) := by
        simp [Finset.sum_sub_distrib, mul_sub]

omit [Nonempty Idx] in
private lemma agreement_sum_linearFn_eq_count (f : ScalarFn F Idx) (α : Vec F Idx) :
    (∑ x : Vec F Idx, (if f x = linearFn α x then (1 : Real) else 0)) =
      (agreementCount f α : Real) := by
  classical
  simp [agreementCount]

/-- Relative Hamming distance in terms of the Fourier coefficients of the
nonzero phase lifts of `f` and `g`. -/
lemma distance_formula_via_phase_fourier_coefficients (f g : ScalarFn F Idx) :
    (distance f g : ℂ) =
      1 - (Fintype.card F : ℂ)⁻¹ *
        (1 + ∑ c ∈ (nonzeroScalars (F := F)), ∑ α : Vec F Idx,
          (phaseLift f c)̂(α) * star ((phaseLift g c)̂(α))) := by
  calc
    (distance f g : ℂ) =
      1 - (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, (if f x = g x then (1 : ℂ) else 0) := by
        rw [distance_eq_one_sub_agreement]
    _ = 1 - (Fintype.card F : ℂ)⁻¹ *
        (1 + ∑ c ∈ (nonzeroScalars (F := F)),
          fnInner (phaseLift f c) (phaseLift g c)) := by
        rw [agreement_probability_eq_phase_inner]
    _ = 1 - (Fintype.card F : ℂ)⁻¹ *
        (1 + ∑ c ∈ (nonzeroScalars (F := F)), ∑ α : Vec F Idx,
          (phaseLift f c)̂(α) * star ((phaseLift g c)̂(α))) := by
        congr 2
        congr 1
        apply Finset.sum_congr rfl
        intro c _
        rw [← fourier_plancherel (phaseLift f c) (phaseLift g c)]

/-- The Fourier score of `f` against the linear function `ℓ_α`. -/
noncomputable def linearFourierScore (f : ScalarFn F Idx) (α : Vec F Idx) : ℂ :=
  ∑ c ∈ (nonzeroScalars (F := F)), (phaseLift f c)̂(fun i => c * α i)

private noncomputable def blrPhaseTerm (f : ScalarFn F Idx) (a b c : F)
    (x y : Vec F Idx) : ℂ :=
  phaseLift f (c * a) x * phaseLift f (c * b) y *
    phaseLift f (-c) (fun i => a * x i + b * y i)

omit [DecidableEq F] [Fintype Idx] [DecidableEq Idx] [Nonempty Idx] in
private lemma blrPhaseTerm_eq_baseChar (f : ScalarFn F Idx) (a b c : F)
    (x y : Vec F Idx) :
    blrPhaseTerm f a b c x y =
      baseChar (F := F)
        (c * (a * f x + b * f y - f (fun i => a * x i + b * y i))) := by
  classical
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  letI : NeZero (ringChar F) := ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  let ψ : AddChar F ℂ := baseChar (F := F)
  calc
    blrPhaseTerm f a b c x y =
        ψ (c * a * f x) * ψ (c * b * f y) *
          ψ ((-c) * f (fun i => a * x i + b * y i)) := by
          simp [blrPhaseTerm, phaseLift, baseChar, ψ]
    _ = ψ (c * a * f x + c * b * f y + (-c) *
          f (fun i => a * x i + b * y i)) := by
          rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    _ = ψ (c * (a * f x + b * f y - f (fun i => a * x i + b * y i))) := by
          ring_nf
    _ = baseChar (F := F)
        (c * (a * f x + b * f y - f (fun i => a * x i + b * y i))) := rfl

omit [Fintype Idx] [DecidableEq Idx] [Nonempty Idx] in
private lemma BLRAcceptsAt_indicator_eq_phase_sum (f : ScalarFn F Idx)
    (a b : F) (x y : Vec F Idx) :
    (if a * f x + b * f y = f (fun i => a * x i + b * y i) then (1 : ℂ) else 0) =
      (Fintype.card F : ℂ)⁻¹ *
        (1 + ∑ c ∈ (nonzeroScalars (F := F)), blrPhaseTerm f a b c x y) := by
  classical
  rw [character_sum_indicator_eq (a * f x + b * f y)
    (f (fun i => a * x i + b * y i))]
  rw [sum_univ_eq_zero_add_sum_nonzero]
  congr 1
  simp [blrPhaseTerm_eq_baseChar]

private lemma blrPhaseTerm_xy_average (f : ScalarFn F Idx) (a b c : F) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, ∑ y : Vec F Idx, blrPhaseTerm f a b c x y =
      ∑ γ : Vec F Idx,
        (phaseLift f (c * a))̂(fun i => -a * γ i) *
          (phaseLift f (c * b))̂(fun i => -b * γ i) *
            (phaseLift f (-c))̂(γ) := by
  classical
  let A : Vec F Idx → ℂ := fun α => (phaseLift f (c * a))̂(α)
  let B : Vec F Idx → ℂ := fun β => (phaseLift f (c * b))̂(β)
  let C : Vec F Idx → ℂ := fun γ => (phaseLift f (-c))̂(γ)
  have hsum :
      (∑ x : Vec F Idx, ∑ y : Vec F Idx, blrPhaseTerm f a b c x y) =
      ∑ x : Vec F Idx, ∑ y : Vec F Idx,
        (∑ α : Vec F Idx, A α * charFn α x) *
          (∑ β : Vec F Idx, B β * charFn β y) *
            (∑ γ : Vec F Idx, C γ *
              charFn γ (fun i => a * x i + b * y i)) := by
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    dsimp [blrPhaseTerm, A, B, C]
    rw [fourier_inversion (phaseLift f (c * a)) x]
    rw [fourier_inversion (phaseLift f (c * b)) y]
    rw [fourier_inversion (phaseLift f (-c)) (fun i => a * x i + b * y i)]
  rw [hsum]
  simpa [A, B, C] using
    (triple_char_average (F := F) (Idx := Idx) A B C a b)

private noncomputable def phaseLinearCoeff (f : ScalarFn F Idx) (d : F)
    (η : Vec F Idx) : ℂ :=
  (phaseLift f d)̂(fun i => d * η i)

omit [Nonempty Idx] in
private lemma linearFourierScore_eq_phaseLinearCoeff (f : ScalarFn F Idx)
    (η : Vec F Idx) :
    linearFourierScore f η =
      ∑ d ∈ (nonzeroScalars (F := F)), phaseLinearCoeff f d η := by
  rfl

omit [Fintype F] [DecidableEq F] [Fintype Idx] [DecidableEq Idx] [Nonempty Idx] in
private lemma vec_mul_left_bijective (d : F) (hd : d ≠ 0) :
    Function.Bijective (fun η : Vec F Idx => fun i => d * η i) := by
  constructor
  · intro η θ hηθ
    ext i
    exact mul_left_cancel₀ hd (congrFun hηθ i)
  · intro η
    refine ⟨fun i => d⁻¹ * η i, ?_⟩
    ext i
    simp [hd]

omit [DecidableEq F] [Nonempty Idx] in
private lemma sum_vec_mul_left (d : F) (hd : d ≠ 0)
    (H : Vec F Idx → ℂ) :
    ∑ η : Vec F Idx, H (fun i => d * η i) =
      ∑ η : Vec F Idx, H η := by
  exact (vec_mul_left_bijective (F := F) (Idx := Idx) d hd).sum_comp H

omit [DecidableEq F] [Nonempty Idx] in
private lemma sum_vec_mul_left_real (d : F) (hd : d ≠ 0)
    (H : Vec F Idx → ℝ) :
    ∑ η : Vec F Idx, H (fun i => d * η i) =
      ∑ η : Vec F Idx, H η := by
  exact (vec_mul_left_bijective (F := F) (Idx := Idx) d hd).sum_comp H

private lemma sum_nonzero_mul_left (d : F) (hd : d ≠ 0) (H : F → ℂ) :
    ∑ a ∈ (nonzeroScalars (F := F)), H (d * a) =
      ∑ e ∈ (nonzeroScalars (F := F)), H e := by
  classical
  refine Finset.sum_bijective (s := nonzeroScalars (F := F))
    (t := nonzeroScalars (F := F)) (fun a => d * a) (mulLeft_bijective₀ d hd) ?_ ?_
  · intro a
    simp [nonzeroScalars, hd]
  · intro a _
    rfl

private lemma sum_nonzero_neg (H : F → ℂ) :
    ∑ c ∈ (nonzeroScalars (F := F)), H (-c) =
      ∑ d ∈ (nonzeroScalars (F := F)), H d := by
  classical
  have hbij : Function.Bijective (fun c : F => -c) := by
    constructor
    · intro a b hab
      exact neg_inj.mp hab
    · intro a
      exact ⟨-a, by simp⟩
  refine Finset.sum_bijective (s := nonzeroScalars (F := F))
    (t := nonzeroScalars (F := F)) (fun c : F => -c) hbij ?_ ?_
  · intro c
    simp [nonzeroScalars]
  · intro c _
    rfl

omit [DecidableEq F] [Fintype Idx] [DecidableEq Idx] [Nonempty Idx] in
private lemma phaseLift_norm (f : ScalarFn F Idx) (c : F) (x : Vec F Idx) :
    ‖phaseLift f c x‖ = 1 := by
  classical
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  letI : NeZero (ringChar F) := ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  let ψ : AddChar F ℂ := baseChar (F := F)
  have hphase : phaseLift f c x = ψ (c * f x) := by
    simp [phaseLift, baseChar, ψ]
  rw [hphase]
  exact AddChar.norm_apply ψ (c * f x)

omit [DecidableEq F] in
private lemma fnNormSq_phaseLift (f : ScalarFn F Idx) (c : F) :
    fnNormSq (phaseLift f c) = 1 := by
  classical
  unfold fnNormSq
  simp [phaseLift_norm]

private lemma sum_norm_sq_phaseLinearCoeff (f : ScalarFn F Idx) {c : F}
    (hc : c ≠ 0) :
    ∑ α : Vec F Idx, ‖phaseLinearCoeff f c α‖ ^ 2 = 1 := by
  classical
  calc
    ∑ α : Vec F Idx, ‖phaseLinearCoeff f c α‖ ^ 2 =
        ∑ β : Vec F Idx, ‖(phaseLift f c)̂(β)‖ ^ 2 := by
          dsimp [phaseLinearCoeff]
          rw [sum_vec_mul_left_real (F := F) (Idx := Idx) c hc
            (fun β : Vec F Idx => ‖(phaseLift f c)̂(β)‖ ^ 2)]
    _ = fnNormSq (phaseLift f c) :=
        parseval_identity (F := F) (Idx := Idx) (phaseLift f c)
    _ = 1 := fnNormSq_phaseLift (F := F) (Idx := Idx) f c

omit [Nonempty Idx] in
private lemma norm_sq_linearFourierScore_le_card_mul_sum_norm_sq
    (f : ScalarFn F Idx) (α : Vec F Idx) :
    ‖linearFourierScore f α‖ ^ 2 ≤
      ((nonzeroScalars (F := F)).card : ℝ) *
        ∑ c ∈ (nonzeroScalars (F := F)), ‖phaseLinearCoeff f c α‖ ^ 2 := by
  classical
  let nz := nonzeroScalars (F := F)
  let A : F → ℂ := fun c => phaseLinearCoeff f c α
  have hnorm :
      ‖linearFourierScore f α‖ ≤ ∑ c ∈ nz, ‖A c‖ := by
    rw [linearFourierScore_eq_phaseLinearCoeff]
    dsimp [A, nz]
    exact norm_sum_le _ _
  have hsq :
      ‖linearFourierScore f α‖ ^ 2 ≤ (∑ c ∈ nz, ‖A c‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (Finset.sum_nonneg fun c _ => norm_nonneg (A c))).2 hnorm
  have hsq_norms :
      (∑ c ∈ nz, ‖A c‖) ^ 2 ≤
        (nz.card : ℝ) * ∑ c ∈ nz, ‖A c‖ ^ 2 := by
    simpa [nz, A] using
      (sq_sum_le_card_mul_sum_sq (s := nz) (f := fun c : F => ‖A c‖))
  exact hsq.trans hsq_norms

/-- The squared linear Fourier scores have total mass at most `(q - 1)^2`. -/
lemma linearFourierScore_norm_sq_sum_le (f : ScalarFn F Idx) :
    ∑ α : Vec F Idx, ‖linearFourierScore f α‖ ^ 2 ≤
      ((nonzeroScalars (F := F)).card : ℝ) ^ 2 := by
  classical
  let nz := nonzeroScalars (F := F)
  calc
    ∑ α : Vec F Idx, ‖linearFourierScore f α‖ ^ 2 ≤
        ∑ α : Vec F Idx,
          (nz.card : ℝ) * ∑ c ∈ nz, ‖phaseLinearCoeff f c α‖ ^ 2 := by
          exact Finset.sum_le_sum fun α _ =>
            norm_sq_linearFourierScore_le_card_mul_sum_norm_sq
              (F := F) (Idx := Idx) f α
    _ = (nz.card : ℝ) *
        ∑ α : Vec F Idx, ∑ c ∈ nz, ‖phaseLinearCoeff f c α‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = (nz.card : ℝ) *
        ∑ c ∈ nz, ∑ α : Vec F Idx, ‖phaseLinearCoeff f c α‖ ^ 2 := by
        congr 1
        rw [Finset.sum_comm]
    _ = (nz.card : ℝ) * ∑ c ∈ nz, (1 : ℝ) := by
        congr 1
        apply Finset.sum_congr rfl
        intro c hc
        have hc0 : c ≠ 0 := by
          simpa [nz, nonzeroScalars] using hc
        exact sum_norm_sq_phaseLinearCoeff (F := F) (Idx := Idx) f hc0
    _ = ((nonzeroScalars (F := F)).card : ℝ) ^ 2 := by
        simp [nz, pow_two]

private lemma blrPhaseTerm_xy_average_reindexed (f : ScalarFn F Idx)
    (a b c : F) (hc : c ≠ 0) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, ∑ y : Vec F Idx, blrPhaseTerm f a b c x y =
      ∑ η : Vec F Idx,
        phaseLinearCoeff f (c * a) η *
          phaseLinearCoeff f (c * b) η *
            phaseLinearCoeff f (-c) η := by
  classical
  rw [blrPhaseTerm_xy_average]
  let P : Vec F Idx → ℂ := fun γ =>
    (phaseLift f (c * a))̂(fun i => -a * γ i) *
      (phaseLift f (c * b))̂(fun i => -b * γ i) *
        (phaseLift f (-c))̂(γ)
  have hmul :
      ∑ γ : Vec F Idx, P γ =
        ∑ η : Vec F Idx, P (fun i => (-c) * η i) := by
    exact (sum_vec_mul_left (F := F) (Idx := Idx) (-c) (neg_ne_zero.mpr hc) P).symm
  rw [show (∑ γ : Vec F Idx,
        (phaseLift f (c * a))̂(fun i => -a * γ i) *
          (phaseLift f (c * b))̂(fun i => -b * γ i) *
            (phaseLift f (-c))̂(γ)) = ∑ γ : Vec F Idx, P γ by rfl]
  rw [hmul]
  apply Finset.sum_congr rfl
  intro η _
  dsimp [P, phaseLinearCoeff]
  have hleftA :
      (fun i => -a * ((-c) * η i)) = fun i => (c * a) * η i := by
    ext i
    ring
  have hleftB :
      (fun i => -b * ((-c) * η i)) = fun i => (c * b) * η i := by
    ext i
    ring
  rw [hleftA, hleftB]

private lemma xy_average_one_add_blrPhaseTerm_sum (f : ScalarFn F Idx)
    (a b : F) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, ∑ y : Vec F Idx,
          (1 + ∑ c ∈ (nonzeroScalars (F := F)), blrPhaseTerm f a b c x y) =
      1 + ∑ c ∈ (nonzeroScalars (F := F)), ∑ η : Vec F Idx,
        phaseLinearCoeff f (c * a) η *
          phaseLinearCoeff f (c * b) η *
            phaseLinearCoeff f (-c) η := by
  classical
  have hvec : (Fintype.card (Vec F Idx) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          ∑ x : Vec F Idx, ∑ y : Vec F Idx,
            (1 + ∑ c ∈ (nonzeroScalars (F := F)), blrPhaseTerm f a b c x y) =
      1 + (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          ∑ x : Vec F Idx, ∑ y : Vec F Idx,
            ∑ c ∈ (nonzeroScalars (F := F)), blrPhaseTerm f a b c x y := by
        simp [Finset.sum_add_distrib, mul_add, Finset.mul_sum, mul_assoc]
    _ = 1 + ∑ c ∈ (nonzeroScalars (F := F)),
        ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            ∑ x : Vec F Idx, ∑ y : Vec F Idx, blrPhaseTerm f a b c x y) := by
        congr 1
        calc
          (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                ∑ x : Vec F Idx, ∑ y : Vec F Idx,
                  ∑ c ∈ (nonzeroScalars (F := F)), blrPhaseTerm f a b c x y =
            (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                ∑ c ∈ (nonzeroScalars (F := F)), ∑ x : Vec F Idx,
                  ∑ y : Vec F Idx, blrPhaseTerm f a b c x y := by
              have hsum :
                  (∑ x : Vec F Idx, ∑ y : Vec F Idx,
                      ∑ c ∈ (nonzeroScalars (F := F)), blrPhaseTerm f a b c x y) =
                    ∑ c ∈ (nonzeroScalars (F := F)), ∑ x : Vec F Idx,
                      ∑ y : Vec F Idx, blrPhaseTerm f a b c x y := by
                calc
                  (∑ x : Vec F Idx, ∑ y : Vec F Idx,
                      ∑ c ∈ (nonzeroScalars (F := F)), blrPhaseTerm f a b c x y) =
                    ∑ x : Vec F Idx, ∑ c ∈ (nonzeroScalars (F := F)),
                      ∑ y : Vec F Idx, blrPhaseTerm f a b c x y := by
                      apply Finset.sum_congr rfl
                      intro x _
                      rw [Finset.sum_comm]
                  _ = ∑ c ∈ (nonzeroScalars (F := F)), ∑ x : Vec F Idx,
                      ∑ y : Vec F Idx, blrPhaseTerm f a b c x y := by
                      rw [Finset.sum_comm]
              rw [hsum]
          _ = ∑ c ∈ (nonzeroScalars (F := F)),
              ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                  ∑ x : Vec F Idx, ∑ y : Vec F Idx, blrPhaseTerm f a b c x y) := by
              rw [Finset.mul_sum]
    _ = 1 + ∑ c ∈ (nonzeroScalars (F := F)), ∑ η : Vec F Idx,
        phaseLinearCoeff f (c * a) η *
          phaseLinearCoeff f (c * b) η *
            phaseLinearCoeff f (-c) η := by
        congr 1
        apply Finset.sum_congr rfl
        intro c hc
        have hc0 : c ≠ 0 := by
          simpa [nonzeroScalars] using hc
        rw [blrPhaseTerm_xy_average_reindexed (F := F) (Idx := Idx) f a b c hc0]

private lemma ab_sum_xy_average_one_add_blrPhaseTerm_sum (f : ScalarFn F Idx) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
          ∑ x : Vec F Idx, ∑ y : Vec F Idx,
            (1 + ∑ c ∈ (nonzeroScalars (F := F)), blrPhaseTerm f a b c x y) =
      ∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
        (1 + ∑ c ∈ (nonzeroScalars (F := F)), ∑ η : Vec F Idx,
          phaseLinearCoeff f (c * a) η *
            phaseLinearCoeff f (c * b) η *
              phaseLinearCoeff f (-c) η) := by
  classical
  calc
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          ∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
            ∑ x : Vec F Idx, ∑ y : Vec F Idx,
              (1 + ∑ c ∈ (nonzeroScalars (F := F)), blrPhaseTerm f a b c x y) =
      ∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
        ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            ∑ x : Vec F Idx, ∑ y : Vec F Idx,
              (1 + ∑ c ∈ (nonzeroScalars (F := F)), blrPhaseTerm f a b c x y)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
    _ = ∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
        (1 + ∑ c ∈ (nonzeroScalars (F := F)), ∑ η : Vec F Idx,
          phaseLinearCoeff f (c * a) η *
            phaseLinearCoeff f (c * b) η *
              phaseLinearCoeff f (-c) η) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [xy_average_one_add_blrPhaseTerm_sum]

omit [Nonempty Idx] in
private lemma ab_average_one_add_phase_triple_sum (f : ScalarFn F Idx) :
    ((nonzeroScalars (F := F)).card : ℂ)⁻¹ *
      ((nonzeroScalars (F := F)).card : ℂ)⁻¹ *
        ∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
          (1 + ∑ c ∈ (nonzeroScalars (F := F)), ∑ η : Vec F Idx,
            phaseLinearCoeff f (c * a) η *
              phaseLinearCoeff f (c * b) η *
                phaseLinearCoeff f (-c) η) =
      1 + ((nonzeroScalars (F := F)).card : ℂ)⁻¹ ^ 2 *
        ∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
          ∑ c ∈ (nonzeroScalars (F := F)), ∑ η : Vec F Idx,
            phaseLinearCoeff f (c * a) η *
              phaseLinearCoeff f (c * b) η *
                phaseLinearCoeff f (-c) η := by
  classical
  let nz : Finset F := nonzeroScalars (F := F)
  let P : F → F → ℂ := fun a b =>
    ∑ c ∈ nz, ∑ η : Vec F Idx,
      phaseLinearCoeff f (c * a) η *
        phaseLinearCoeff f (c * b) η *
          phaseLinearCoeff f (-c) η
  have hnz_nonempty : nz.Nonempty := by
    exact ⟨1, by simp [nz, nonzeroScalars]⟩
  have hnz : (nz.card : ℂ) ≠ 0 := by
    exact_mod_cast hnz_nonempty.card_pos.ne'
  calc
    ((nonzeroScalars (F := F)).card : ℂ)⁻¹ *
        ((nonzeroScalars (F := F)).card : ℂ)⁻¹ *
          ∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
            (1 + ∑ c ∈ (nonzeroScalars (F := F)), ∑ η : Vec F Idx,
              phaseLinearCoeff f (c * a) η *
                phaseLinearCoeff f (c * b) η *
                  phaseLinearCoeff f (-c) η) =
      (nz.card : ℂ)⁻¹ * (nz.card : ℂ)⁻¹ *
        ∑ a ∈ nz, ∑ b ∈ nz, (1 + P a b) := by
        rfl
    _ = 1 + (nz.card : ℂ)⁻¹ ^ 2 *
        ∑ a ∈ nz, ∑ b ∈ nz, P a b := by
        simp [P, Finset.sum_add_distrib, Finset.mul_sum, mul_add, hnz, pow_two,
          mul_assoc, mul_comm]
    _ = 1 + ((nonzeroScalars (F := F)).card : ℂ)⁻¹ ^ 2 *
        ∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
          ∑ c ∈ (nonzeroScalars (F := F)), ∑ η : Vec F Idx,
            phaseLinearCoeff f (c * a) η *
              phaseLinearCoeff f (c * b) η *
                phaseLinearCoeff f (-c) η := by
        rfl

omit [Nonempty Idx] in
private lemma scalar_phase_triple_sum_fixed (f : ScalarFn F Idx) (η : Vec F Idx) :
    (∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
      ∑ c ∈ (nonzeroScalars (F := F)),
        phaseLinearCoeff f (c * a) η *
          phaseLinearCoeff f (c * b) η *
            phaseLinearCoeff f (-c) η) =
      (linearFourierScore f η) ^ 3 := by
  classical
  let L : F → ℂ := fun d => phaseLinearCoeff f d η
  let nz : Finset F := nonzeroScalars (F := F)
  have hscore : linearFourierScore f η = ∑ d ∈ nz, L d := rfl
  calc
    (∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
      ∑ c ∈ (nonzeroScalars (F := F)),
        phaseLinearCoeff f (c * a) η *
          phaseLinearCoeff f (c * b) η *
            phaseLinearCoeff f (-c) η) =
      ∑ a ∈ nz, ∑ b ∈ nz, ∑ c ∈ nz, L (c * a) * L (c * b) * L (-c) := by
        rfl
    _ = ∑ c ∈ nz, ∑ a ∈ nz, ∑ b ∈ nz, L (c * a) * L (c * b) * L (-c) := by
        calc
          (∑ a ∈ nz, ∑ b ∈ nz, ∑ c ∈ nz, L (c * a) * L (c * b) * L (-c)) =
            ∑ a ∈ nz, ∑ c ∈ nz, ∑ b ∈ nz, L (c * a) * L (c * b) * L (-c) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.sum_comm]
          _ = ∑ c ∈ nz, ∑ a ∈ nz, ∑ b ∈ nz, L (c * a) * L (c * b) * L (-c) := by
              rw [Finset.sum_comm]
    _ = ∑ c ∈ nz,
        (∑ d ∈ nz, L d) * (∑ e ∈ nz, L e) * L (-c) := by
        apply Finset.sum_congr rfl
        intro c hc
        have hc0 : c ≠ 0 := by
          simpa [nz, nonzeroScalars] using hc
        calc
          (∑ a ∈ nz, ∑ b ∈ nz, L (c * a) * L (c * b) * L (-c)) =
            (∑ a ∈ nz, L (c * a)) * (∑ b ∈ nz, L (c * b)) * L (-c) := by
              simp [Finset.mul_sum, mul_assoc, mul_comm]
          _ = (∑ d ∈ nz, L d) * (∑ e ∈ nz, L e) * L (-c) := by
              rw [sum_nonzero_mul_left (F := F) c hc0 L]
    _ = (∑ d ∈ nz, L d) ^ 3 := by
        let S : ℂ := ∑ d ∈ nz, L d
        have hneg : (∑ c ∈ nz, L (-c)) = S := by
          dsimp [S]
          rw [sum_nonzero_neg (F := F) L]
        calc
          (∑ c ∈ nz, (∑ d ∈ nz, L d) * (∑ e ∈ nz, L e) * L (-c)) =
            S * S * (∑ c ∈ nz, L (-c)) := by
              rw [Finset.mul_sum]
              rw [Finset.mul_sum]
          _ = S ^ 3 := by
              rw [hneg]
              ring
          _ = (∑ d ∈ nz, L d) ^ 3 := rfl
    _ = (linearFourierScore f η) ^ 3 := by
        rw [hscore]

omit [Nonempty Idx] in
private lemma scalar_phase_triple_sum (f : ScalarFn F Idx) :
    (∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
      ∑ c ∈ (nonzeroScalars (F := F)), ∑ η : Vec F Idx,
        phaseLinearCoeff f (c * a) η *
          phaseLinearCoeff f (c * b) η *
            phaseLinearCoeff f (-c) η) =
      ∑ η : Vec F Idx, (linearFourierScore f η) ^ 3 := by
  classical
  calc
    (∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
      ∑ c ∈ (nonzeroScalars (F := F)), ∑ η : Vec F Idx,
        phaseLinearCoeff f (c * a) η *
          phaseLinearCoeff f (c * b) η *
            phaseLinearCoeff f (-c) η) =
      ∑ η : Vec F Idx, ∑ a ∈ (nonzeroScalars (F := F)),
        ∑ b ∈ (nonzeroScalars (F := F)), ∑ c ∈ (nonzeroScalars (F := F)),
          phaseLinearCoeff f (c * a) η *
            phaseLinearCoeff f (c * b) η *
              phaseLinearCoeff f (-c) η := by
        calc
          (∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
            ∑ c ∈ (nonzeroScalars (F := F)), ∑ η : Vec F Idx,
              phaseLinearCoeff f (c * a) η *
                phaseLinearCoeff f (c * b) η *
                  phaseLinearCoeff f (-c) η) =
            ∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
              ∑ η : Vec F Idx, ∑ c ∈ (nonzeroScalars (F := F)),
                phaseLinearCoeff f (c * a) η *
                  phaseLinearCoeff f (c * b) η *
                    phaseLinearCoeff f (-c) η := by
              apply Finset.sum_congr rfl
              intro a _
              apply Finset.sum_congr rfl
              intro b _
              rw [Finset.sum_comm]
          _ = ∑ a ∈ (nonzeroScalars (F := F)), ∑ η : Vec F Idx,
              ∑ b ∈ (nonzeroScalars (F := F)), ∑ c ∈ (nonzeroScalars (F := F)),
                phaseLinearCoeff f (c * a) η *
                  phaseLinearCoeff f (c * b) η *
                    phaseLinearCoeff f (-c) η := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.sum_comm]
          _ = ∑ η : Vec F Idx, ∑ a ∈ (nonzeroScalars (F := F)),
              ∑ b ∈ (nonzeroScalars (F := F)), ∑ c ∈ (nonzeroScalars (F := F)),
                phaseLinearCoeff f (c * a) η *
                  phaseLinearCoeff f (c * b) η *
                    phaseLinearCoeff f (-c) η := by
              rw [Finset.sum_comm]
    _ = ∑ η : Vec F Idx, (linearFourierScore f η) ^ 3 := by
        apply Finset.sum_congr rfl
        intro η _
        rw [scalar_phase_triple_sum_fixed]

/-- Exact BLR acceptance formula in terms of the Fourier scores
`∑ c∈Fˣ, \widehat{f_c}(cα)`. -/
lemma exact_blr_acceptance_formula (f : ScalarFn F Idx) :
    (acceptanceProbabilityBLR f : ℂ) =
      (Fintype.card F : ℂ)⁻¹ *
        (1 + ((nonzeroScalars (F := F)).card : ℂ)⁻¹ ^ 2 *
          ∑ α : Vec F Idx, (linearFourierScore f α) ^ 3) := by
  classical
  let S : Vec F Idx → ℂ := linearFourierScore f
  change (acceptanceProbabilityBLR f : ℂ) =
      (Fintype.card F : ℂ)⁻¹ *
        (1 + ((nonzeroScalars (F := F)).card : ℂ)⁻¹ ^ 2 *
          ∑ α : Vec F Idx, (S α) ^ 3)
  have haccept :
      (acceptanceProbabilityBLR f : ℂ) =
        ((nonzeroScalars (F := F)).card : ℂ)⁻¹ *
          ((nonzeroScalars (F := F)).card : ℂ)⁻¹ *
            (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                ∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
                  ∑ x : Vec F Idx, ∑ y : Vec F Idx,
                    if BLRAcceptsAt f a b x y then (1 : ℂ) else 0 := by
    simp [acceptanceProbabilityBLR]
  have hindicator :
      (∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
        ∑ x : Vec F Idx, ∑ y : Vec F Idx,
          if BLRAcceptsAt f a b x y then (1 : ℂ) else 0) =
        ∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
          ∑ x : Vec F Idx, ∑ y : Vec F Idx,
            (Fintype.card F : ℂ)⁻¹ *
              (1 + ∑ c ∈ (nonzeroScalars (F := F)), blrPhaseTerm f a b c x y) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [show (if BLRAcceptsAt f a b x y then (1 : ℂ) else 0) =
      (if a * f x + b * f y = f (fun i => a * x i + b * y i) then (1 : ℂ) else 0) by
        simp [BLRAcceptsAt]]
    exact BLRAcceptsAt_indicator_eq_phase_sum (F := F) (Idx := Idx) f a b x y
  calc
    (acceptanceProbabilityBLR f : ℂ) =
      ((nonzeroScalars (F := F)).card : ℂ)⁻¹ *
        ((nonzeroScalars (F := F)).card : ℂ)⁻¹ *
          (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              ∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
                ∑ x : Vec F Idx, ∑ y : Vec F Idx,
                  if BLRAcceptsAt f a b x y then (1 : ℂ) else 0 := haccept
    _ = ((nonzeroScalars (F := F)).card : ℂ)⁻¹ *
        ((nonzeroScalars (F := F)).card : ℂ)⁻¹ *
          (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              ∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
                ∑ x : Vec F Idx, ∑ y : Vec F Idx,
                  (Fintype.card F : ℂ)⁻¹ *
                    (1 + ∑ c ∈ (nonzeroScalars (F := F)),
                      blrPhaseTerm f a b c x y) := by
        rw [hindicator]
    _ = (Fintype.card F : ℂ)⁻¹ *
        (((nonzeroScalars (F := F)).card : ℂ)⁻¹ *
          ((nonzeroScalars (F := F)).card : ℂ)⁻¹ *
            ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                ∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
                  ∑ x : Vec F Idx, ∑ y : Vec F Idx,
                    (1 + ∑ c ∈ (nonzeroScalars (F := F)),
                      blrPhaseTerm f a b c x y))) := by
        simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = (Fintype.card F : ℂ)⁻¹ *
        (((nonzeroScalars (F := F)).card : ℂ)⁻¹ *
          ((nonzeroScalars (F := F)).card : ℂ)⁻¹ *
            ∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
              (1 + ∑ c ∈ (nonzeroScalars (F := F)), ∑ η : Vec F Idx,
                phaseLinearCoeff f (c * a) η *
                  phaseLinearCoeff f (c * b) η *
                    phaseLinearCoeff f (-c) η)) := by
        rw [ab_sum_xy_average_one_add_blrPhaseTerm_sum]
    _ = (Fintype.card F : ℂ)⁻¹ *
        (1 + ((nonzeroScalars (F := F)).card : ℂ)⁻¹ ^ 2 *
          ∑ a ∈ (nonzeroScalars (F := F)), ∑ b ∈ (nonzeroScalars (F := F)),
            ∑ c ∈ (nonzeroScalars (F := F)), ∑ η : Vec F Idx,
              phaseLinearCoeff f (c * a) η *
                phaseLinearCoeff f (c * b) η *
                  phaseLinearCoeff f (-c) η) := by
        rw [ab_average_one_add_phase_triple_sum]
    _ = (Fintype.card F : ℂ)⁻¹ *
        (1 + ((nonzeroScalars (F := F)).card : ℂ)⁻¹ ^ 2 *
          ∑ α : Vec F Idx, (S α) ^ 3) := by
        rw [scalar_phase_triple_sum]

/-- The real part of the Fourier score of `f` against `ℓ_α`. The score is
proved real in `linearFourierScore_im_eq_zero`. -/
noncomputable def linearFourierScoreReal (f : ScalarFn F Idx) (α : Vec F Idx) : Real :=
  (linearFourierScore f α).re

/-- Relative Hamming distance from `f` to the linear function `ℓ_α`, written in
terms of the Fourier coefficients of the nonzero phase lifts of `f`. -/
lemma distance_linearFn_fourier (f : ScalarFn F Idx) (α : Vec F Idx) :
    (distance f (linearFn α) : ℂ) =
      1 - (Fintype.card F : ℂ)⁻¹ * (1 + linearFourierScore f α) := by
  rw [distance_formula_via_phase_fourier_coefficients]
  congr 2
  congr 1
  simp only [linearFourierScore]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_eq_single (fun i => c * α i)]
  · simp [fourierCoeff_phaseLift_linearFn]
  · intro β _ hβ
    rw [fourierCoeff_phaseLift_linearFn]
    simp [hβ]
  · intro hβ
    simp at hβ

/-- The fixed-linear-function Fourier distance formula, with real-valued score. -/
lemma distance_linearFn_fourier_real (f : ScalarFn F Idx) (α : Vec F Idx) :
    distance f (linearFn α) =
      1 - (Fintype.card F : Real)⁻¹ * (1 + linearFourierScoreReal f α) := by
  have h := congrArg Complex.re (distance_linearFn_fourier (F := F) (Idx := Idx) f α)
  simpa [linearFourierScoreReal] using h

omit [Field F] [Nonempty Idx] in
private lemma distance_nonneg (f g : ScalarFn F Idx) : 0 ≤ distance f g := by
  classical
  unfold distance
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun x _ => by
      by_cases hx : f x ≠ g x <;> simp [hx])

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

omit [Field F] [Nonempty Idx] in
private lemma distance_congr_right {f g h : ScalarFn F Idx} (hgh : ∀ x, g x = h x) :
    distance f g = distance f h := by
  classical
  simp [distance, hgh]

omit [Nonempty Idx] in
private lemma distanceToLinear_eq_inf_linearFn (f : ScalarFn F Idx) :
    distanceToLinear f =
      (Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Vec F Idx)).Nonempty)
        fun α => distance f (linearFn α)) := by
  classical
  unfold distanceToLinear
  let linearFns := linearFunctionsFinset (F := F) (Idx := Idx)
  let hlinearFns := linearFunctionsFinset_nonempty (F := F) (Idx := Idx)
  change linearFns.inf' hlinearFns (fun g => distance f g) =
    (Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Vec F Idx)).Nonempty)
      fun α => distance f (linearFn α))
  apply le_antisymm
  · apply Finset.le_inf'
    intro α _
    have hmem : linearFn α ∈ linearFns := by
      simp [linearFns, linearFunctionsFinset, LinearSet, IsLinear]
      exact ⟨α, fun x => rfl⟩
    rw [Finset.inf'_le_iff]
    exact ⟨linearFn α, hmem, le_rfl⟩
  · apply Finset.le_inf'
    intro g hg
    have hg_linear : g ∈ LinearSet (F := F) (Idx := Idx) := by
      simpa [linearFns, linearFunctionsFinset] using hg
    rcases hg_linear with ⟨α, hα⟩
    have hdist : distance f g = distance f (linearFn α) :=
      distance_congr_right (F := F) (Idx := Idx) hα
    have hle :
        (Finset.univ.inf'
          (Finset.univ_nonempty : (Finset.univ : Finset (Vec F Idx)).Nonempty)
          fun α => distance f (linearFn α)) ≤
            distance f (linearFn α) :=
      by
        rw [Finset.inf'_le_iff]
        exact ⟨α, by simp, le_rfl⟩
    simpa [hdist] using hle

private lemma linearFourierScore_eq_card_mul_one_sub_distance (f : ScalarFn F Idx)
    (α : Vec F Idx) :
    linearFourierScore f α =
      (((Fintype.card F : Real) * (1 - distance f (linearFn α)) - 1 : Real) : ℂ) := by
  have hcard0 : (Fintype.card F : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have h := distance_linearFn_fourier (F := F) (Idx := Idx) f α
  have h' :
      (Fintype.card F : ℂ) * (1 - (distance f (linearFn α) : ℂ)) =
        1 + linearFourierScore f α := by
    rw [h]
    field_simp [hcard0]
    ring
  calc
    linearFourierScore f α = (1 + linearFourierScore f α) - 1 := by ring
    _ = (Fintype.card F : ℂ) * (1 - (distance f (linearFn α) : ℂ)) - 1 := by
      rw [← h']
    _ = (((Fintype.card F : Real) * (1 - distance f (linearFn α)) - 1 : Real) : ℂ) := by
      norm_num

lemma linearFourierScore_im_eq_zero (f : ScalarFn F Idx) (α : Vec F Idx) :
    (linearFourierScore f α).im = 0 := by
  rw [linearFourierScore_eq_card_mul_one_sub_distance]
  simp

private lemma linearFourierScore_eq_ofReal_real (f : ScalarFn F Idx)
    (α : Vec F Idx) :
    linearFourierScore f α = (linearFourierScoreReal f α : ℂ) := by
  apply Complex.ext
  · simp [linearFourierScoreReal]
  · simp [linearFourierScoreReal,
      linearFourierScore_im_eq_zero (F := F) (Idx := Idx) f α]

/-- Real-valued form of the exact BLR acceptance formula. -/
lemma exact_blr_acceptance_formula_real (f : ScalarFn F Idx) :
    acceptanceProbabilityBLR f =
      (Fintype.card F : Real)⁻¹ *
        (1 + ((nonzeroScalars (F := F)).card : Real)⁻¹ ^ 2 *
          ∑ α : Vec F Idx, (linearFourierScoreReal f α) ^ 3) := by
  classical
  apply Complex.ofReal_injective
  have hscore :
      (∑ α : Vec F Idx, (linearFourierScore f α) ^ 3) =
        ((∑ α : Vec F Idx, (linearFourierScoreReal f α) ^ 3 : Real) : ℂ) := by
    calc
      (∑ α : Vec F Idx, (linearFourierScore f α) ^ 3) =
          ∑ α : Vec F Idx, ((linearFourierScoreReal f α : ℂ) ^ 3) := by
            apply Finset.sum_congr rfl
            intro α _
            rw [linearFourierScore_eq_ofReal_real]
      _ = ((∑ α : Vec F Idx, (linearFourierScoreReal f α) ^ 3 : Real) : ℂ) := by
            simp
  simpa [hscore] using exact_blr_acceptance_formula (F := F) (Idx := Idx) f

/-- Real form of `linearFourierScore_norm_sq_sum_le`. -/
lemma linearFourierScoreReal_sq_sum_le (f : ScalarFn F Idx) :
    ∑ α : Vec F Idx, (linearFourierScoreReal f α) ^ 2 ≤
      ((nonzeroScalars (F := F)).card : ℝ) ^ 2 := by
  classical
  calc
    ∑ α : Vec F Idx, (linearFourierScoreReal f α) ^ 2 =
        ∑ α : Vec F Idx, ‖linearFourierScore f α‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro α _
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp [linearFourierScoreReal,
            linearFourierScore_im_eq_zero (F := F) (Idx := Idx) f α, pow_two]
    _ ≤ ((nonzeroScalars (F := F)).card : ℝ) ^ 2 :=
        linearFourierScore_norm_sq_sum_le (F := F) (Idx := Idx) f

private lemma linearFourierScoreReal_eq_card_mul_one_sub_distance (f : ScalarFn F Idx)
    (α : Vec F Idx) :
    linearFourierScoreReal f α =
      (Fintype.card F : Real) * (1 - distance f (linearFn α)) - 1 := by
  have h := congrArg Complex.re
    (linearFourierScore_eq_card_mul_one_sub_distance (F := F) (Idx := Idx) f α)
  simpa [linearFourierScoreReal] using h

private lemma linearFourierScoreReal_eq_card_mul_agreement_ratio_sub_one
    (f : ScalarFn F Idx) (α : Vec F Idx) :
    linearFourierScoreReal f α =
      (Fintype.card F : Real) *
        ((Fintype.card (Vec F Idx) : Real)⁻¹ * (agreementCount f α : Real)) - 1 := by
  rw [linearFourierScoreReal_eq_card_mul_one_sub_distance]
  rw [distance_eq_one_sub_agreement_real]
  rw [agreement_sum_linearFn_eq_count]
  ring

omit [DecidableEq F] in
private lemma card_vec_eq_card_field_mul_div :
    Fintype.card (Vec F Idx) =
      Fintype.card F * (Fintype.card (Vec F Idx) / Fintype.card F) := by
  classical
  let q := Fintype.card F
  let m := Fintype.card Idx
  have hq : 1 < q := by
    dsimp [q]
    exact Fintype.one_lt_card
  have hm : 0 < m := by
    dsimp [m]
    exact Fintype.card_pos_iff.mpr inferInstance
  have hcard : Fintype.card (Vec F Idx) = q ^ m := by
    dsimp [q, m]
    simp
  have hdiv : q ^ m / q = q ^ (m - 1) := by
    rw [← Nat.succ_pred_eq_of_pos hm, pow_succ, Nat.succ_sub_one]
    exact Nat.mul_div_left _ (Nat.zero_lt_of_lt hq)
  calc
    Fintype.card (Vec F Idx) = q ^ m := hcard
    _ = q * (q ^ m / q) := by
        rw [hdiv]
        rw [← Nat.succ_pred_eq_of_pos hm, pow_succ, Nat.succ_sub_one]
        rw [mul_comm]
    _ = Fintype.card F * (Fintype.card (Vec F Idx) / Fintype.card F) := by
        simp [q, hcard]

private lemma linearFourierScoreReal_sup_nonneg (f : ScalarFn F Idx) :
    0 ≤ (Finset.univ.sup'
      (Finset.univ_nonempty : (Finset.univ : Finset (Vec F Idx)).Nonempty)
      (linearFourierScoreReal f)) := by
  classical
  rcases exists_agreementCount_ge (F := F) (Idx := Idx) f with ⟨α, hα⟩
  have hscore :=
    linearFourierScoreReal_eq_card_mul_agreement_ratio_sub_one
      (F := F) (Idx := Idx) f α
  have hqpos : 0 < (Fintype.card F : Real) := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hNpos : 0 < (Fintype.card (Vec F Idx) : Real) := by
    exact_mod_cast Fintype.card_pos (α := Vec F Idx)
  have hkpos :
      ((Fintype.card (Vec F Idx) / Fintype.card F : ℕ) : Real) ≠ 0 := by
    exact_mod_cast
      (card_vec_div_card_field_pos (F := F) (Idx := Idx)).ne'
  have hcard_real :
      (Fintype.card (Vec F Idx) : Real) =
        (Fintype.card F : Real) *
          ((Fintype.card (Vec F Idx) / Fintype.card F : ℕ) : Real) := by
    exact_mod_cast card_vec_eq_card_field_mul_div (F := F) (Idx := Idx)
  have hbase :
      (Fintype.card F : Real) *
        ((Fintype.card (Vec F Idx) : Real)⁻¹ *
          ((Fintype.card (Vec F Idx) / Fintype.card F : ℕ) : Real)) = 1 := by
    rw [hcard_real]
    field_simp [hqpos.ne', hkpos]
  have hα_real :
      ((Fintype.card (Vec F Idx) / Fintype.card F : ℕ) : Real) ≤
        (agreementCount f α : Real) := by
    exact_mod_cast hα
  have hagree_ratio :
      1 ≤ (Fintype.card F : Real) *
        ((Fintype.card (Vec F Idx) : Real)⁻¹ * (agreementCount f α : Real)) := by
    calc
      (1 : Real) =
          (Fintype.card F : Real) *
            ((Fintype.card (Vec F Idx) : Real)⁻¹ *
              ((Fintype.card (Vec F Idx) / Fintype.card F : ℕ) : Real)) := hbase.symm
      _ ≤ (Fintype.card F : Real) *
          ((Fintype.card (Vec F Idx) : Real)⁻¹ * (agreementCount f α : Real)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hα_real (inv_nonneg.mpr hNpos.le))
            hqpos.le
  have hαscore_nonneg : 0 ≤ linearFourierScoreReal f α := by
    rw [hscore]
    linarith
  exact hαscore_nonneg.trans
    (Finset.le_sup' (s := (Finset.univ : Finset (Vec F Idx)))
      (f := linearFourierScoreReal f) (by simp))

lemma linearFourierScoreReal_bounds (f : ScalarFn F Idx) (α : Vec F Idx) :
    -1 ≤ linearFourierScoreReal f α ∧
      linearFourierScoreReal f α ≤ (Fintype.card F : Real) - 1 := by
  have hd0 : 0 ≤ distance f (linearFn α) := distance_nonneg (F := F) (Idx := Idx) f (linearFn α)
  have hd1 : distance f (linearFn α) ≤ 1 := distance_le_one (F := F) (Idx := Idx) f (linearFn α)
  have hcard_nonneg : 0 ≤ (Fintype.card F : Real) := Nat.cast_nonneg _
  have hscore :=
    linearFourierScoreReal_eq_card_mul_one_sub_distance (F := F) (Idx := Idx) f α
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
          (linearFourierScoreReal f))) := by
  classical
  rw [distanceToLinear_eq_inf_linearFn]
  let score := linearFourierScoreReal (F := F) (Idx := Idx) f
  let coeffs := (Finset.univ : Finset (Vec F Idx))
  let hcoeffs : coeffs.Nonempty := Finset.univ_nonempty
  let maxScore := coeffs.sup' hcoeffs score
  change coeffs.inf' hcoeffs (fun α => distance f (linearFn α)) =
    1 - (Fintype.card F : Real)⁻¹ * (1 + maxScore)
  apply le_antisymm
  · rcases Finset.exists_mem_eq_sup' (s := coeffs) (H := hcoeffs) score with
      ⟨α, hα_mem, hα_eq⟩
    have hdist := distance_linearFn_fourier_real (F := F) (Idx := Idx) f α
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
    simpa [distance_linearFn_fourier_real (F := F) (Idx := Idx) f α] using hterm

/-- Distance to linearity in Fourier form, together with the realness and
range of each linear Fourier score. -/
lemma distance_to_linearity_fourier (f : ScalarFn F Idx) :
    distanceToLinear f =
        1 - (Fintype.card F : Real)⁻¹ *
          (1 + (Finset.univ.sup'
            (Finset.univ_nonempty : (Finset.univ : Finset (Vec F Idx)).Nonempty)
            (linearFourierScoreReal f))) ∧
      ∀ α : Vec F Idx,
        (linearFourierScore f α).im = 0 ∧
          -1 ≤ linearFourierScoreReal f α ∧
            linearFourierScoreReal f α ≤ (Fintype.card F : Real) - 1 := by
  refine ⟨distanceToLinear_fourier (F := F) (Idx := Idx) f, ?_⟩
  intro α
  exact ⟨linearFourierScore_im_eq_zero (F := F) (Idx := Idx) f α,
    linearFourierScoreReal_bounds (F := F) (Idx := Idx) f α⟩

/-- Soundness of the finite-field BLR test in the Fourier-score form used by
the proof: acceptance is at most `1 - distanceToLinear f`. -/
theorem finite_field_blr_soundness (f : ScalarFn F Idx) :
    acceptanceProbabilityBLR f ≤ 1 - distanceToLinear f := by
  classical
  let nz : Finset F := nonzeroScalars (F := F)
  let coeffs : Finset (Vec F Idx) := Finset.univ
  let score : Vec F Idx → Real := linearFourierScoreReal (F := F) (Idx := Idx) f
  let M : Real := coeffs.sup' (Finset.univ_nonempty :
    (Finset.univ : Finset (Vec F Idx)).Nonempty) score
  have hM_nonneg' : 0 ≤ M := by
    simpa [M, coeffs, score] using
      linearFourierScoreReal_sup_nonneg (F := F) (Idx := Idx) f
  have hnz_nonempty : nz.Nonempty := by
    exact ⟨1, by simp [nz, nonzeroScalars]⟩
  have hnz_pos : 0 < (nz.card : Real) := by
    exact_mod_cast hnz_nonempty.card_pos
  have hnz_sq_ne : (nz.card : Real) ^ 2 ≠ 0 := by
    exact pow_ne_zero _ hnz_pos.ne'
  have hscore_le : ∀ α : Vec F Idx, score α ≤ M := by
    intro α
    exact Finset.le_sup' (s := coeffs) (f := score) (by simp [coeffs])
  have hcube_le :
      ∑ α : Vec F Idx, (score α) ^ 3 ≤
        M * ∑ α : Vec F Idx, (score α) ^ 2 := by
    calc
      ∑ α : Vec F Idx, (score α) ^ 3 ≤
          ∑ α : Vec F Idx, M * (score α) ^ 2 := by
          apply Finset.sum_le_sum
          intro α _
          have hmul :
              score α * (score α) ^ 2 ≤ M * (score α) ^ 2 :=
            mul_le_mul_of_nonneg_right (hscore_le α) (sq_nonneg (score α))
          nlinarith [hmul]
      _ = M * ∑ α : Vec F Idx, (score α) ^ 2 := by
          rw [Finset.mul_sum]
  have hsumsq :
      ∑ α : Vec F Idx, (score α) ^ 2 ≤ (nz.card : Real) ^ 2 := by
    simpa [score, nz] using linearFourierScoreReal_sq_sum_le (F := F) (Idx := Idx) f
  have hcube_le_M :
      ((nz.card : Real)⁻¹ ^ 2) * ∑ α : Vec F Idx, (score α) ^ 3 ≤ M := by
    have hcube_bound :
        ∑ α : Vec F Idx, (score α) ^ 3 ≤ M * (nz.card : Real) ^ 2 :=
      hcube_le.trans (mul_le_mul_of_nonneg_left hsumsq hM_nonneg')
    calc
      ((nz.card : Real)⁻¹ ^ 2) * ∑ α : Vec F Idx, (score α) ^ 3 ≤
          ((nz.card : Real)⁻¹ ^ 2) * (M * (nz.card : Real) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hcube_bound (sq_nonneg _)
      _ = M := by
          field_simp [hnz_sq_ne]
  have hinner :
      1 + ((nz.card : Real)⁻¹ ^ 2) *
          ∑ α : Vec F Idx, (score α) ^ 3 ≤ 1 + M := by
    linarith
  have hq_inv_nonneg : 0 ≤ (Fintype.card F : Real)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  calc
    acceptanceProbabilityBLR f =
        (Fintype.card F : Real)⁻¹ *
          (1 + ((nz.card : Real)⁻¹ ^ 2) *
            ∑ α : Vec F Idx, (score α) ^ 3) := by
          simpa [score, nz] using exact_blr_acceptance_formula_real (F := F) (Idx := Idx) f
    _ ≤ (Fintype.card F : Real)⁻¹ * (1 + M) := by
          exact mul_le_mul_of_nonneg_left hinner hq_inv_nonneg
    _ = 1 - distanceToLinear f := by
          rw [distanceToLinear_fourier (F := F) (Idx := Idx) f]
          simp [M, coeffs, score]

omit [Nonempty Idx] in
private lemma acceptanceProbabilityBLR_nonneg (f : ScalarFn F Idx) :
    0 ≤ acceptanceProbabilityBLR f := by
  classical
  unfold acceptanceProbabilityBLR
  positivity

/-- The finite-field BLR acceptance probability is sandwiched between
completeness for linear functions and the soundness bound from distance to linearity. -/
theorem blr (f : ScalarFn F Idx) :
    linearSetIndicator f ≤ acceptanceProbabilityBLR f ∧
      acceptanceProbabilityBLR f ≤ 1 - distanceToLinear f := by
  constructor
  · unfold linearSetIndicator
    by_cases hf : f ∈ LinearSet (F := F) (Idx := Idx)
    · rw [if_pos hf, blr_completeness (F := F) (Idx := Idx) hf]
    · rw [if_neg hf]
      exact acceptanceProbabilityBLR_nonneg (F := F) (Idx := Idx) f
  · exact finite_field_blr_soundness (F := F) (Idx := Idx) f

end BlrPcp
