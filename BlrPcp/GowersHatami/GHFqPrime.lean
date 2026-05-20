import BlrPcp.FnFiniteFIelds.BLR
import BlrPcp.GowersHatami.GH2
import BlrPcp.GowersHatami.Concrete
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option linter.unusedSectionVars false

/-!

# BLR test as an approximate representation

Lemma `lem:affine-to-approx-rep` from the blueprint section
"Gowers-Hatami for classical BLR" (the `F_q^n` version):

> If `f : F^Idx → F` satisfies `Pr_{a,b,x,y}[f(ax+by) = a·f(x) + b·f(y)] ≥ 1-ε`
> then the phase function `F(x) = ω^{f(x)}` satisfies
> `E_{x,y} Re(conj(F(x) F(y)) · F(x+y)) ≥ 1 - 2(q-1)^2 ε`.
-/

namespace BlrPcp

open scoped BigOperators ComplexConjugate Matrix ComplexOrder
open Finset

variable {F Idx : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]

noncomputable def linearSetIndicator (f : ScalarFn F Idx) : Real :=
  if f ∈ LinearSet (F := F) (Idx := Idx) then 1 else 0

noncomputable def rejectionProbabilityBLR (f : ScalarFn F Idx) : Real :=
  1 - acceptanceProbabilityBLR f

/-- For a finite field `F` of prime cardinality, the algebra map
`ZMod (ringChar F) → F` is bijective: it is injective (a ring hom out of a
field) and both sides have cardinality `p = ringChar F = Fintype.card F`. -/
private lemma algebraMap_bijective_of_prime
    [hp : Fact (Nat.Prime (Fintype.card F))] :
    letI : NeZero (ringChar F) :=
      ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
    letI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
    letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
    Function.Bijective (algebraMap (ZMod (ringChar F)) F) := by
  letI : NeZero (ringChar F) :=
    ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  letI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  refine (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨RingHom.injective _, ?_⟩
  rw [ZMod.card]
  obtain ⟨n, _, hc⟩ := FiniteField.card F (ringChar F)
  exact ((Nat.Prime.pow_eq_iff hp.out).mp hc.symm).1

/-- For a finite field `F` of prime cardinality, the canonical ring iso
`F ≃+* ZMod (ringChar F)` (the inverse of the bijective `algebraMap`).

Used to define `blrChar` directly without `Algebra.trace`. -/
private noncomputable def primeFieldEquivZMod
    [Fact (Nat.Prime (Fintype.card F))] :
    F ≃+* ZMod (ringChar F) :=
  letI : NeZero (ringChar F) :=
    ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  letI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  (RingEquiv.ofBijective _ algebraMap_bijective_of_prime).symm

/-- `algebraMap` and `primeFieldEquivZMod` are mutually inverse: applying
`algebraMap` to `primeFieldEquivZMod k` recovers `k`. -/
private lemma algebraMap_primeFieldEquivZMod
    [Fact (Nat.Prime (Fintype.card F))] (k : F) :
    letI : NeZero (ringChar F) :=
      ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
    letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
    algebraMap (ZMod (ringChar F)) F (primeFieldEquivZMod k) = k :=
  letI : NeZero (ringChar F) :=
    ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  letI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  (RingEquiv.ofBijective _ algebraMap_bijective_of_prime).apply_symm_apply k

/-- The additive character `χ_F : F → ℂ`, defined directly via
`primeFieldEquivZMod` and `ZMod.stdAddChar` — no `Algebra.trace`. -/
private noncomputable def blrChar
    [Fact (Nat.Prime (Fintype.card F))] : AddChar F ℂ :=
  letI : NeZero (ringChar F) :=
    ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  ZMod.stdAddChar.compAddMonoidHom
    (primeFieldEquivZMod (F := F)).toRingHom.toAddMonoidHom

/-- The phase-lifted function `F(x) = ω^{f(x)} = blrChar (f x)`. -/
noncomputable def blrPhase
    [Fact (Nat.Prime (Fintype.card F))]
    (f : ScalarFn F Idx) : ComplexFn F Idx :=
  fun x => blrChar (f x)

private lemma blrPhase_eq_blrChar
    [Fact (Nat.Prime (Fintype.card F))]
    (f : ScalarFn F Idx) (u : Vec F Idx) :
    blrPhase f u = blrChar (F := F) (f u) := rfl

/-- Compatibility: for prime `F`, the algebra trace to `ZMod (ringChar F)`
agrees with `primeFieldEquivZMod`. Both invert `algebraMap`. -/
private lemma trace_eq_primeFieldEquivZMod
    [hp : Fact (Nat.Prime (Fintype.card F))] (k : F) :
    letI : NeZero (ringChar F) :=
      ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
    letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
    Algebra.trace (ZMod (ringChar F)) F k = primeFieldEquivZMod k := by
  letI : NeZero (ringChar F) :=
    ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  letI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  apply (algebraMap (ZMod (ringChar F)) F).injective
  rw [algebraMap_primeFieldEquivZMod]
  -- algebraMap (trace k) = k via FiniteField.algebraMap_trace_eq_sum_pow + finrank=1.
  have hqp : (Fintype.card F).Prime := hp.out
  have hrc : ringChar F = Fintype.card F := by
    obtain ⟨n, _, hc⟩ := FiniteField.card F (ringChar F)
    exact ((Nat.Prime.pow_eq_iff hqp).mp hc.symm).1
  have hcardZ : Fintype.card (ZMod (ringChar F)) = Fintype.card F := by
    rw [ZMod.card, hrc]
  have hpow : Fintype.card F =
      Fintype.card F ^ Module.finrank (ZMod (ringChar F)) F := by
    conv_lhs => rw [Module.card_eq_pow_finrank (K := ZMod (ringChar F)) (V := F),
      hcardZ]
  have hfinrank : Module.finrank (ZMod (ringChar F)) F = 1 :=
    ((Nat.Prime.pow_eq_iff hqp).mp hpow.symm).2
  have h := FiniteField.algebraMap_trace_eq_sum_pow (ZMod (ringChar F)) F k
  rw [hfinrank, Finset.sum_range_one] at h
  simpa using h

/-- The summand is bounded below by `1 - 2 · 1[bad]`, where the bad event is
`f(x+y) ≠ f x + f y`. The summand collapses to the additive character at
`f(x+y) − f x − f y`, which is `1` on the good event and has modulus `1`
(hence real part `≥ −1`) otherwise. -/
private lemma blrPhase_summand_lower
    [Fact (Nat.Prime (Fintype.card F))]
    (f : ScalarFn F Idx) (x y : Vec F Idx) :
    (1 : ℝ) - 2 * (if f (x + y) = f x + f y then (0 : ℝ) else 1) ≤
      ((starRingEnd ℂ) (blrPhase f x * blrPhase f y) * blrPhase f (x + y)).re := by
  have hcorr : (starRingEnd ℂ) (blrPhase f x * blrPhase f y) * blrPhase f (x + y) =
      blrChar (F := F) (f (x + y) - f x - f y) := by
    set ψ : AddChar F ℂ := blrChar (F := F)
    have hstar : ∀ z : F, star (ψ z) = ψ (-z) := fun z => by
      rw [AddChar.map_neg_eq_inv]
      exact (Complex.inv_eq_conj (AddChar.norm_apply ψ z)).symm
    rw [blrPhase_eq_blrChar, blrPhase_eq_blrChar, blrPhase_eq_blrChar,
        starRingEnd_apply, ← AddChar.map_add_eq_mul, hstar,
        ← AddChar.map_add_eq_mul]
    congr 1; ring
  rw [hcorr]
  by_cases hxy : f (x + y) = f x + f y
  · have h0 : f (x + y) - f x - f y = 0 := by linear_combination hxy
    rw [h0, AddChar.map_zero_eq_one]
    simp [hxy]
  · have hnorm : ‖blrChar (F := F) (f (x + y) - f x - f y)‖ = 1 :=
      AddChar.norm_apply _ _
    have habs := Complex.abs_re_le_norm (blrChar (F := F) (f (x + y) - f x - f y))
    rw [hnorm] at habs
    simp only [hxy, if_false, mul_one]
    linarith [(abs_le.mp habs).1]

/-- The bad-pair count is bounded by `(q-1)^2 N^2 ε`. The affine BLR test
samples `(a,b)` uniformly from `(F\{0})^2`, so the event `a = b = 1` has
probability `1/(q-1)^2`, contributing the (linear) bad pairs to the
overall rejection probability.

(See `notes/BlrApproxRep_wrapper-alternative.lean.txt` for an alternative
formulation that introduces a `perPairRejection` helper. The helper makes
the "drop to (1,1)" step structurally cleaner, but the supporting wrapper
lemma re-introduces the K²/N² bookkeeping it was meant to hide, so the net
line count is slightly worse than this direct version.) -/
private lemma badCount_le
    (f : ScalarFn F Idx) (ε : ℝ)
    (hε : rejectionProbabilityBLR f ≤ ε) :
    (∑ x : Vec F Idx, ∑ y : Vec F Idx,
        (if f (x + y) = f x + f y then (0 : ℝ) else 1)) ≤
      ((Fintype.card F : ℝ) - 1) ^ 2 *
        ((Fintype.card (Vec F Idx) : ℝ) ^ 2) * ε := by
  classical
  set K : ℝ := ((nonzeroF (F := F)).card : ℝ) with hK_def
  set N : ℝ := (Fintype.card (Vec F Idx) : ℝ) with hN_def
  have hK_eq : K = (Fintype.card F : ℝ) - 1 := by
    have heq : (nonzeroF (F := F)) = (Finset.univ : Finset F).erase 0 := by
      ext c; simp [nonzeroF]
    rw [hK_def, heq, Finset.card_erase_of_mem (by simp), Finset.card_univ,
      Nat.cast_sub Fintype.card_pos]; simp
  have hN_pos : 0 < N := by
    rw [hN_def]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Vec F Idx))
  have hK_pos : 0 < K := by
    have : (nonzeroF (F := F)).Nonempty := ⟨1, by simp [nonzeroF]⟩
    rw [hK_def]; exact_mod_cast this.card_pos
  have hKne : K ≠ 0 := ne_of_gt hK_pos
  have hNne : N ≠ 0 := ne_of_gt hN_pos
  have hKN2_nn : 0 ≤ K * K * N * N := by positivity
  -- Identify the bad indicator with the failure indicator at `(a,b) = (1,1)`.
  have hbad_eq : ∀ x y : Vec F Idx,
      (if f (x + y) = f x + f y then (0 : ℝ) else 1) =
        if BLRAcceptsAt f 1 1 x y then (0 : ℝ) else 1 := fun x y => by
    have hxy : (fun i => x i + y i) = x + y := rfl
    have hiff : BLRAcceptsAt f 1 1 x y ↔ f (x + y) = f x + f y := by
      simp [BLRAcceptsAt, hxy, eq_comm]
    by_cases h : f (x + y) = f x + f y
    · simp [hiff.mpr h, h]
    · have h' : ¬ BLRAcceptsAt f 1 1 x y := fun e => h (hiff.mp e)
      simp [h, h']
  -- Acceptance sum equals `acc · K²N²` (definition of `acceptanceProbabilityBLR`).
  have hsum_acc :
      (∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
          ∑ x : Vec F Idx, ∑ y : Vec F Idx,
            (if BLRAcceptsAt f a b x y then (1 : ℝ) else 0)) =
        acceptanceProbabilityBLR f * (K * K * N * N) := by
    show _ = (K⁻¹ * K⁻¹ * N⁻¹ * N⁻¹ * _) * (K * K * N * N)
    field_simp
  -- Failure sum = K²N² − acceptance sum = (1 − acc) · K²N².
  have hsum_fail :
      (∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
          ∑ x : Vec F Idx, ∑ y : Vec F Idx,
            (if BLRAcceptsAt f a b x y then (0 : ℝ) else 1)) =
        (1 - acceptanceProbabilityBLR f) * (K * K * N * N) := by
    have hpoint : ∀ (c : Prop) [Decidable c],
        (if c then (0 : ℝ) else 1) = 1 - (if c then 1 else 0) :=
      fun c _ => by split_ifs <;> ring
    simp_rw [hpoint, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [hsum_acc]; show K * (K * (N * N)) - _ = _; ring
  -- Drop the failure sum to its `(a,b) = (1,1)` summand and combine.
  have hone : (1 : F) ∈ (nonzeroF (F := F)) := by simp [nonzeroF]
  have hnn : ∀ a b : F, 0 ≤ ∑ x : Vec F Idx, ∑ y : Vec F Idx,
      (if BLRAcceptsAt f a b x y then (0 : ℝ) else 1) := fun a b =>
    Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  calc (∑ x : Vec F Idx, ∑ y : Vec F Idx,
          (if f (x + y) = f x + f y then (0 : ℝ) else 1))
      = ∑ x : Vec F Idx, ∑ y : Vec F Idx,
          (if BLRAcceptsAt f 1 1 x y then (0 : ℝ) else 1) := by simp_rw [hbad_eq]
    _ ≤ ∑ b ∈ (nonzeroF (F := F)),
          ∑ x : Vec F Idx, ∑ y : Vec F Idx,
            (if BLRAcceptsAt f 1 b x y then (0 : ℝ) else 1) :=
        Finset.single_le_sum (f := fun b => _) (fun b _ => hnn 1 b) hone
    _ ≤ ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
          ∑ x : Vec F Idx, ∑ y : Vec F Idx,
            (if BLRAcceptsAt f a b x y then (0 : ℝ) else 1) :=
        Finset.single_le_sum
          (f := fun a => ∑ b ∈ (nonzeroF (F := F)),
                ∑ x : Vec F Idx, ∑ y : Vec F Idx,
                  (if BLRAcceptsAt f a b x y then (0 : ℝ) else 1))
          (fun a _ => Finset.sum_nonneg fun _ _ => hnn _ _) hone
    _ = (1 - acceptanceProbabilityBLR f) * (K * K * N * N) := hsum_fail
    _ ≤ ε * (K * K * N * N) := mul_le_mul_of_nonneg_right hε hKN2_nn
    _ = ((Fintype.card F : ℝ) - 1) ^ 2 *
          ((Fintype.card (Vec F Idx) : ℝ) ^ 2) * ε := by rw [hK_eq]; ring

/-- **Affine BLR test induces an approximate representation**
(`lem:affine-to-approx-rep` in the blueprint).

If `f : F^Idx → F` passes the affine BLR test with rejection probability at
most `ε`, then the phase-lifted function `F(x) = ω^{f(x)}` satisfies the
average-correlation bound of a `(2(q-1)^2 ε, 1)`-approximate representation,
where `q = |F|`. -/
theorem affineTest_isApproxRepresentation
    [Fact (Nat.Prime (Fintype.card F))]
    (f : ScalarFn F Idx) (ε : ℝ)
    (hε : rejectionProbabilityBLR f ≤ ε) :
    (∑ x : Vec F Idx, ∑ y : Vec F Idx,
        ((starRingEnd ℂ) (blrPhase f x * blrPhase f y) *
          blrPhase f (x + y)).re) /
        ((Fintype.card (Vec F Idx) : ℝ) ^ 2) ≥
      1 - 2 * ((Fintype.card F : ℝ) - 1) ^ 2 * ε := by
  classical
  set N : ℝ := (Fintype.card (Vec F Idx) : ℝ) with hN_def
  have hN_pos : 0 < N := by
    rw [hN_def]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Vec F Idx))
  have hN2_pos : 0 < N ^ 2 := by positivity
  -- Pointwise lower bound, summed.
  have hsum_lower :
      ∑ x : Vec F Idx, ∑ y : Vec F Idx,
        ((1 : ℝ) - 2 * (if f (x + y) = f x + f y then (0 : ℝ) else 1)) ≤
      ∑ x : Vec F Idx, ∑ y : Vec F Idx,
        ((starRingEnd ℂ) (blrPhase f x * blrPhase f y) *
          blrPhase f (x + y)).re := by
    apply Finset.sum_le_sum; intro x _
    apply Finset.sum_le_sum; intro y _
    exact blrPhase_summand_lower f x y
  -- Compute the LHS sum: N^2 - 2 · #bad.
  have hLHS_eq :
      (∑ x : Vec F Idx, ∑ y : Vec F Idx,
        ((1 : ℝ) - 2 * (if f (x + y) = f x + f y then (0 : ℝ) else 1))) =
      N ^ 2 - 2 *
        ∑ x : Vec F Idx, ∑ y : Vec F Idx,
          (if f (x + y) = f x + f y then (0 : ℝ) else 1) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, ← Finset.mul_sum]
    have hcardR :
        ((Fintype.card (Vec F Idx) : ℝ) * Fintype.card (Vec F Idx)) = N ^ 2 := by
      rw [hN_def]; ring
    linarith
  -- Bad-pair bound.
  have hbad := badCount_le f ε hε
  -- Combine.
  rw [ge_iff_le, le_div_iff₀ hN2_pos]
  have hchain :
      (1 - 2 * ((Fintype.card F : ℝ) - 1) ^ 2 * ε) * N ^ 2 ≤
        N ^ 2 - 2 *
          ∑ x : Vec F Idx, ∑ y : Vec F Idx,
            (if f (x + y) = f x + f y then (0 : ℝ) else 1) := by
    nlinarith [hbad, sq_nonneg ((Fintype.card F : ℝ) - 1), hN_pos]
  linarith [hsum_lower, hLHS_eq ▸ hchain]

/-! ## Gowers-Hatami corollary for BLR (dimension 1) -/

/-- Lift a scalar function `Φ : Vec F Idx → ℂ` to a `1×1` matrix-valued
function on the multiplicative group, so that `gowers_hatami_GH2` can be
applied to it. -/
private noncomputable def liftMat1 (Φ : Vec F Idx → ℂ) :
    Multiplicative (Vec F Idx) → Matrix (Fin 1) (Fin 1) ℂ :=
  fun x _ _ => Φ (Multiplicative.toAdd x)

private lemma liftMat1_unitary
    (Φ : Vec F Idx → ℂ) (hΦ : ∀ x, ‖Φ x‖ = 1)
    (x : Multiplicative (Vec F Idx)) :
    liftMat1 Φ x ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i; fin_cases j
  have h := hΦ (Multiplicative.toAdd x)
  have hne : Φ (Multiplicative.toAdd x) ≠ 0 := by
    intro he; rw [he, norm_zero] at h; exact zero_ne_one h
  have hinv :
      star (Φ (Multiplicative.toAdd x)) = (Φ (Multiplicative.toAdd x))⁻¹ :=
    (Complex.inv_eq_conj h).symm
  simp [liftMat1, Matrix.mul_apply, hinv, mul_inv_cancel₀ hne]

/-- For `1×1` matrices with `σ = 1`, the `σ`-inner product is the scalar
inner product. -/
private lemma sigmaInner_one_fin1 (A B : Matrix (Fin 1) (Fin 1) ℂ) :
    sigmaInner (1 : Matrix (Fin 1) (Fin 1) ℂ) A B =
      (starRingEnd ℂ) (A 0 0) * B 0 0 := by
  unfold sigmaInner
  rw [Matrix.mul_one]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.trace_fin_one]

/-! ## Regular representation of `F^Idx` -/

/-- The (right) regular representation of the additive group `F^Idx` on
complex-valued functions: `(ρ(a) f)(x) = f(x + a)`. -/
def regRep (a : Vec F Idx) (f : ComplexFn F Idx) : ComplexFn F Idx :=
  fun x => f (x + a)

/-- The character `χ_α` is multiplicative under translation of its argument:
`χ_α(x + a) = χ_α(x) · χ_α(a)`. -/
private lemma charFn_translate (α x a : Vec F Idx) :
    charFn α (x + a) = charFn α x * charFn α a := by
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  letI : NeZero (ringChar F) := ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  have hbilin : (⟪α, x + a⟫ᵥ : F) = ⟪α, x⟫ᵥ + ⟪α, a⟫ᵥ := by
    simp [dotProduct, mul_add, Finset.sum_add_distrib]
  show ZMod.stdAddChar (N := ringChar F)
        (Algebra.trace (ZMod (ringChar F)) F ⟪α, x + a⟫ᵥ) =
      ZMod.stdAddChar (N := ringChar F)
          (Algebra.trace (ZMod (ringChar F)) F ⟪α, x⟫ᵥ) *
        ZMod.stdAddChar (N := ringChar F)
          (Algebra.trace (ZMod (ringChar F)) F ⟪α, a⟫ᵥ)
  rw [hbilin, map_add]
  exact AddChar.map_add_eq_mul _ _ _

/-- **Diagonalization of the regular representation in the Fourier basis**
(the regular-representation fact from the blueprint).

The character `χ_α` is an eigenvector of the regular representation `ρ(a)`
with eigenvalue `χ_α(a)`:  `ρ(a) χ_α = χ_α(a) · χ_α`.

In matrix language, this says that in the basis of characters `{χ_α}` the
operator `ρ(a)` is the diagonal matrix `∑_α χ_α(a) |α⟩⟨α|`. -/
theorem regRep_charFn (α a : Vec F Idx) :
    regRep a (charFn α) = charFn α a • charFn α := by
  funext x
  show charFn α (x + a) = charFn α a * charFn α x
  rw [charFn_translate, mul_comm]

/-! ## Path to `gh_implies_near_linearity` (following the blueprint)

The blueprint proof factors as:

1. **`gh_blr_correlation` (Lean version of `cor:gh-Fq`)** — invoke
   `gh2_average_correlation` at `d = 1`, `σ = 1` to get the inner-product
   form of GH for the BLR setting:
   `E_x Re ⟨F(x), ⟨v, G(x) v⟩⟩ ≥ 1 − ε`,
   where `g(x) := ⟨v, G(x) v⟩ = (V · R(x) · V*)_{0,0}` and `R = gh_right_reg`.

2. **Fourier expansion of `g`** — via `gh2_compression_apply` plus
   character orthogonality, `g(x) = ∑_α |F̂(α)|² · χ_α(x)`. This is a
   convex combination of characters, with `p_α := |F̂(α)|²` (so `p_α ≥ 0`
   and `∑_α p_α = 1` by Parseval).

3. **From `(1)` and `(2)`**: `∑_α p_α · Re(F̂(α)) ≥ 1 − ε`.

4. **`exists_heavy_fourier_coeff`** (max ≥ avg): ∃ α* with `Re(F̂(α*)) ≥ 1 − ε`.

5. **`phase_collision_distance_bound`**: with `ℓ(x) := ⟨α*, x⟩`,
   `δ(f, ℓ) ≤ q²/2 · ε` via `1 − cos(2π/q) ≥ 2/q²`.

Steps (1)–(3) — the GH inner-product bound and the convex-combination form
for the compression `g(x)` — are bundled into `gh_blr_fourier_lower_bound`.
Concretely, that proof:

* invokes `gh_blr_correlation` to obtain the GH bound
  `(1/N) ∑_x Re(conj(Φ x) · g(x)) ≥ 1 − ε`, where
  `g(x) = (V · R(x) · V*)_{0,0}` is the diagonal entry of the compressed
  right-regular representation;
* expands that matrix entry via `gh2_compression_apply` (matrix entry =
  autocorrelation `(1/N) ∑_y star(Φ y) · Φ(y+x)`), then uses the
  eigenvector property of `R(x)` in the Fourier basis — derived from
  Pontryagin orthogonality (no irrep theory) via `fourier_inversion` +
  `charFn_translate` + `sum_star_mul_charFn` — to obtain
  `g(x) = ∑_α |F̂α|² · χ_α(x)`;
* substitutes back, pulls `Re` through, swaps sums, and identifies the
  inner average `(1/N) ∑_x Re(conj(Φ x) · χ_α(x))` with `Re(F̂α)`.
-/

/-- The phase-lifted function lands on the unit circle. -/
private lemma blrPhase_norm
    [Fact (Nat.Prime (Fintype.card F))]
    (f : ScalarFn F Idx) (x : Vec F Idx) :
    ‖blrPhase f x‖ = 1 := AddChar.norm_apply _ _

/-- Max-≥-average: from a convex combination `≥ 1 − ε`, extract an index
where the value alone is `≥ 1 − ε`. -/
private lemma exists_heavy_fourier_coeff
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → ℝ) (a : ι → ℝ) (ε : ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hpa : ∑ i, p i * a i ≥ 1 - ε) :
    ∃ i, a i ≥ 1 - ε := by
  classical
  obtain ⟨i_star, _, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty a
  refine ⟨i_star, ?_⟩
  have hi_max : ∀ i, a i ≤ a i_star := fun i => hmax ▸ Finset.le_sup' a (Finset.mem_univ i)
  have h_avg_le_max : ∑ i, p i * a i ≤ a i_star := by
    calc ∑ i, p i * a i ≤ ∑ i, p i * a i_star := by
            apply Finset.sum_le_sum; intro i _
            exact mul_le_mul_of_nonneg_left (hi_max i) (hp_nonneg i)
      _ = a i_star * ∑ i, p i := by rw [← Finset.sum_mul]; ring
      _ = a i_star := by rw [hp_sum]; ring
  linarith

/-- **Real-analytic phase bound (sub-lemma)**.

For any non-zero `k : F`, the real part of `blrChar k = ω_p^{Tr(k)}` is
bounded above by `cos(2π/q)`. With `q = |F|` prime, the trace is the
identity, so `blrChar k = exp(2πi·k/q)` and the bound `cos(2π·k/q) ≤
cos(2π/q)` for `k ∈ {1, …, q−1}` follows from monotonicity of `cos` on
`[0, π]` after picking the balanced representative `|k| ≤ q/2`. -/
private lemma blrChar_re_le_of_ne_zero
    [hp : Fact (Nat.Prime (Fintype.card F))]
    (k : F) (hk : k ≠ 0) :
    (blrChar (F := F) k).re ≤
      Real.cos (2 * Real.pi / (Fintype.card F : ℝ)) := by
  letI : NeZero (ringChar F) :=
    ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  have hqp : (Fintype.card F).Prime := hp.out
  -- `ringChar F = Fintype.card F` (since `card = ringChar^n` and `card` is prime).
  have hrc : ringChar F = Fintype.card F := by
    obtain ⟨n, _, hcard⟩ := FiniteField.card F (ringChar F)
    exact ((Nat.Prime.pow_eq_iff hqp).mp hcard.symm).1
  -- Reduce to `ZMod.stdAddChar` via `primeFieldEquivZMod`. Injectivity (the
  -- equiv is bijective) plus `k ≠ 0` gives `t ≠ 0`.
  set t : ZMod (ringChar F) := primeFieldEquivZMod k with ht_def
  have hblr : blrChar (F := F) k = ZMod.stdAddChar t := by
    show ZMod.stdAddChar ((primeFieldEquivZMod (F := F)).toRingHom.toAddMonoidHom k) =
      ZMod.stdAddChar t
    rfl
  have ht_ne : t ≠ 0 := fun h => hk
    (by simpa using (primeFieldEquivZMod (F := F)).injective (h.trans (map_zero _).symm))
  set q : ℕ := Fintype.card F with hq_def
  have htv_pos : 0 < t.val := Nat.pos_of_ne_zero fun h => ht_ne
    (by rw [← ZMod.natCast_zmod_val t, h, Nat.cast_zero])
  have htv_lt : t.val < q := by rw [← hrc]; exact ZMod.val_lt t
  -- Balanced representative `j ∈ ℤ` of `t`: `1 ≤ |j|` and `2|j| ≤ q`.
  set j : ℤ := if 2 * t.val ≤ q then (t.val : ℤ) else (t.val : ℤ) - (q : ℤ) with hj_def
  have hqcastN : ((q : ℕ) : ZMod (ringChar F)) = 0 := by
    rw [show (q : ℕ) = ringChar F from hrc.symm]; exact ZMod.natCast_self _
  have hj_cong : (j : ZMod (ringChar F)) = t := by
    simp only [j]; split_ifs
    · push_cast; exact ZMod.natCast_zmod_val t
    · push_cast; rw [hqcastN, sub_zero]; exact ZMod.natCast_zmod_val t
  have hj_real : (j : ℝ) = if 2 * t.val ≤ q then (t.val : ℝ) else (t.val : ℝ) - q := by
    simp only [j]; split_ifs <;> push_cast <;> rfl
  have hj_abs_le : |(j : ℝ)| * 2 ≤ q := by
    rw [hj_real]
    split_ifs with h
    · rw [abs_of_nonneg (by exact_mod_cast Nat.zero_le _)]
      have : (2 : ℝ) * t.val ≤ q := by exact_mod_cast h
      linarith
    · push_neg at h
      have h1 : (t.val : ℝ) - q ≤ 0 := by
        have : (t.val : ℝ) ≤ q := by exact_mod_cast Nat.le_of_lt htv_lt
        linarith
      rw [abs_of_nonpos h1]
      have : (q : ℝ) < 2 * t.val := by exact_mod_cast h
      linarith
  have hj_abs_ge : (1 : ℝ) ≤ |(j : ℝ)| := by
    rw [hj_real]
    split_ifs with h
    · rw [abs_of_nonneg (by exact_mod_cast Nat.zero_le _)]
      exact_mod_cast htv_pos
    · push_neg at h
      have h1 : (t.val : ℝ) - q ≤ 0 := by
        have : (t.val : ℝ) ≤ q := by exact_mod_cast Nat.le_of_lt htv_lt
        linarith
      rw [abs_of_nonpos h1]
      have htlt : (t.val : ℝ) ≤ (q : ℝ) - 1 := by
        have h2 : (t.val : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast htv_lt
        linarith
      linarith
  -- (stdAddChar t).re = cos (2π · j / q).
  have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast hqp.pos.ne'
  have hSAC_re : (ZMod.stdAddChar t).re = Real.cos (2 * Real.pi * j / q) := by
    rw [← hj_cong, ZMod.stdAddChar_coe, hrc]
    rw [show ((2 : ℂ) * Real.pi * Complex.I * (j : ℂ) / (q : ℂ)) =
            ((2 * Real.pi * j / q : ℝ) : ℂ) * Complex.I from by push_cast; ring]
    exact Complex.exp_ofReal_mul_I_re _
  rw [hblr, hSAC_re,
      show (2 * Real.pi * (j : ℝ) / q) = (2 * Real.pi / q) * (j : ℝ) from by ring,
      ← Real.cos_abs ((2 * Real.pi / q) * (j : ℝ)), abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi / q)]
  -- Goal: cos ((2π/q) · |j|) ≤ cos (2π/q). Apply monotonicity of cos on [0, π].
  have hpos : (0 : ℝ) ≤ 2 * Real.pi / q := by positivity
  have hπ_eq : 2 * Real.pi / q * ((q : ℝ) / 2) = Real.pi := by field_simp
  refine Real.cos_le_cos_of_nonneg_of_le_pi hpos ?_ ?_
  · calc 2 * Real.pi / q * |(j : ℝ)|
        ≤ 2 * Real.pi / q * ((q : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hpos
      _ = Real.pi := hπ_eq
  · simpa using mul_le_mul_of_nonneg_left hj_abs_ge hpos

/-- Pointwise indicator-form bound on the BLR-phase / character correlation
summand. Specialises `blrChar_re_le_of_ne_zero` to the form that appears
inside the Fourier coefficient: identifies the product as a single character
at `f x − ⟨α,x⟩`, splits on whether that argument is zero, and packages both
cases as a single linear bound. -/
private lemma blrPhase_star_charFn_re_le
    [Fact (Nat.Prime (Fintype.card F))]
    (f : ScalarFn F Idx) (α : Vec F Idx) (x : Vec F Idx) :
    (blrPhase f x * star (charFn α x)).re ≤
      1 - (1 - Real.cos (2 * Real.pi / (Fintype.card F : ℝ))) *
            (if f x ≠ linearFn α x then (1 : ℝ) else 0) := by
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  letI : NeZero (ringChar F) := ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  have hkey : blrPhase f x * star (charFn α x) =
      blrChar (F := F) (f x - linearFn α x) := by
    set ψ : AddChar F ℂ := blrChar (F := F)
    have hstar : star (ψ (linearFn α x)) = ψ (- linearFn α x) := by
      rw [AddChar.map_neg_eq_inv]
      exact (Complex.inv_eq_conj (AddChar.norm_apply ψ _)).symm
    have hcharFn_eq : charFn α x = ψ (linearFn α x) := by
      have htrace : Algebra.trace (ZMod (ringChar F)) F ⟪α, x⟫ᵥ =
          primeFieldEquivZMod (F := F) ⟪α, x⟫ᵥ :=
        trace_eq_primeFieldEquivZMod ⟪α, x⟫ᵥ
      change ZMod.stdAddChar (Algebra.trace (ZMod (ringChar F)) F ⟪α, x⟫ᵥ) =
        ZMod.stdAddChar ((primeFieldEquivZMod (F := F)).toRingHom.toAddMonoidHom
          (linearFn α x))
      rw [htrace]; rfl
    rw [blrPhase_eq_blrChar, hcharFn_eq, hstar, ← AddChar.map_add_eq_mul]
    congr 1; ring
  rw [hkey]
  by_cases h : f x = linearFn α x
  · simp [h, AddChar.map_zero_eq_one]
  · have := blrChar_re_le_of_ne_zero (f x - linearFn α x) (sub_ne_zero.mpr h)
    simp only [h, ne_eq, not_false_iff, if_true, mul_one]; linarith

/-- **Phase-collision bound** (the `c_q = 1 - cos(2π/q)` step in the blueprint).

If `Re(F̂(α*)) ≥ 1 − ε` for `F = ω^{f(·)}`, then `f` is
`ε / (1 - cos(2π/q))`-close to `ℓ(x) = ⟨α*, x⟩` in relative Hamming
distance.

The proof: write `F̂(α) = (1/N) ∑_x ψ(f(x) − ℓ(x))`. The pointwise bound
`Re ≤ 1 − c · 𝟙[f x ≠ ℓ x]` (with `c = 1 − cos(2π/q)`) is supplied by
`blrPhase_star_charFn_re_le`; averaging gives `Re(F̂(α)) ≤ 1 − c · δ`,
which combined with `Re(F̂(α)) ≥ 1 − ε` yields `δ ≤ ε / c`. -/
private lemma phase_collision_distance_bound
    [Fact (Nat.Prime (Fintype.card F))]
    (f : ScalarFn F Idx) (α : Vec F Idx) (ε : ℝ)
    (hbound : (fourierCoeff (blrPhase f) α).re ≥ 1 - ε) :
    distance f (linearFn α) ≤
      ε / (1 - Real.cos (2 * Real.pi / (Fintype.card F : ℝ))) := by
  classical
  set N : ℝ := (Fintype.card (Vec F Idx) : ℝ) with hN_def
  set c : ℝ := 1 - Real.cos (2 * Real.pi / (Fintype.card F : ℝ)) with hc_def
  have hN_pos : 0 < N := by
    rw [hN_def]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Vec F Idx))
  -- `0 < c` since `2π/q ∈ (0, π]` and cos is strictly antitone on `[0, π]`.
  have hc_pos : 0 < c := by
    have hq_pos : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
    have hq_ge_2 : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by
      exact_mod_cast (Fact.out (p := (Fintype.card F).Prime)).two_le
    have hle : 2 * Real.pi / (Fintype.card F : ℝ) ≤ Real.pi := by
      rw [div_le_iff₀ hq_pos]; nlinarith [Real.pi_pos]
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hle (by positivity)
    rw [Real.cos_zero] at this; rw [hc_def]; linarith
  -- `(F̂α).re ≤ 1 - c · δ` via the pointwise specialised bound.
  have hbound2 :
      (fourierCoeff (blrPhase f) α).re ≤ 1 - c * distance f (linearFn α) := by
    have hReFour : (fourierCoeff (blrPhase f) α).re =
        N⁻¹ * ∑ x : Vec F Idx, (blrPhase f x * star (charFn α x)).re := by
      unfold fourierCoeff fnInner expectation
      rw [Complex.re_ofReal_mul, Complex.re_sum]
    rw [hReFour]
    calc N⁻¹ * ∑ x, (blrPhase f x * star (charFn α x)).re
        ≤ N⁻¹ * ∑ x : Vec F Idx,
            (1 - c * (if f x ≠ linearFn α x then (1 : ℝ) else 0)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun x _ => by
              rw [hc_def]; exact blrPhase_star_charFn_re_le f α x)
            (inv_nonneg.mpr hN_pos.le)
      _ = 1 - c * distance f (linearFn α) := by
          unfold distance
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
              nsmul_eq_mul, mul_one, ← Finset.mul_sum, mul_sub,
              inv_mul_cancel₀ hN_pos.ne']
          ring
  have : c * distance f (linearFn α) ≤ ε := by linarith
  rwa [le_div_iff₀ hc_pos, mul_comm]

/-! ### Shared helpers for the GH-correlation corollaries -/

/-- The 1×1 lift of `Φ` is an `(ε, 1)`-approximate representation of
`Multiplicative (F^Idx)`, given the BLR-form hypothesis. -/
private lemma liftMat1_isApproxRep
    (Φ : Vec F Idx → ℂ) (ε : ℝ)
    (hApprox :
      (∑ x : Vec F Idx, ∑ y : Vec F Idx,
          ((starRingEnd ℂ) (Φ x * Φ y) * Φ (x + y)).re) /
        ((Fintype.card (Vec F Idx) : ℝ) ^ 2) ≥ 1 - ε) :
    IsApproxRepresentation (Multiplicative (Vec F Idx))
      (1 : Matrix (Fin 1) (Fin 1) ℂ) (liftMat1 Φ) ε := by
  show (∑ x : Multiplicative (Vec F Idx), ∑ y,
      (sigmaInner 1 (liftMat1 Φ x * liftMat1 Φ y) (liftMat1 Φ (x * y))).re) /
    ((Fintype.card (Multiplicative (Vec F Idx)) : ℝ) ^ 2) ≥ 1 - ε
  rw [show (Fintype.card (Multiplicative (Vec F Idx)) : ℝ) =
        (Fintype.card (Vec F Idx) : ℝ) from by simp,
      show (∑ x : Multiplicative (Vec F Idx), ∑ y,
          (sigmaInner 1 (liftMat1 Φ x * liftMat1 Φ y) (liftMat1 Φ (x*y))).re) =
        ∑ x : Vec F Idx, ∑ y : Vec F Idx,
          ((starRingEnd ℂ) (Φ x * Φ y) * Φ (x + y)).re from by
        refine Fintype.sum_equiv Multiplicative.toAdd _ _ (fun x => ?_)
        refine Fintype.sum_equiv Multiplicative.toAdd _ _ (fun y => ?_)
        rw [sigmaInner_one_fin1]; simp [liftMat1, Matrix.mul_apply]]
  exact hApprox

/-- **Gowers-Hatami correlation for BLR** (Lean form of `cor:gh-Fq`).

Specialisation of `gh2_average_correlation` to the BLR setting (`d = 1`,
`σ = I`). It does **two** things:

1. Constructs the witness pair: `V := gh2Embedding _ (liftMat1 Φ)` is a 1×N
   isometry (`V · V* = 1`), and `R(x) := gh2RightRegularMatrix x` is the
   right-regular permutation matrix on `ℂ^N`.

2. Repackages the BLR-style **double-sum** hypothesis
   `(1/N²) ∑_{x,y} Re(conj(Φx · Φy) · Φ(x+y)) ≥ 1 − ε`
   as the GH-style **single-sum** bound
   `(1/N) ∑_x Re(conj(Φx) · g(x)) ≥ 1 − ε`,
   where `g(x) := (V · R(x) · V*)_{0,0}` is the matrix entry.

What it does **not** do:

* It does not compute `g(x)` in terms of `Φ`. The matrix entry is left
  abstract — its expansion (via `gh2_compression_apply`) and
  diagonalisation in the Fourier basis (via `charFn_translate` + character
  orthogonality) are the substantive content of `gh_blr_fourier_lower_bound`.
* It does not produce Fourier coefficients of either `Φ` or `g`.

The blueprint's existential statement
"∃ unit vector v and exact rep G such that ..." is the immediate
`⟨_, _, _, _⟩` from this conclusion (after the standard
`GH2Index ≃ Fin n` reindex). -/
theorem gh_blr_correlation
    (Φ : Vec F Idx → ℂ) (hΦ : ∀ x, ‖Φ x‖ = 1)
    (ε : ℝ)
    (hApprox :
      (∑ x : Vec F Idx, ∑ y : Vec F Idx,
          ((starRingEnd ℂ) (Φ x * Φ y) * Φ (x + y)).re) /
        ((Fintype.card (Vec F Idx) : ℝ) ^ 2) ≥ 1 - ε) :
    let V_orig := gh2Embedding (Multiplicative (Vec F Idx)) (liftMat1 Φ)
    V_orig * V_origᴴ = 1 ∧
    (∑ x : Vec F Idx,
        ((starRingEnd ℂ) (Φ x) *
          (V_orig * gh2RightRegularMatrix
              (G := Multiplicative (Vec F Idx)) (d := 1)
              (Multiplicative.ofAdd x) * V_origᴴ) 0 0).re) /
      (Fintype.card (Vec F Idx) : ℝ) ≥ 1 - ε := by
  classical
  refine ⟨?_, ?_⟩
  · exact gh2Embedding_isometry _ (liftMat1 Φ) (liftMat1_unitary Φ hΦ)
  · have hgh := gh2_average_correlation (Multiplicative (Vec F Idx))
                  (1 : Matrix (Fin 1) (Fin 1) ℂ) (liftMat1 Φ) ε
                  (liftMat1_isApproxRep Φ ε hApprox)
    rw [show (Fintype.card (Multiplicative (Vec F Idx)) : ℝ) =
          (Fintype.card (Vec F Idx) : ℝ) from by simp] at hgh
    -- Reduce each `sigmaInner` summand to scalar form: `sigmaInner 1 (liftMat1 Φ x) M`
    -- expands via `sigmaInner_one_fin1` to `(starRingEnd ℂ) ((liftMat1 Φ x) 0 0) * M 0 0`,
    -- and `(liftMat1 Φ x) 0 0` reduces to `Φ (toAdd x)` by `rfl`.
    simp_rw [sigmaInner_one_fin1, show ∀ (Φ' : Vec F Idx → ℂ)
        (x' : Multiplicative (Vec F Idx)),
        (liftMat1 Φ' x') 0 0 = Φ' (Multiplicative.toAdd x') from fun _ _ => rfl] at hgh
    -- Reindex the sum from `Multiplicative` to `Vec F Idx`.
    rw [show (∑ x : Vec F Idx,
            ((starRingEnd ℂ) (Φ x) *
              (gh2Embedding (Multiplicative (Vec F Idx)) (liftMat1 Φ) *
                gh2RightRegularMatrix
                  (G := Multiplicative (Vec F Idx)) (d := 1)
                  (Multiplicative.ofAdd x) *
                (gh2Embedding (Multiplicative (Vec F Idx)) (liftMat1 Φ))ᴴ) 0 0).re) =
          ∑ x : Multiplicative (Vec F Idx),
            ((starRingEnd ℂ) (Φ (Multiplicative.toAdd x)) *
              (gh2Embedding (Multiplicative (Vec F Idx)) (liftMat1 Φ) *
                gh2RightRegularMatrix
                  (G := Multiplicative (Vec F Idx)) (d := 1) x *
                (gh2Embedding (Multiplicative (Vec F Idx)) (liftMat1 Φ))ᴴ) 0 0).re from
      (Fintype.sum_equiv Multiplicative.toAdd _ _ (fun _ => rfl)).symm]
    exact hgh


/-- Helper: `N · star(F̂α) = ∑_x star(Φ x) · χ_α(x)`. Conjugate of the
definition of `fourierCoeff`, normalisation cleared. -/
private lemma sum_star_mul_charFn (Φ : ComplexFn F Idx) (α : Vec F Idx) :
    (∑ x : Vec F Idx, (starRingEnd ℂ) (Φ x) * charFn α x) =
      (Fintype.card (Vec F Idx) : ℂ) * star (fourierCoeff Φ α) := by
  have hN : (Fintype.card (Vec F Idx) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  -- `N · F̂α = ∑ Φ · star χ_α`; then conjugate both sides.
  have h1 : (Fintype.card (Vec F Idx) : ℂ) * fourierCoeff Φ α =
      ∑ x : Vec F Idx, Φ x * star (charFn α x) := by
    show (Fintype.card (Vec F Idx) : ℂ) * ⟪Φ, charFn α⟫ = _
    unfold fnInner expectation
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul]
  have h2 : star ((Fintype.card (Vec F Idx) : ℂ) * fourierCoeff Φ α) =
      ∑ x : Vec F Idx, (starRingEnd ℂ) (Φ x) * charFn α x := by
    rw [h1, star_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [star_mul', star_star, Complex.star_def]
  rw [← h2, star_mul', Complex.star_def, Complex.conj_natCast]

/-- **Combined corollary** (the Fourier-form bound used in the blueprint
proof of `lem:gh-linearity`):

If `Φ : F^Idx → ℂ` lies on the unit circle and satisfies the
`(ε, 1)`-approximate-representation hypothesis, there is a probability
distribution `(p_α)` on `F^Idx` such that
`∑_α p_α · Re(F̂(α)) ≥ 1 − ε`, with `p_α := ‖F̂(α)‖²`.

**Blueprint proof** (steps 1–3 of `gh_implies_near_linearity`):

1. **`gh_blr_correlation`** packages the BLR-style hypothesis as the GH
   inner-product bound `(1/N) ∑_x Re(conj(Φ x) · g(x)) ≥ 1 − ε`, where
   `g(x) := (V · R(x) · V*)_{0,0}` is the diagonal entry of the compressed
   right-regular representation.
2. **Spectral decomposition** `g(x) = ∑_α |F̂α|² · χ_α(x)` via
   `gh2_compression_apply` (matrix → autocorrelation `(1/N) ∑_y star(Φ y)·
   Φ(y+x)`), `fourier_inversion` + `charFn_translate` (the eigenvector
   property of `R(x)` from `regRep_charFn`, in additive form), and
   `sum_star_mul_charFn` (orthogonality of characters / Plancherel).
3. **Substitute and identify**: pull `Re` through, swap sums, and recognise
   `(1/N) ∑_x Re(conj(Φ x) · χ_α(x)) = Re(F̂α)`. -/
theorem gh_blr_fourier_lower_bound
    (Φ : Vec F Idx → ℂ) (hΦ : ∀ x, ‖Φ x‖ = 1)
    (ε : ℝ)
    (hApprox :
      (∑ x : Vec F Idx, ∑ y : Vec F Idx,
          ((starRingEnd ℂ) (Φ x * Φ y) * Φ (x + y)).re) /
        ((Fintype.card (Vec F Idx) : ℝ) ^ 2) ≥ 1 - ε) :
    ∃ (p : Vec F Idx → ℝ),
      (∀ α, 0 ≤ p α) ∧ (∑ α, p α = 1) ∧
      (∑ α, p α * (fourierCoeff Φ α).re) ≥ 1 - ε := by
  classical
  set N : ℕ := Fintype.card (Vec F Idx) with hN_def
  have hN_ne_R : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hN_ne_C : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  refine ⟨fun α => ‖fourierCoeff Φ α‖ ^ 2, fun α => sq_nonneg _, ?_, ?_⟩
  · -- ∑ ‖F̂α‖² = 1: Parseval + `‖Φ‖ = 1`.
    rw [parseval_identity]
    show (Fintype.card (Vec F Idx) : ℝ)⁻¹ * ∑ x : Vec F Idx, ‖Φ x‖ ^ 2 = 1
    simp [hΦ, Finset.card_univ, ← hN_def, inv_mul_cancel₀ hN_ne_R]
  · -- (1) GH bound from `gh_blr_correlation`.
    obtain ⟨_, hgh⟩ := gh_blr_correlation Φ hΦ ε hApprox
    -- (2) Spectral decomposition `g(x) = ∑_α |F̂α|² · χ_α(x)`.
    have hg_eq : ∀ x : Vec F Idx,
        (gh2Embedding (Multiplicative (Vec F Idx)) (liftMat1 Φ) *
            gh2RightRegularMatrix (G := Multiplicative (Vec F Idx)) (d := 1)
              (Multiplicative.ofAdd x) *
            (gh2Embedding (Multiplicative (Vec F Idx)) (liftMat1 Φ))ᴴ) 0 0 =
          ∑ α : Vec F Idx, ((‖fourierCoeff Φ α‖ ^ 2 : ℝ) : ℂ) * charFn α x := by
      intro x
      -- (a) Matrix entry → autocorrelation `(1/N) ∑_y star(Φ y) · Φ(y+x)`.
      rw [gh2_compression_apply]
      simp only [Fin.sum_univ_one, gh2Scale_mul_self,
        show (Fintype.card (Multiplicative (Vec F Idx)) : ℂ)⁻¹ = (N : ℂ)⁻¹ from by
          congr 1; simp [hN_def]]
      rw [← Finset.mul_sum,
          show (∑ y : Multiplicative (Vec F Idx),
                ((starRingEnd ℂ) (liftMat1 Φ y 0 0) *
                    liftMat1 Φ (y * Multiplicative.ofAdd x) 0 0)) =
              ∑ y : Vec F Idx, (starRingEnd ℂ) (Φ y) * Φ (y + x) from
            (Fintype.sum_equiv Multiplicative.ofAdd _ _ (fun y => by simp [liftMat1])).symm]
      -- (b) Substitute Fourier inversion of Φ(y+x); apply orthogonality.
      rw [show (∑ y : Vec F Idx, (starRingEnd ℂ) (Φ y) * Φ (y + x)) =
            ∑ y : Vec F Idx, ∑ α : Vec F Idx,
              fourierCoeff Φ α * ((starRingEnd ℂ) (Φ y) * charFn α y) * charFn α x from
          Finset.sum_congr rfl fun y _ => by
            rw [fourier_inversion Φ (y + x), Finset.mul_sum]
            refine Finset.sum_congr rfl fun α _ => ?_
            rw [charFn_translate]; ring]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [show (∑ y : Vec F Idx,
              fourierCoeff Φ α * ((starRingEnd ℂ) (Φ y) * charFn α y) * charFn α x) =
            fourierCoeff Φ α * charFn α x *
              ∑ y : Vec F Idx, (starRingEnd ℂ) (Φ y) * charFn α y from by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_; ring,
          sum_star_mul_charFn,
          show ((‖fourierCoeff Φ α‖ ^ 2 : ℝ) : ℂ) =
                fourierCoeff Φ α * star (fourierCoeff Φ α) from by
            rw [Complex.sq_norm, ← Complex.mul_conj, Complex.star_def]]
      field_simp; ring
    -- (3) Substitute `hg_eq` into `hgh`; pull `Re` through; identify the inner
    -- average `(1/N) ∑_x Re(conj(Φ x) · χ_α(x))` with `Re(F̂α)`.
    simp_rw [hg_eq] at hgh
    have hpoint : ∀ x : Vec F Idx,
        ((starRingEnd ℂ) (Φ x) *
            ∑ α : Vec F Idx, ((‖fourierCoeff Φ α‖ ^ 2 : ℝ) : ℂ) * charFn α x).re =
        ∑ α : Vec F Idx,
          ‖fourierCoeff Φ α‖ ^ 2 * ((starRingEnd ℂ) (Φ x) * charFn α x).re := by
      intro x
      rw [Finset.mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [show (starRingEnd ℂ) (Φ x) *
              (((‖fourierCoeff Φ α‖ ^ 2 : ℝ) : ℂ) * charFn α x) =
            ((‖fourierCoeff Φ α‖ ^ 2 : ℝ) : ℂ) *
              ((starRingEnd ℂ) (Φ x) * charFn α x) from by ring,
          Complex.re_ofReal_mul]
    have hreF : ∀ α : Vec F Idx, (fourierCoeff Φ α).re =
        (N : ℝ)⁻¹ * ∑ x : Vec F Idx, ((starRingEnd ℂ) (Φ x) * charFn α x).re := by
      intro α
      show (⟪Φ, charFn α⟫).re = _
      unfold fnInner expectation
      rw [Complex.re_ofReal_mul, Complex.re_sum]
      refine congrArg ((Fintype.card (Vec F Idx) : ℝ)⁻¹ * ·) ?_
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [show Φ x * star (charFn α x) =
            (starRingEnd ℂ) ((starRingEnd ℂ) (Φ x) * charFn α x) from by
          rw [map_mul, ← Complex.star_def, star_star],
          Complex.conj_re]
    simp_rw [hpoint, ← hN_def] at hgh
    rw [Finset.sum_comm,
        show (∑ α : Vec F Idx, ∑ x : Vec F Idx,
              ‖fourierCoeff Φ α‖ ^ 2 * ((starRingEnd ℂ) (Φ x) * charFn α x).re) /
              (N : ℝ) =
            ∑ α : Vec F Idx,
              ‖fourierCoeff Φ α‖ ^ 2 *
                ((N : ℝ)⁻¹ * ∑ x : Vec F Idx,
                  ((starRingEnd ℂ) (Φ x) * charFn α x).re) from by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [← Finset.mul_sum, mul_div_assoc, div_eq_inv_mul]] at hgh
    simp_rw [← hreF] at hgh
    exact hgh

/-- **Gowers-Hatami implies near linearity** (`lem:gh-linearity` in the
blueprint).

If the phase-lifted function `F(x) = ω^{f(x)}` is an `(ε, 1)`-approximate
representation of `F^Idx`, then `f` is `ε / (1 - cos(2π/q))`-close in
relative Hamming distance to some linear function `ℓ`, where `q = |F|`.
(The Jordan inequality `1 - cos(2π/q) ≥ 2/q²` then gives the cruder
`q²ε/2` bound.)

**Proof structure (following the blueprint):**

1. By `gh_blr_correlation` (`cor:gh-Fq`), get the GH inner-product bound
   `E_x Re(conj(F(x)) · g(x)) ≥ 1 − ε`,
   where `g(x) = (V·R(x)·V*)_{0,0}` is the compression of the regular rep.
2. Expand `v` in the Fourier basis: `g(x) = ∑_α p_α χ_α(x)` with
   `p_α := |F̂(α)|²` (`∑ p_α = 1` by Parseval).
3. Hence `∑_α p_α Re(F̂(α)) ≥ 1 − ε`.
4. Max-≥-avg ⟹ ∃ α* with `Re(F̂(α*)) ≥ 1 − ε`.
5. Phase-collision bound: `δ(f, ℓ_{α*}) ≤ ε / (1 - cos(2π/q))`.

In the formalisation below, steps 1–3 are bundled in
`gh_blr_fourier_lower_bound` (= `cor:gh-Fq` + spectral decomposition of the
GH compression `g(x)` as a convex combination of characters). -/
theorem gh_implies_near_linearity
    [Fact (Nat.Prime (Fintype.card F))]
    (f : ScalarFn F Idx) (ε : ℝ)
    (hApprox :
      (∑ x : Vec F Idx, ∑ y : Vec F Idx,
          ((starRingEnd ℂ) (blrPhase f x * blrPhase f y) *
            blrPhase f (x + y)).re) /
        ((Fintype.card (Vec F Idx) : ℝ) ^ 2) ≥ 1 - ε) :
    ∃ ℓ : ScalarFn F Idx, IsLinear ℓ ∧
      distance f ℓ ≤
        ε / (1 - Real.cos (2 * Real.pi / (Fintype.card F : ℝ))) := by
  classical
  -- 1. Get the Fourier-form bound from `gh_blr_fourier_lower_bound`
  --    (= cor:gh-Fq + convex-combination of characters).
  obtain ⟨p, hp_nonneg, hp_sum, hp_bound⟩ :=
    gh_blr_fourier_lower_bound (blrPhase f) (blrPhase_norm f) ε hApprox
  -- 2. Max-≥-avg ⟹ ∃ α* with Re(F̂(α*)) ≥ 1 − ε.
  obtain ⟨α_star, hα_star⟩ :=
    exists_heavy_fourier_coeff p
      (fun α => (fourierCoeff (blrPhase f) α).re)
      ε hp_nonneg hp_sum hp_bound
  -- 3. Apply the phase-collision bound at `ℓ = linearFn α_star`.
  refine ⟨linearFn α_star, ⟨α_star, fun _ => rfl⟩, ?_⟩
  exact phase_collision_distance_bound f α_star ε hα_star

/-- The distance from `f` to linearity is bounded by the distance from `f` to
any specific linear function `ℓ`. Proved by unfolding `distanceToLinear`
(an `inf'` over the finset of linear functions) and exhibiting `ℓ` as a
member of that finset.

(Local copy retained for this GH-oriented proof path.) -/
private lemma distanceToLinear_le_of_isLinear
    {f ℓ : ScalarFn F Idx} (hℓ : IsLinear ℓ) :
    distanceToLinear f ≤ distance f ℓ := by
  classical
  unfold distanceToLinear
  rw [Finset.inf'_le_iff]
  refine ⟨ℓ, ?_, le_rfl⟩
  simp [LinearSet, hℓ]

/-- **Equivalence for the BLR test** (`prop:equiv_blr` in the blueprint).

For any positive constant `C`, the soundness statement "if the rejection
probability is at most `ε`, then the distance to the closest linear function
is at most `C · ε`" is equivalent to the single inequality
`Pr[BLR rejects] ≥ δ(f, Lin) / C`.

This is a purely algebraic equivalence:
* (→) Specialise the hypothesis at `ε := rejectionProbabilityBLR f`.
* (←) Chain `distanceToLinear f / C ≤ rejectionProbabilityBLR f ≤ ε`. -/
theorem rejection_distance_equivalence
    (f : ScalarFn F Idx) (C : ℝ) (hC : 0 < C) :
    (∀ ε : ℝ, rejectionProbabilityBLR f ≤ ε →
        distanceToLinear f ≤ C * ε) ↔
      rejectionProbabilityBLR f ≥ distanceToLinear f / C := by
  refine ⟨fun h => ?_, fun h ε hε => ?_⟩
  · have hself := h _ le_rfl
    rw [ge_iff_le, div_le_iff₀ hC, mul_comm]
    exact hself
  · rw [ge_iff_le, div_le_iff₀ hC] at h
    calc distanceToLinear f
        ≤ rejectionProbabilityBLR f * C := h
      _ ≤ ε * C := mul_le_mul_of_nonneg_right hε hC.le
      _ = C * ε := mul_comm _ _

/-- **Soundness of the BLR test, GH-flavoured** (rejection form).


Composing `affineTest_isApproxRepresentation` with `gh_implies_near_linearity`:
if the BLR test rejects `f` with probability at most `ε`, then `f` is within
`C · ε` of the closest linear function, where
`C := 2 (q - 1)² / (1 - cos(2π/q))` and `q = |F|`.

By `rejection_distance_equivalence`, this is equivalently stated as
`Pr[BLR rejects f] ≥ δ(f, Lin) / C`. -/
theorem blr_gh_soundness
    [Fact (Nat.Prime (Fintype.card F))]
    (f : ScalarFn F Idx) :
    rejectionProbabilityBLR f ≥
      distanceToLinear f /
        (2 * ((Fintype.card F : ℝ) - 1) ^ 2 /
          (1 - Real.cos (2 * Real.pi / (Fintype.card F : ℝ)))) := by
  classical
  -- Positivity of the constant `C`.
  have hq_ge_2 : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast (Fact.out (p := (Fintype.card F).Prime)).two_le
  have hq_pos : (0 : ℝ) < (Fintype.card F : ℝ) := by linarith
  have hc_pos :
      0 < 1 - Real.cos (2 * Real.pi / (Fintype.card F : ℝ)) := by
    have hle : 2 * Real.pi / (Fintype.card F : ℝ) ≤ Real.pi := by
      rw [div_le_iff₀ hq_pos]; nlinarith [Real.pi_pos]
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hle (by positivity)
    rw [Real.cos_zero] at this; linarith
  have hq_m1_sq_pos : 0 < ((Fintype.card F : ℝ) - 1) ^ 2 := by nlinarith
  set C : ℝ := 2 * ((Fintype.card F : ℝ) - 1) ^ 2 /
      (1 - Real.cos (2 * Real.pi / (Fintype.card F : ℝ))) with hC_def
  have hC_pos : 0 < C := by rw [hC_def]; positivity
  -- Reduce via the equivalence.
  apply (rejection_distance_equivalence f C hC_pos).mp
  intro ε hε
  -- Step 1: BLR-phase satisfies the (2(q-1)²·ε, 1)-approx-rep bound.
  have hApprox := affineTest_isApproxRepresentation f ε hε
  -- Step 2: GH ⟹ ∃ linear ℓ with `distance f ℓ ≤ 2(q-1)²·ε / (1 - cos(2π/q))`.
  obtain ⟨ℓ, hlin, hdist⟩ :=
    gh_implies_near_linearity f
      (2 * ((Fintype.card F : ℝ) - 1) ^ 2 * ε) hApprox
  -- Step 3: `distanceToLinear f ≤ distance f ℓ ≤ C · ε`.
  refine (distanceToLinear_le_of_isLinear hlin).trans (hdist.trans_eq ?_)
  rw [hC_def]; ring

/-- The finite-field BLR acceptance probability is sandwiched between
completeness for linear functions and the GH-flavoured soundness bound, with
constant `C := 2 (q - 1)² / (1 - cos(2π/q))` and `q = |F|`.

GH-flavoured analogue of the finite-field `blr` theorem (which has the
sharper Fourier-form bound `acceptance ≤ 1 - δ(f, Lin)`, no constant). -/
theorem blr_gh
    [Fact (Nat.Prime (Fintype.card F))]
    (f : ScalarFn F Idx) :
    linearSetIndicator f ≤ acceptanceProbabilityBLR f ∧
      acceptanceProbabilityBLR f ≤
        1 - distanceToLinear f /
          (2 * ((Fintype.card F : ℝ) - 1) ^ 2 /
            (1 - Real.cos (2 * Real.pi / (Fintype.card F : ℝ)))) := by
  refine ⟨by simpa [linearSetIndicator] using (blr f).1, ?_⟩
  -- Convert `rejection ≥ δ/C` (from `blr_gh_soundness`) into `acceptance ≤ 1 - δ/C`.
  have hsound := blr_gh_soundness f
  unfold rejectionProbabilityBLR at hsound
  linarith

end BlrPcp
