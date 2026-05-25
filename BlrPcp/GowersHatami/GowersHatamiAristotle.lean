/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

set_option maxHeartbeats 800000

/-!
# The Gowers–Hatami Theorem

This file proves the Gowers–Hatami theorem on the stability of approximate unitary
representations of finite groups.

Given a finite group `Γ`, a finite-dimensional complex Hilbert space `H`, a positive
semi-definite operator `σ ∈ End(H)`, and `ε ≥ 0`, the theorem asserts that any
`(ε, σ)`-approximate unitary representation `ρ : Γ → U(H)` can be approximated by a
genuine unitary representation `ρ' : Γ → U(H')` on a (possibly larger) Hilbert space `H'`,
via a linear isometry `V : H → H'`, with error at most `2ε` in the averaged squared
`σ`-seminorm.

## Proof outline

The proof constructs `H' = ℓ²(Γ, H)` (the PiLp 2 product), embeds `H` via
`V(h)(x) = |Γ|⁻¹ᐟ² · ρ(x) h`, and takes `ρ'` to be the right regular representation
`(ρ'(g) f)(x) = f(x g)`. Then `V∗ ρ'(g) V = 𝔼_y [ρ(y)∗ ρ(y g)]`, and the bound
follows by Jensen's inequality for the `σ`-seminorm and left-unitary invariance.

## References

* [W. T. Gowers, O. Hatami, *Inverse and stability theorems for approximate
  representations of finite groups*, Sbornik: Mathematics 208(12):1784, 2017][GH17]

## Tags

approximate representation, stability, unitary representation, Gowers–Hatami
-/

noncomputable section

universe u

namespace GowersHatami

open scoped ComplexInnerProductSpace
open RCLike Finset

variable {Γ : Type u} [Group Γ] [Fintype Γ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-! ### The σ-Hilbert–Schmidt seminorm -/

/-- The squared `σ`-Hilbert–Schmidt seminorm of an operator `T ∈ End(H)`, defined as
`‖T‖²_σ = tr(T σ T∗) = ∑ᵢ Re ⟪T∗ bᵢ, σ(T∗ bᵢ)⟫`
where `{bᵢ}` is the standard orthonormal basis of `H`. -/
def sigmaNormSq (σ T : H →L[ℂ] H) : ℝ :=
  let b := stdOrthonormalBasis ℂ H
  ∑ i, re ⟪(star T) (b i), σ ((star T) (b i))⟫

/-! ### Approximate unitary representations -/

/-- A map `ρ : Γ → U(H)` is an **`(ε, σ)`-approximate unitary representation** if
`𝔼_{x,y} ‖ρ(xy) − ρ(x)ρ(y)‖²_σ ≤ ε`. -/
def IsApproxUnitaryRep (ε : ℝ) (σ : H →L[ℂ] H)
    (ρ : Γ → ↥(unitary (H →L[ℂ] H))) : Prop :=
  univ.expect (fun x => univ.expect (fun y =>
    sigmaNormSq σ ((ρ (x * y) : H →L[ℂ] H) - (ρ x : H →L[ℂ] H) * (ρ y : H →L[ℂ] H))))
      ≤ ε

/-! ### Conjugation by an isometry -/

/-- Conjugation of `T ∈ End(H')` by a linear isometry `V : H →ₗᵢ[ℂ] H'`:
`V∗ T V ∈ End(H)`. -/
def conjByIsometry {H' : Type u} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [FiniteDimensional ℂ H'] (V : H →ₗᵢ[ℂ] H') (T : H' →L[ℂ] H') : H →L[ℂ] H :=
  (ContinuousLinearMap.adjoint V.toContinuousLinearMap).comp (T.comp V.toContinuousLinearMap)

/-! ### Witness data -/

/-- Witness data for the Gowers–Hatami theorem: a target space `H'`, isometry `V`, and
genuine unitary representation `ρ'`. -/
structure UnitaryApprox (Γ : Type u) [Group Γ] [Fintype Γ]
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] where
  H' : Type u
  [instNACG : NormedAddCommGroup H']
  [instIPS : InnerProductSpace ℂ H']
  [instFD : FiniteDimensional ℂ H']
  V : H →ₗᵢ[ℂ] H'
  ρ' : Γ →* ↥(unitary (H' →L[ℂ] H'))

attribute [instance] UnitaryApprox.instNACG UnitaryApprox.instIPS UnitaryApprox.instFD

/-! ### Properties of the σ-seminorm -/

section SigmaNormProperties

/-- The `σ`-seminorm is nonneg when `σ` is positive semi-definite. -/
lemma sigmaNormSq_nonneg (σ : H →L[ℂ] H) (hσ : σ.IsPositive) (T : H →L[ℂ] H) :
    0 ≤ sigmaNormSq σ T :=
  Finset.sum_nonneg fun i _ =>
    (RCLike.nonneg_iff.mp (hσ.inner_nonneg_right ((star T) (stdOrthonormalBasis ℂ H i)))).1

/-- Negation invariance: `‖-T‖²_σ = ‖T‖²_σ`. -/
lemma sigmaNormSq_neg (σ T : H →L[ℂ] H) :
    sigmaNormSq σ (-T) = sigmaNormSq σ T := by
  simp only [sigmaNormSq, star_neg, ContinuousLinearMap.neg_apply, inner_neg_left, inner_neg_right,
    map_neg, neg_neg]

/-
The `σ`-seminorm expressed as `re(trace(T σ T∗))`.
-/
lemma sigmaNormSq_eq_re_trace (σ T : H →L[ℂ] H) :
    sigmaNormSq σ T =
      re (LinearMap.trace ℂ H (T * σ * star T : H →L[ℂ] H).toLinearMap) := by
  nontriviality;
  have h_trace : ∀ (A : H →ₗ[ℂ] H), (LinearMap.trace ℂ H) A = ∑ i, ⟪(stdOrthonormalBasis ℂ H) i, A ((stdOrthonormalBasis ℂ H) i)⟫ := by
    intro A
    have h_trace_def : (LinearMap.trace ℂ H) A = ∑ i, (A.toMatrix (stdOrthonormalBasis ℂ H).toBasis (stdOrthonormalBasis ℂ H).toBasis) i i := by
      convert LinearMap.trace_eq_matrix_trace ℂ ( stdOrthonormalBasis ℂ H ).toBasis A;
    simp_all +decide [ LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply ];
  simp +decide [ h_trace, sigmaNormSq ];
  simp +decide [ star, ContinuousLinearMap.adjoint_inner_left ]

/-
Left multiplication by a unitary preserves the `σ`-seminorm. Proved via the trace
identity `‖UT‖²_σ = re tr(U T σ T∗ U∗) = re tr(T σ T∗) = ‖T‖²_σ`.
-/
lemma sigmaNormSq_comp_unitary_left (σ T : H →L[ℂ] H) (U : ↥(unitary (H →L[ℂ] H))) :
    sigmaNormSq σ (↑U * T) = sigmaNormSq σ T := by
  convert sigmaNormSq_eq_re_trace σ ( ↑U * T ) using 1;
  -- Use the fact that `U * star U = 1` to simplify the expression.
  have h_U_star_U : (U : H →L[ℂ] H) * star U = 1 := by
    convert U.2.2;
  convert sigmaNormSq_eq_re_trace σ T using 1;
  -- Apply the cyclic property of the trace: trace(AB) = trace(BA).
  have h_trace_cyclic : LinearMap.trace ℂ H ((U : H →L[ℂ] H) * (T * σ * star T) * star U).toLinearMap = LinearMap.trace ℂ H ((T * σ * star T) * star U * U).toLinearMap := by
    have h_trace_cyclic : ∀ (A B : H →L[ℂ] H), LinearMap.trace ℂ H (A * B).toLinearMap = LinearMap.trace ℂ H (B * A).toLinearMap := by
      intro A B; exact (by
      convert LinearMap.trace_mul_comm ℂ ( A.toLinearMap ) ( B.toLinearMap ) using 1);
    convert h_trace_cyclic ( U ) ( ( T * σ * star T ) * star U ) using 1;
  convert congr_arg re h_trace_cyclic using 2;
  · simp +decide [ mul_assoc ];
  · simp +decide [ mul_assoc, U.2.1 ]

/-
Jensen's inequality for the `σ`-seminorm: for any positive semi-definite `σ`,
`‖c • ∑ᵢ Tᵢ‖²_σ ≤ c • ∑ᵢ ‖Tᵢ‖²_σ` where `c = |ι|⁻¹`.
-/
lemma sigmaNormSq_smul_sum_le (σ : H →L[ℂ] H) (hσ : σ.IsPositive)
    {ι : Type*} [Fintype ι] [Nonempty ι] (T : ι → H →L[ℂ] H) :
    sigmaNormSq σ (((Fintype.card ι : ℝ) : ℂ)⁻¹ • ∑ i : ι, T i) ≤
      (Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, sigmaNormSq σ (T i) := by
  have h_jensen : sigmaNormSq σ (∑ i, T i) ≤ (Fintype.card ι) * ∑ i, sigmaNormSq σ (T i) := by
    -- By the properties of the trace and the linearity of the inner product, we can expand the left-hand side.
    have h_expand : re (LinearMap.trace ℂ H (∑ i, ∑ j, (T i * σ * star (T j)).toLinearMap)) ≤ (Fintype.card ι) * ∑ i, re (LinearMap.trace ℂ H ((T i * σ * star (T i)).toLinearMap)) := by
      -- By the properties of the trace and the linearity of the inner product, we can expand the left-hand side and simplify.
      have h_expand : ∑ i, ∑ j, re (LinearMap.trace ℂ H ((T i * σ * star (T j)).toLinearMap)) + ∑ i, ∑ j, re (LinearMap.trace ℂ H ((T j * σ * star (T i)).toLinearMap)) ≤ ∑ i, ∑ j, (re (LinearMap.trace ℂ H ((T i * σ * star (T i)).toLinearMap)) + re (LinearMap.trace ℂ H ((T j * σ * star (T j)).toLinearMap))) := by
        have h_expand : ∀ i j, re (LinearMap.trace ℂ H ((T i * σ * star (T j)).toLinearMap)) + re (LinearMap.trace ℂ H ((T j * σ * star (T i)).toLinearMap)) ≤ re (LinearMap.trace ℂ H ((T i * σ * star (T i)).toLinearMap)) + re (LinearMap.trace ℂ H ((T j * σ * star (T j)).toLinearMap)) := by
          intro i j;
          have h_nonneg : 0 ≤ sigmaNormSq σ (T i - T j) := by
            exact sigmaNormSq_nonneg σ hσ _;
          simp_all +decide [ sigmaNormSq_eq_re_trace, sub_mul, mul_sub ];
          linarith;
        simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h_expand i j;
      convert div_le_div_of_nonneg_right h_expand ( show ( 0 : ℝ ) ≤ 2 by norm_num ) using 1 <;> norm_num [ Finset.sum_add_distrib ] ; ring;
      · rw [ ← Finset.sum_comm ] ; ring;
      · rw [ ← Finset.mul_sum _ _ _ ] ; ring;
    convert h_expand using 1;
    · convert sigmaNormSq_eq_re_trace σ ( ∑ i, T i ) using 2;
      simp +decide [ Finset.sum_mul _ _ _, Finset.mul_sum, star_sum ];
    · exact congrArg _ ( Finset.sum_congr rfl fun _ _ => sigmaNormSq_eq_re_trace _ _ );
  have h_homogeneous : ∀ (c : ℂ) (T : H →L[ℂ] H), sigmaNormSq σ (c • T) = ‖c‖^2 * sigmaNormSq σ T := by
    intros c T
    simp [sigmaNormSq, star_smul];
    simp +decide [ Complex.normSq, Complex.sq_norm, Finset.mul_sum _ _ _ ];
    exact Finset.sum_congr rfl fun x _ => by ring
  convert mul_le_mul_of_nonneg_left h_jensen ( sq_nonneg ( ( Fintype.card ι : ℝ ) ⁻¹ ) ) using 1 <;> norm_num [ h_homogeneous ] ; ring;
  simp +decide [ sq, ne_of_gt ( Fintype.card_pos ) ]

end SigmaNormProperties

/-! ### The witness construction -/

section Construction

/-- The target Hilbert space `ℓ²(Γ, H) = PiLp 2 (fun _ : Γ => H)`. -/
abbrev TargetSpace (Γ : Type u) (H : Type u) := PiLp 2 (fun _ : Γ => H)

/-- Scaling factor for the embedding: `√(|Γ|⁻¹)`, as a complex number. -/
def embScale (Γ : Type u) [Fintype Γ] : ℂ :=
  (Real.sqrt ((Fintype.card Γ : ℝ)⁻¹) : ℝ)

variable (Γ) in
/-- The right regular representation on `ℓ²(Γ, H)`, given by `(ρ_R(g) f)(x) = f(x g)`.
This is a `LinearIsometryEquiv` since it permutes coordinates.

`piLpCongrLeft 2 ℂ H (Equiv.mulRight g⁻¹)` sends `f` to `f ∘ (mulRight g⁻¹).symm = f ∘ mulRight g`,
i.e. `(ρ_R(g) f)(x) = f(x g)` as required. -/
def rightRegLIE (g : Γ) :
    TargetSpace Γ H ≃ₗᵢ[ℂ] TargetSpace Γ H :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ H (Equiv.mulRight g⁻¹)

variable (Γ) in
/-- The right regular representation as a `ContinuousLinearMap`. -/
def rightRegCLM (g : Γ) :
    TargetSpace Γ H →L[ℂ] TargetSpace Γ H :=
  (rightRegLIE Γ (H := H) g).toContinuousLinearEquiv.toContinuousLinearMap

variable (Γ) in
/-- The right regular representation is unitary. -/
lemma rightRegCLM_mem_unitary (g : Γ) :
    rightRegCLM Γ (H := H) g ∈ unitary (TargetSpace Γ H →L[ℂ] TargetSpace Γ H) := by
  simp +decide [ rightRegCLM ];
  constructor <;> simp +decide [ rightRegLIE ] ;
  · ext; simp +decide [ Equiv.mulRight ] ;
  · ext; simp +decide [ LinearIsometryEquiv.toContinuousLinearEquiv ] ;

variable (Γ) in
/-- The right regular representation as a monoid homomorphism to the unitary group. -/
def rightRegularRep :
    Γ →* ↥(unitary (TargetSpace Γ H →L[ℂ] TargetSpace Γ H)) where
  toFun g := ⟨rightRegCLM Γ g, rightRegCLM_mem_unitary Γ g⟩
  map_one' := by
    ext; simp [rightRegCLM, rightRegLIE]
  map_mul' x y := by
    simp +decide [ ContinuousLinearMap.ext_iff ];
    intro z
    simp [rightRegCLM, rightRegLIE]
    exact LinearIsometryEquiv.congr_arg rfl

/-- The linear map underlying the isometric embedding `V : H → ℓ²(Γ, H)`, defined by
`V(h)(x) = √(|Γ|⁻¹) · ρ(x) h`. -/
def mkIsometryLM (ρ : Γ → ↥(unitary (H →L[ℂ] H))) :
    H →ₗ[ℂ] TargetSpace Γ H :=
  (WithLp.linearEquiv 2 ℂ (Γ → H)).symm.toLinearMap.comp
    (LinearMap.pi (fun x =>
      ((embScale Γ : ℂ) • (ρ x : H →L[ℂ] H)).toLinearMap))

/-
The isometric embedding `V : H → ℓ²(Γ, H)` defined by
`V(h)(x) = √(|Γ|⁻¹) · ρ(x) h`.
-/
def mkIsometry (ρ : Γ → ↥(unitary (H →L[ℂ] H))) : H →ₗᵢ[ℂ] TargetSpace Γ H where
  toLinearMap := mkIsometryLM ρ
  norm_map' := by
    intro x
    have h_norm_sq : ‖(mkIsometryLM ρ) x‖ ^ 2 = ∑ i : Γ, ‖(embScale Γ • (ρ i : H →L[ℂ] H)) x‖ ^ 2 := by
      rw [ PiLp.norm_sq_eq_of_L2 ] ; aesop;
    generalize_proofs at *; (
    -- Since `ρ x` is unitary, `‖(ρ x) h‖ = ‖h‖`.
    have h_unitary : ∀ i : Γ, ‖(ρ i : H →L[ℂ] H) x‖ = ‖x‖ := by
      grind +suggestions
    generalize_proofs at *; (
    simp_all +decide [ embScale, norm_smul ];
    rw [ ← sq_eq_sq₀ ( norm_nonneg _ ) ( norm_nonneg _ ), h_norm_sq ] ; ring ; norm_num [ ne_of_gt ( Fintype.card_pos ) ] ;))

/-- The `UnitaryApprox` witness for the Gowers–Hatami theorem. -/
def mkWitness (ρ : Γ → ↥(unitary (H →L[ℂ] H))) : UnitaryApprox Γ H where
  H' := TargetSpace Γ H
  V := mkIsometry ρ
  ρ' := rightRegularRep Γ

end Construction

/-! ### The averaged operator and key computation -/

section KeyComputation

/-- The averaged operator `𝔼_y [ρ(y)∗ ρ(y g)]`. This is what `V∗ ρ'(g) V` computes. -/
def avgOp (ρ : Γ → ↥(unitary (H →L[ℂ] H))) (g : Γ) : H →L[ℂ] H :=
  ((Fintype.card Γ : ℝ) : ℂ)⁻¹ •
    ∑ y : Γ, star (ρ y : H →L[ℂ] H) * (ρ (y * g) : H →L[ℂ] H)

/-
The conjugation `V∗ ρ'(g) V` equals the averaged operator `𝔼_y [ρ(y)∗ ρ(yg)]`.
-/
lemma conjByIsometry_mkWitness_eq (ρ : Γ → ↥(unitary (H →L[ℂ] H))) (g : Γ) :
    conjByIsometry (mkIsometry ρ)
      ((rightRegularRep (H := H) Γ g : TargetSpace Γ H →L[ℂ] _)) =
      avgOp ρ g := by
  refine' ContinuousLinearMap.ext fun h => _;
  refine' ext_inner_left ℂ _;
  intro v; simp +decide [ conjByIsometry, avgOp ] ;
  -- By definition of adjoint, we have:
  have h_adj : ∀ (f : TargetSpace Γ H), (ContinuousLinearMap.adjoint (mkIsometry ρ).toContinuousLinearMap) f = (embScale Γ : ℂ) • ∑ x : Γ, (star (ρ x : H →L[ℂ] H)) (f x) := by
    intro f
    have h_adj : ∀ (h : H), inner ℂ ((mkIsometry ρ).toContinuousLinearMap h) f = inner ℂ h ((embScale Γ : ℂ) • ∑ x : Γ, (star (ρ x : H →L[ℂ] H)) (f.ofLp x)) := by
      intro h
      simp [mkIsometry, mkIsometryLM, PiLp.inner_apply];
      simp +decide [ embScale, inner_smul_left, Finset.mul_sum _ _ _ ];
      simp +decide [ ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right ];
    refine' ext_inner_left ℂ _;
    intro v; rw [ ← h_adj v, ContinuousLinearMap.adjoint_inner_right ] ;
  simp +decide [ h_adj, rightRegularRep, rightRegCLM, rightRegLIE ];
  simp +decide [ embScale, mkIsometry, mkIsometryLM ];
  simp +decide [ inner_smul_right, inner_sum, Finset.mul_sum _ _ _ ];
  refine Finset.sum_congr rfl fun i _ => ?_;
  rw [ ← mul_assoc ]; congr 1;
  rw [ ← mul_inv ]; congr 1;
  rw [ ← Complex.ofReal_mul, Real.mul_self_sqrt ( by positivity ) ]; norm_cast

end KeyComputation

/-! ### The main error bound -/

section ErrorBound

/-
The key bound: `𝔼_x ‖ρ(x) − avgOp ρ x‖²_σ ≤ 𝔼_{x,y} ‖ρ(xy) − ρ(x)ρ(y)‖²_σ`.

The proof proceeds as follows. For each fixed `x`:
1. Write `ρ(x) − avgOp(ρ, x) = (|Γ|⁻¹) • ∑_y [ρ(y)∗ (ρ(y)ρ(x) − ρ(yx))]`.
2. By Jensen: `‖(|Γ|⁻¹) • ∑_y [⋯]‖²_σ ≤ |Γ|⁻¹ • ∑_y ‖ρ(y)∗ (ρ(y)ρ(x)−ρ(yx))‖²_σ`.
3. By left-unitary invariance: `= |Γ|⁻¹ • ∑_y ‖ρ(y)ρ(x) − ρ(yx)‖²_σ`.
4. By negation invariance: `= 𝔼_y ‖ρ(yx) − ρ(y)ρ(x)‖²_σ`.
Averaging over `x` and swapping the two averages yields the bound `ε`.
-/
lemma avg_error_le_approx_error (ε : ℝ) (σ : H →L[ℂ] H) (hσ : σ.IsPositive)
    (ρ : Γ → ↥(unitary (H →L[ℂ] H))) (hρ : IsApproxUnitaryRep ε σ ρ) :
    univ.expect (fun x =>
      sigmaNormSq σ ((ρ x : H →L[ℂ] H) - avgOp ρ x)) ≤ ε := by
  -- Apply the Jensen's inequality to rewrite the expectation inside the goal.
  have h_jensen : ∀ x : Γ, sigmaNormSq σ (ρ x - avgOp ρ x) ≤ (univ.expect fun y => sigmaNormSq σ ((ρ y * (ρ x : H →L[ℂ] H) - ρ (y * x) : H →L[ℂ] H))) := by
    intro x
    have h_sum : (ρ x : H →L[ℂ] H) - avgOp ρ x = (Fintype.card Γ : ℝ)⁻¹ • ∑ y : Γ, star (ρ y : H →L[ℂ] H) * ((ρ y : H →L[ℂ] H) * (ρ x : H →L[ℂ] H) - (ρ (y * x) : H →L[ℂ] H)) := by
      have h_sum : (ρ x : H →L[ℂ] H) - avgOp ρ x = (Fintype.card Γ : ℝ)⁻¹ • (∑ y : Γ, star (ρ y : H →L[ℂ] H) * ((ρ y : H →L[ℂ] H) * (ρ x : H →L[ℂ] H)) - ∑ y : Γ, star (ρ y : H →L[ℂ] H) * (ρ (y * x) : H →L[ℂ] H)) := by
        simp +decide [ avgOp, Finset.smul_sum, smul_sub ];
        have h_sum : ∑ y : Γ, star (ρ y : H →L[ℂ] H) * ((ρ y : H →L[ℂ] H) * (ρ x : H →L[ℂ] H)) = (Fintype.card Γ : ℝ) • (ρ x : H →L[ℂ] H) := by
          have h1 : ∀ y : Γ, star (ρ y : H →L[ℂ] H) * ((ρ y : H →L[ℂ] H) * (ρ x : H →L[ℂ] H)) = (ρ x : H →L[ℂ] H) := by
            intro y; rw [← mul_assoc, (ρ y).2.1, one_mul]
          rw [Finset.sum_congr rfl (fun y _ => h1 y), Finset.sum_const, Finset.card_univ];
          norm_num [ Algebra.smul_def ];
        simp_all +decide [ ← Finset.smul_sum ];
        module;
      simp_all +decide [ mul_sub, Finset.sum_sub_distrib ];
    -- Apply Jensen's inequality to the sum.
    have h_jensen : sigmaNormSq σ ((Fintype.card Γ : ℝ)⁻¹ • ∑ y : Γ, star (ρ y : H →L[ℂ] H) * ((ρ y : H →L[ℂ] H) * (ρ x : H →L[ℂ] H) - (ρ (y * x) : H →L[ℂ] H))) ≤ (Fintype.card Γ : ℝ)⁻¹ * ∑ y : Γ, sigmaNormSq σ (star (ρ y : H →L[ℂ] H) * ((ρ y : H →L[ℂ] H) * (ρ x : H →L[ℂ] H) - (ρ (y * x) : H →L[ℂ] H))) := by
      haveI : Nonempty Γ := ⟨x⟩
      rw [← Complex.coe_smul, Complex.ofReal_inv]
      exact sigmaNormSq_smul_sum_le σ hσ
        (fun y : Γ => star (ρ y : H →L[ℂ] H) * ((ρ y : H →L[ℂ] H) * (ρ x : H →L[ℂ] H) - (ρ (y * x) : H →L[ℂ] H)))
    -- Apply the left-unitary invariance to each term in the sum.
    have h_left_unitary : ∀ y : Γ, sigmaNormSq σ (star (ρ y : H →L[ℂ] H) * ((ρ y : H →L[ℂ] H) * (ρ x : H →L[ℂ] H) - (ρ (y * x) : H →L[ℂ] H))) = sigmaNormSq σ ((ρ y : H →L[ℂ] H) * (ρ x : H →L[ℂ] H) - (ρ (y * x) : H →L[ℂ] H)) := by
      intro y
      simpa [Unitary.coe_star] using
        sigmaNormSq_comp_unitary_left σ ((ρ y : H →L[ℂ] H) * (ρ x : H →L[ℂ] H) - (ρ (y * x) : H →L[ℂ] H)) (star (ρ y))
    rw [h_sum]
    refine le_trans h_jensen (le_of_eq ?_)
    rw [Finset.sum_congr rfl (fun y _ => h_left_unitary y), Fintype.expect_eq_sum_div_card,
      div_eq_inv_mul]
  have h_jensen' : ∀ x : Γ, sigmaNormSq σ (ρ x - avgOp ρ x) ≤ (univ.expect fun y => sigmaNormSq σ ((ρ (y * x) : H →L[ℂ] H) - (ρ y * (ρ x : H →L[ℂ] H)))) := by
    convert h_jensen using 3; simp_all +decide;
    convert sigmaNormSq_neg σ _ using 2 ; abel_nf;
  refine' le_trans (Finset.expect_le_expect fun x _ => h_jensen' x) _;
  rw [Finset.expect_comm];
  exact hρ

end ErrorBound

/-! ### Main theorem -/

/-- **Gowers–Hatami theorem.** Let `Γ` be a finite group, `H` a finite-dimensional complex
Hilbert space, `σ ∈ End(H)` a positive semi-definite operator, and `ε ≥ 0`.

If `ρ : Γ → U(H)` is an `(ε, σ)`-approximate unitary representation, then there exist
a finite-dimensional Hilbert space `H'`, a linear isometry `V : H →ₗᵢ[ℂ] H'`, and a
genuine unitary representation `ρ' : Γ →* U(H')` such that
`𝔼_x ‖ρ(x) − V∗ ρ'(x) V‖²_σ ≤ 2ε`. -/
theorem gowers_hatami (ε : ℝ) (hε : 0 ≤ ε) (σ : H →L[ℂ] H) (hσ : σ.IsPositive)
    (ρ : Γ → ↥(unitary (H →L[ℂ] H))) (hρ : IsApproxUnitaryRep ε σ ρ) :
    ∃ (w : UnitaryApprox Γ H),
      univ.expect (fun x =>
        sigmaNormSq σ ((ρ x : H →L[ℂ] H) -
          conjByIsometry w.V (w.ρ' x : w.H' →L[ℂ] w.H'))) ≤ 2 * ε := by
  refine ⟨mkWitness ρ, ?_⟩
  show univ.expect (fun x =>
    sigmaNormSq σ ((ρ x : H →L[ℂ] H) -
      conjByIsometry (mkIsometry ρ)
        ((rightRegularRep (H := H) Γ x : TargetSpace Γ H →L[ℂ] _)))) ≤ 2 * ε
  simp_rw [conjByIsometry_mkWitness_eq]
  calc univ.expect (fun x =>
          sigmaNormSq σ ((ρ x : H →L[ℂ] H) - avgOp ρ x))
      ≤ ε := avg_error_le_approx_error ε σ hσ ρ hρ
    _ ≤ 2 * ε := le_mul_of_one_le_left hε one_le_two

end GowersHatami