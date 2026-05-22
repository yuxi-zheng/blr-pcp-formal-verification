/-
Authors: Serhat Emre Coban, Davide Mazzali, Khanh Nguyen, Vincent Palma, Yanting Teng, Thomas Vidick, Yuxi Zheng
-/
import BlrPcp.FnFiniteFIelds.BLR
import BlrPcp.GowersHatami.GH2
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

set_option linter.unusedSectionVars false

/-!
# Gowers–Hatami for the BLR linearity test over `𝔽_q` (twisted-group route)

This file formalizes the blueprint `gh_blr.tex`, which proves soundness of the
BLR linearity test over a finite field via the Gowers–Hatami theorem applied to
the *twisted group* `G = X × A`, where `X = 𝔽_q^Idx` and `A = 𝔽_q^×`.

## Contents so far

* `Twist` — the carrier `X × A` equipped with the twisted operation
  `(x, a) ⋆ (y, b) = (b⁻¹ • x + a⁻¹ • y, a * b)` (blueprint `lem:group`),
  together with its `CommGroup`, `Fintype` and `DecidableEq` instances.
-/

namespace BlrPcp

open scoped Matrix

variable {F Idx : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]

/-- The carrier of the twisted group `G = X × A` from the blueprint, with
`X = 𝔽_q^Idx` (`Vec F Idx`) and `A = 𝔽_q^×` (`Fˣ`). -/
@[ext]
structure Twist (F Idx : Type*) [Field F] where
  /-- The `X = 𝔽_q^Idx` component. -/
  vec : Vec F Idx
  /-- The `A = 𝔽_q^×` component. -/
  unit : Fˣ

namespace Twist

/-- Twisted multiplication `(x, a) ⋆ (y, b) = (b⁻¹ • x + a⁻¹ • y, a * b)`. -/
instance : Mul (Twist F Idx) where
  mul p q := ⟨(↑q.unit⁻¹ : F) • p.vec + (↑p.unit⁻¹ : F) • q.vec, p.unit * q.unit⟩

/-- The identity element `(0, 1)`. -/
instance : One (Twist F Idx) where
  one := ⟨0, 1⟩

/-- The inverse `(x, a)⁻¹ = (-a² • x, a⁻¹)`. -/
instance : Inv (Twist F Idx) where
  inv p := ⟨(-(↑p.unit : F) ^ 2) • p.vec, p.unit⁻¹⟩

@[simp] lemma mul_vec (p q : Twist F Idx) :
    (p * q).vec = (↑q.unit⁻¹ : F) • p.vec + (↑p.unit⁻¹ : F) • q.vec := rfl

@[simp] lemma mul_unit (p q : Twist F Idx) : (p * q).unit = p.unit * q.unit := rfl

@[simp] lemma one_vec : (1 : Twist F Idx).vec = 0 := rfl

@[simp] lemma one_unit : (1 : Twist F Idx).unit = 1 := rfl

@[simp] lemma inv_vec (p : Twist F Idx) :
    p⁻¹.vec = (-(↑p.unit : F) ^ 2) • p.vec := rfl

@[simp] lemma inv_unit (p : Twist F Idx) : p⁻¹.unit = p.unit⁻¹ := rfl

/-- `Twist` is an abelian group under `⋆` (blueprint `lem:group`). -/
instance instCommGroup : CommGroup (Twist F Idx) where
  mul := (· * ·)
  one := 1
  inv := (·⁻¹)
  mul_assoc p q r := by
    apply Twist.ext
    · funext i
      simp only [mul_vec, mul_unit, mul_inv_rev, Units.val_mul,
        Units.val_inv_eq_inv_val, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [mul_unit, mul_assoc]
  one_mul p := by
    apply Twist.ext
    · simp [mul_vec, one_vec, one_unit]
    · simp [mul_unit, one_unit]
  mul_one p := by
    apply Twist.ext
    · simp [mul_vec, one_vec, one_unit]
    · simp [mul_unit, one_unit]
  inv_mul_cancel p := by
    have ha : (↑p.unit : F) ≠ 0 := p.unit.ne_zero
    apply Twist.ext
    · funext i
      simp only [mul_vec, inv_vec, inv_unit, one_vec, Units.val_inv_eq_inv_val,
        inv_inv, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
      field_simp
      ring
    · simp [mul_unit, inv_unit]
  mul_comm p q := by
    apply Twist.ext
    · simp only [mul_vec]
      exact add_comm _ _
    · simp only [mul_unit]
      exact mul_comm _ _

/-- `Twist` is, as a bare type, just `X × A`. -/
@[simps]
def equivProd : Twist F Idx ≃ Vec F Idx × Fˣ where
  toFun p := (p.vec, p.unit)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (Twist F Idx) := Fintype.ofEquiv _ equivProd.symm

instance : DecidableEq (Twist F Idx) := equivProd.decidableEq

/-- The order of the twisted group: `|G| = |X| · |A| = q^{|Idx|} · (q - 1)`. -/
lemma card_eq :
    Fintype.card (Twist F Idx) = Fintype.card (Vec F Idx) * Fintype.card Fˣ := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod]

end Twist

/-! ## The matrix lift `F_f` (blueprint `eq:Flift-def`)

`F_f(x, a) = D(a f(x)) = ∑_{c ∈ A} ω^{Tr(c · a · f(x))} |c⟩⟨c|`, the diagonal
unitary on `ℂ^A ≅ ℂ^{q-1}`. Here `ω = exp(2πi/p)`, `Tr : 𝔽_q → 𝔽_p` is the field
trace, and the character `z ↦ ω^{Tr z}` is `baseChar`.
-/

/-- The matrix lift `F_f(x, a)` (blueprint `eq:Flift-def`): the diagonal matrix on
`ℂ^A` (`A = 𝔽_q^×`) whose `c`-th diagonal entry is `ω^{Tr(c · a · f(x))}`. -/
noncomputable def liftMatrix (f : ScalarFn F Idx) (p : Twist F Idx) :
    Matrix Fˣ Fˣ ℂ :=
  Matrix.diagonal fun c : Fˣ => baseChar (F := F) ((c : F) * (p.unit : F) * f p.vec)

/-- `F_f` is unitary-valued, `F_f : G → U(ℂ^{q-1})` (blueprint `eq:Flift-def`):
the lift is diagonal with unit-modulus entries `‖ω^{Tr(·)}‖ = 1`. -/
lemma liftMatrix_mem_unitaryGroup (f : ScalarFn F Idx) (p : Twist F Idx) :
    liftMatrix f p ∈ Matrix.unitaryGroup Fˣ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, liftMatrix, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext c
  simp only [Pi.star_apply]
  have hz : ‖baseChar (F := F) ((c : F) * (p.unit : F) * f p.vec)‖ = 1 :=
    AddChar.norm_apply _ _
  have hne : baseChar (F := F) ((c : F) * (p.unit : F) * f p.vec) ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact one_ne_zero hz.symm
  rw [← starRingEnd_apply, ← Complex.inv_eq_conj hz]
  exact mul_inv_cancel₀ hne

/-! ## M5 setup: the weight `σ = I/(q-1)` (blueprint `eq:Flift-def`)

The blueprint takes `σ = I/(q-1)`, the normalized identity on `ℂ^A`, as the
density matrix defining the `σ`-inner product `⟨A,B⟩_σ = Tr(A* B σ)`.
-/

/-- The blueprint weight `σ = I/(q-1)`: the normalized identity on `ℂ^A`. -/
noncomputable def sigmaBLR : Matrix Fˣ Fˣ ℂ := (Fintype.card Fˣ : ℂ)⁻¹ • 1

/-- `σ` has unit trace, i.e. it is a density matrix (blueprint `eq:Flift-def`). -/
lemma sigmaBLR_trace : (sigmaBLR (F := F)).trace = 1 := by
  haveI : Nonempty Fˣ := ⟨1⟩
  have hne : (Fintype.card Fˣ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [sigmaBLR, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, inv_mul_cancel₀ hne]

/-! ## M5: the character sum behind `lem:rep-iff-blr`

The diagonal entries of `F_f` are values of `baseChar`, so the σ-correlation
of the lift reduces to the additive-character sum `∑_{c ∈ A} ω^{Tr(c·w)}`, which
equals `q-1` when `w = 0` and `-1` otherwise (`A = 𝔽_q^×`).
-/

/-- For a field, the units biject with the nonzero elements. -/
private def unitsEquivNeZero : Fˣ ≃ {x : F // x ≠ 0} where
  toFun u := ⟨(u : F), u.ne_zero⟩
  invFun x := Units.mk0 x.1 x.2
  left_inv _ := Units.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Summing a function over the units equals its full-field sum minus the value at `0`. -/
private lemma sum_units_eq_sum_sub (g : F → ℂ) :
    ∑ c : Fˣ, g (c : F) = (∑ c : F, g c) - g 0 := by
  classical
  rw [eq_sub_iff_add_eq, add_comm, sum_univ_eq_zero_add_sum_nonzero g]
  congr 1
  rw [Finset.sum_subtype (nonzeroF (F := F)) (p := fun x => x ≠ 0)
    (fun x => by simp [nonzeroF]) g]
  exact Equiv.sum_comp unitsEquivNeZero (fun x : {x : F // x ≠ 0} => g (x : F))

/-- The character sum over `A = 𝔽_q^×`: `∑_{c ∈ A} ω^{Tr(c·w)}` is `q-1` if `w = 0`
and `-1` otherwise (the core identity behind `lem:rep-iff-blr`). -/
lemma baseChar_units_sum (w : F) :
    ∑ c : Fˣ, baseChar (F := F) ((c : F) * w)
      = if w = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  classical
  haveI : Nonempty F := ⟨0⟩
  have hcardF : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hfull : ∑ c : F, baseChar (F := F) (c * w)
      = if w = 0 then (Fintype.card F : ℂ) else 0 := by
    have h := character_sum_indicator_eq (F := F) w 0
    simp only [sub_zero] at h
    have key : (Fintype.card F : ℂ) * (if w = 0 then (1 : ℂ) else 0)
        = ∑ c : F, baseChar (F := F) (c * w) := by
      rw [h, ← mul_assoc, mul_inv_cancel₀ hcardF, one_mul]
    rw [← key]; split <;> simp
  rw [sum_units_eq_sum_sub (fun c => baseChar (F := F) (c * w)), hfull, zero_mul,
    AddChar.map_zero_eq_one]
  split_ifs with hw
  · rw [Fintype.card_units, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  · ring

/-! ## M5: the per-pair correlation of the lift

The blueprint's `lem:rep-iff-blr` rests on computing, for `g, h ∈ G`, the
σ-correlation `⟨F_f(g) F_f(h), F_f(g·h)⟩_σ`.  Because `F_f` is diagonal, this
collapses to the character sum above, evaluated at the *homomorphism defect*
`w(g,h) = a_{gh} f(x_{gh}) − a_g f(x_g) − a_h f(x_h)`.
-/

/-- The exponent datum `a · f(x)` of `F_f` at a group element (so the `c`-th
diagonal entry of `F_f(p)` is `ω^{Tr(c · liftPhase p)}`). -/
def liftPhase (f : ScalarFn F Idx) (p : Twist F Idx) : F := (p.unit : F) * f p.vec

lemma liftMatrix_diagonal (f : ScalarFn F Idx) (p : Twist F Idx) :
    liftMatrix f p = Matrix.diagonal fun c : Fˣ => baseChar (F := F) ((c : F) * liftPhase f p) := by
  unfold liftMatrix liftPhase
  congr 1
  funext c
  rw [mul_assoc]

/-- `σ = I/(q-1)` written as a diagonal matrix. -/
lemma sigmaBLR_diagonal :
    sigmaBLR (F := F) = Matrix.diagonal fun _ : Fˣ => (Fintype.card Fˣ : ℂ)⁻¹ := by
  rw [sigmaBLR, Matrix.smul_one_eq_diagonal]

/-- The complex conjugate of a character value is the character at the negation. -/
lemma star_baseChar (t : F) : star (baseChar (F := F) t) = baseChar (F := F) (-t) := by
  rw [← starRingEnd_apply, ← Complex.inv_eq_conj (AddChar.norm_apply _ _), AddChar.map_neg_eq_inv]

/-- The pointwise diagonal entry of the correlation product is a single character
value at the homomorphism defect. -/
lemma lift_entry_eq (f : ScalarFn F Idx) (g h : Twist F Idx) (c : Fˣ) :
    star (baseChar (F := F) ((c : F) * liftPhase f g) *
          baseChar (F := F) ((c : F) * liftPhase f h)) *
        baseChar (F := F) ((c : F) * liftPhase f (g * h))
      = baseChar (F := F) ((c : F) *
          (liftPhase f (g * h) - liftPhase f g - liftPhase f h)) := by
  rw [← AddChar.map_add_eq_mul, star_baseChar, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The σ-correlation of the lift at `(g,h)` reduces to the character sum at the
homomorphism defect. -/
lemma lift_trace_eq (f : ScalarFn F Idx) (g h : Twist F Idx) :
    Matrix.trace ((liftMatrix f g * liftMatrix f h)ᴴ * liftMatrix f (g * h) * sigmaBLR)
      = (Fintype.card Fˣ : ℂ)⁻¹ * ∑ c : Fˣ,
          baseChar (F := F) ((c : F) * (liftPhase f (g * h) - liftPhase f g - liftPhase f h)) := by
  rw [liftMatrix_diagonal f g, liftMatrix_diagonal f h, liftMatrix_diagonal f (g * h),
    sigmaBLR_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Pi.star_apply]
  rw [lift_entry_eq f g h c]
  ring

/-- **Per-pair correlation** (core of `lem:rep-iff-blr`): the σ-correlation of the
lift at `(g,h)` is `1` when the homomorphism defect vanishes and `-1/(q-1)`
otherwise. -/
lemma lift_pair_correlation (f : ScalarFn F Idx) (g h : Twist F Idx) :
    Matrix.trace ((liftMatrix f g * liftMatrix f h)ᴴ * liftMatrix f (g * h) * sigmaBLR)
      = if liftPhase f (g * h) - liftPhase f g - liftPhase f h = 0
          then 1 else -(Fintype.card Fˣ : ℂ)⁻¹ := by
  haveI : Nonempty Fˣ := ⟨1⟩
  have hne : (Fintype.card Fˣ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [lift_trace_eq, baseChar_units_sum]
  split_ifs with hw
  · exact inv_mul_cancel₀ hne
  · ring

/-- **The homomorphism defect vanishes iff the BLR test accepts** (blueprint
`eq:rep-eq-blr`).  For `g = (x,a)`, `h = (y,b)`, the defect is zero exactly when
the BLR test accepts `f` at scalars `(b⁻¹, a⁻¹)` and points `(x, y)`. -/
lemma defect_eq_zero_iff (f : ScalarFn F Idx) (g h : Twist F Idx) :
    liftPhase f (g * h) - liftPhase f g - liftPhase f h = 0
      ↔ BLRAcceptsAt f (↑h.unit⁻¹) (↑g.unit⁻¹) g.vec h.vec := by
  have hWvec : (g * h).vec
      = fun i => (↑h.unit⁻¹ : F) * g.vec i + (↑g.unit⁻¹ : F) * h.vec i := by
    funext i; simp [Twist.mul_vec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hga : (↑g.unit : F) ≠ 0 := g.unit.ne_zero
  have hhb : (↑h.unit : F) ≠ 0 := h.unit.ne_zero
  unfold liftPhase BLRAcceptsAt
  rw [Twist.mul_unit, hWvec]
  set A := f g.vec
  set B := f h.vec
  set C := f fun i => (↑h.unit⁻¹ : F) * g.vec i + (↑g.unit⁻¹ : F) * h.vec i
  have hab : (↑(g.unit * h.unit) : F) ≠ 0 := by
    rw [Units.val_mul]; exact mul_ne_zero hga hhb
  have hkey : (↑(g.unit * h.unit) : F) * C - ↑g.unit * A - ↑h.unit * B
      = ↑(g.unit * h.unit) * (C - (↑h.unit⁻¹ * A + ↑g.unit⁻¹ * B)) := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
    field_simp
    ring
  rw [hkey, mul_eq_zero, sub_eq_zero, or_iff_right hab]
  exact eq_comm

/-! ## M5: bridge to GH2's `sigmaInner` over `Fin (q-1)`

GH2's `IsApproxRepresentation`/`gh2_average_correlation` work over `Matrix (Fin d)`,
so we reindex `Fˣ ≃ Fin (q-1)`. Trace is reindex-invariant, so GH2's `sigmaInner`
of reindexed matrices equals the `Fˣ`-trace we computed above.
-/

/-- Trace is invariant under reindexing by an equivalence. -/
lemma trace_reindex_self {n : ℕ} (e : Fˣ ≃ Fin n) (M : Matrix Fˣ Fˣ ℂ) :
    Matrix.trace (Matrix.reindex e e M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm fun c => M c c

/-- GH2's `sigmaInner` of reindexed matrices is the `Fˣ`-trace `Tr(Aᴴ B σ)`. -/
lemma sigmaInner_reindex {n : ℕ} (e : Fˣ ≃ Fin n) (σ A B : Matrix Fˣ Fˣ ℂ) :
    sigmaInner (Matrix.reindex e e σ) (Matrix.reindex e e A) (Matrix.reindex e e B)
      = Matrix.trace (Aᴴ * B * σ) := by
  unfold sigmaInner
  rw [Matrix.conjTranspose_reindex,
    show Matrix.reindex e e Aᴴ * Matrix.reindex e e B = Matrix.reindex e e (Aᴴ * B)
      from Matrix.reindexLinearEquiv_mul ℂ ℂ e e e Aᴴ B,
    show Matrix.reindex e e (Aᴴ * B) * Matrix.reindex e e σ = Matrix.reindex e e (Aᴴ * B * σ)
      from Matrix.reindexLinearEquiv_mul ℂ ℂ e e e (Aᴴ * B) σ,
    trace_reindex_self]

/-! ## M5: the lift and weight over `Fin (q-1)` (GH2-ready) -/

/-- The canonical reindexing `Fˣ ≃ Fin (q-1)` (`|Fˣ| = q-1`). -/
noncomputable def eFin : Fˣ ≃ Fin (Fintype.card Fˣ) := Fintype.equivFin Fˣ

/-- The lift `F_f` transported to `Matrix (Fin (q-1))`, ready for GH2. -/
noncomputable def liftFin (f : ScalarFn F Idx) (p : Twist F Idx) :
    Matrix (Fin (Fintype.card Fˣ)) (Fin (Fintype.card Fˣ)) ℂ :=
  Matrix.reindex eFin eFin (liftMatrix f p)

/-- `σ = I/(q-1)` transported to `Matrix (Fin (q-1))`. -/
noncomputable def sigmaFin : Matrix (Fin (Fintype.card Fˣ)) (Fin (Fintype.card Fˣ)) ℂ :=
  Matrix.reindex eFin eFin sigmaBLR

/-- `liftFin` is unitary-valued (reindexing preserves unitarity). -/
lemma liftFin_unitary (f : ScalarFn F Idx) (p : Twist F Idx) :
    liftFin f p ∈ Matrix.unitaryGroup (Fin (Fintype.card Fˣ)) ℂ := by
  have h1 : liftMatrix f p * (liftMatrix f p)ᴴ = 1 := by
    have h := liftMatrix_mem_unitaryGroup f p
    rwa [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
  rw [Matrix.mem_unitaryGroup_iff, liftFin, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_reindex,
    show Matrix.reindex eFin eFin (liftMatrix f p) * Matrix.reindex eFin eFin ((liftMatrix f p)ᴴ)
        = Matrix.reindex eFin eFin (liftMatrix f p * (liftMatrix f p)ᴴ)
      from Matrix.reindexLinearEquiv_mul ℂ ℂ eFin eFin eFin (liftMatrix f p) ((liftMatrix f p)ᴴ),
    h1]
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply, eFin.symm.injective.eq_iff]

/-- **Per-pair correlation over `Fin`** (GH2's `sigmaInner`): `1` if the
homomorphism defect vanishes, `-1/(q-1)` otherwise. -/
lemma liftFin_pair_correlation (f : ScalarFn F Idx) (g h : Twist F Idx) :
    (sigmaInner sigmaFin (liftFin f g * liftFin f h) (liftFin f (g * h))).re
      = if liftPhase f (g * h) - liftPhase f g - liftPhase f h = 0
          then (1 : ℝ) else -(Fintype.card Fˣ : ℝ)⁻¹ := by
  unfold liftFin sigmaFin
  rw [show Matrix.reindex eFin eFin (liftMatrix f g) * Matrix.reindex eFin eFin (liftMatrix f h)
        = Matrix.reindex eFin eFin (liftMatrix f g * liftMatrix f h)
      from Matrix.reindexLinearEquiv_mul ℂ ℂ eFin eFin eFin (liftMatrix f g) (liftMatrix f h),
    sigmaInner_reindex, lift_pair_correlation, apply_ite Complex.re, Complex.one_re]
  congr 1
  rw [Complex.neg_re]
  congr 1
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]

/-! ## M5: `F_f` is an approximate representation (blueprint `lem:rep-iff-blr`) -/

/-- The `G × G` failure fraction: the fraction of pairs `(g,h)` at which `F_f` fails
to be multiplicative (equivalently, where the BLR test rejects). -/
noncomputable def rejGG (f : ScalarFn F Idx) : ℝ :=
  (∑ g : Twist F Idx, ∑ h : Twist F Idx,
    if liftPhase f (g * h) - liftPhase f g - liftPhase f h = 0 then (0 : ℝ) else 1)
    / (Fintype.card (Twist F Idx) : ℝ) ^ 2

/-- **`lem:rep-iff-blr` (GH-side).** The lift `F_f` is a
`((q/(q-1))·rejGG, σ)`-approximate representation of the twisted group `G`. -/
theorem liftFin_isApproxRepresentation (f : ScalarFn F Idx) :
    IsApproxRepresentation (Twist F Idx) sigmaFin (liftFin f)
      ((Fintype.card F / Fintype.card Fˣ : ℝ) * rejGG f) := by
  haveI : Nonempty F := ⟨0⟩
  haveI : Nonempty (Twist F Idx) := ⟨1⟩
  have hcardFx : (Fintype.card Fˣ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcardG : (Fintype.card (Twist F Idx) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard : (Fintype.card F : ℝ) = (Fintype.card Fˣ : ℝ) + 1 := by
    have h1 : 1 ≤ Fintype.card F := Fintype.card_pos
    rw [Fintype.card_units (α := F), Nat.cast_sub h1, Nat.cast_one]; ring
  refine ⟨liftFin_unitary f, ?_⟩
  have hpt : ∀ g h : Twist F Idx,
      (sigmaInner sigmaFin (liftFin f g * liftFin f h) (liftFin f (g * h))).re
        = 1 - (Fintype.card F / Fintype.card Fˣ : ℝ) *
            (if liftPhase f (g * h) - liftPhase f g - liftPhase f h = 0 then (0 : ℝ) else 1) := by
    intro g h
    rw [liftFin_pair_correlation, hcard]
    split_ifs <;> field_simp <;> ring
  have key : (∑ g : Twist F Idx, ∑ h : Twist F Idx,
        (sigmaInner sigmaFin (liftFin f g * liftFin f h) (liftFin f (g * h))).re)
      = (Fintype.card (Twist F Idx) : ℝ) ^ 2
        - (Fintype.card F / Fintype.card Fˣ : ℝ) *
            (∑ g : Twist F Idx, ∑ h : Twist F Idx,
              if liftPhase f (g * h) - liftPhase f g - liftPhase f h = 0 then (0 : ℝ) else 1) := by
    simp only [hpt, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.mul_sum]
    ring
  rw [key, rejGG, ge_iff_le]
  apply le_of_eq
  field_simp

/-! ## M6: Gowers–Hatami correlation witness for BLR (apply GH2) -/

/-- **Gowers–Hatami correlation for BLR** (blueprint, the GH conclusion specialized to `F_f`).
Directly from `gh2_average_correlation` applied to `liftFin_isApproxRepresentation` — no
`PosSemidef` hypothesis is needed for the correlation form. -/
theorem gh_blr_correlation (f : ScalarFn F Idx) :
    (∑ g : Twist F Idx,
      (sigmaInner sigmaFin (liftFin f g)
        (gh2Embedding (Twist F Idx) (liftFin f) *
          gh2RightRegularMatrix (G := Twist F Idx) (d := Fintype.card Fˣ) g *
          (gh2Embedding (Twist F Idx) (liftFin f))ᴴ)).re) /
      (Fintype.card (Twist F Idx) : ℝ) ≥ 1 - (Fintype.card F / Fintype.card Fˣ : ℝ) * rejGG f :=
  gh2_average_correlation (Twist F Idx) sigmaFin (liftFin f) _ (liftFin_isApproxRepresentation f)

/-! ## M7: Gowers–Hatami implies BLR soundness (`lem:gh_linearity_3`)

The full argument extracts a *dominant character* from the Gowers–Hatami
witness: it decomposes the right-regular representation `R` over the twisted
group's Pontryagin dual `{χ_{α,k}}`, identifies the Fourier weights
`|ν₀(β)|²` as a sub-probability distribution, and isolates the configuration
`β*` whose phase-collision score is `≥ 1 − ε`.  That spectral core (which needs
the character group of `G`, i.e. milestone M3) is the remaining crux.

This section formalizes the **self-contained final step**: once a candidate
linear function `ℓ_α` carries a phase-collision score `≥ 1 − ε`, its Hamming
distance to `f` is at most `(q−1)/q · ε`.  The computation is the inner
`𝔼_{b∈A}` average collapsing through `baseChar_units_sum`. -/

/-! ### Twisted-group characters (`prop:group_characaters`)

The dominant character of the extraction lives in the Pontryagin dual of
`(G, ⋆)`.  By `prop:group_characaters` these are
`χ_{α,ψ}(x,a) = ω^{Tr(a·⟪α,x⟫)}·ψ(a)`, for `α ∈ X` and `ψ` a multiplicative
character of `A = 𝔽_q^×`.  We define them directly on `Twist`; the twist makes
the homomorphism cross-terms `a·b·b⁻¹` and `a·b·a⁻¹` collapse to `a` and `b`. -/

/-- The twisted-group character `χ_{α,ψ}(x,a) = ω^{Tr(a·⟪α,x⟫)}·ψ(a)`. -/
noncomputable def gChar (α : Vec F Idx) (ψ : MulChar F ℂ) (p : Twist F Idx) : ℂ :=
  baseChar (F := F) ((p.unit : F) * dotProduct α p.vec) * ψ (p.unit : F)

@[simp] lemma gChar_one (α : Vec F Idx) (ψ : MulChar F ℂ) :
    gChar α ψ (1 : Twist F Idx) = 1 := by
  simp [gChar, dotProduct, AddChar.map_zero_eq_one]

/-- The twisted-group characters are genuine homomorphisms `(G, ⋆) → ℂˣ`. -/
lemma gChar_mul (α : Vec F Idx) (ψ : MulChar F ℂ) (p q : Twist F Idx) :
    gChar α ψ (p * q) = gChar α ψ p * gChar α ψ q := by
  have hp : (↑p.unit : F) ≠ 0 := p.unit.ne_zero
  have hq : (↑q.unit : F) ≠ 0 := q.unit.ne_zero
  have hdp : ∀ (c d : F) (u v : Vec F Idx),
      dotProduct α (c • u + d • v) = c * dotProduct α u + d * dotProduct α v := by
    intro c d u v
    simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have harg : ((p * q).unit : F) * dotProduct α (p * q).vec
      = (p.unit : F) * dotProduct α p.vec + (q.unit : F) * dotProduct α q.vec := by
    simp only [Twist.mul_unit, Twist.mul_vec, Units.val_mul]
    rw [hdp, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
    field_simp
  unfold gChar
  rw [harg, AddChar.map_add_eq_mul, Twist.mul_unit, Units.val_mul, map_mul ψ]
  ring

/-- Character sum over `X`: `∑_x ω^{Tr⟪γ,x⟫}` is `|X|` when `γ=0` and `0` otherwise.
Derived from the orthonormality of the additive characters of `X`. -/
private lemma baseChar_dotProduct_sum (γ : Vec F Idx) :
    ∑ x : Vec F Idx, baseChar (F := F) (dotProduct γ x)
      = if γ = 0 then (Fintype.card (Vec F Idx) : ℂ) else 0 := by
  have hX : (Fintype.card (Vec F Idx) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := (characters_orthonormal (F := F) (Idx := Idx)).1 γ 0
  have hexp : ⟪charFn (F := F) (Idx := Idx) γ, charFn (F := F) (Idx := Idx) 0⟫
      = (Fintype.card (Vec F Idx) : ℂ)⁻¹ * ∑ x : Vec F Idx, baseChar (F := F) (dotProduct γ x) := by
    simp only [fnInner, expectation]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    simp [charFn, dotProduct, AddChar.map_zero_eq_one]
  rw [hexp] at h
  have hS : (∑ x : Vec F Idx, baseChar (F := F) (dotProduct γ x))
      = (Fintype.card (Vec F Idx) : ℂ) * (if γ = 0 then (1 : ℂ) else 0) := by
    rw [← h, ← mul_assoc, mul_inv_cancel₀ hX, one_mul]
  rw [hS]; split_ifs <;> simp

open Classical in
/-- Orthogonality of the multiplicative characters over `A = 𝔽_q^×`:
`∑_{a∈A} ψ(a)·conj(ψ'(a))` is `|A|` when `ψ=ψ'` and `0` otherwise. -/
private lemma mulChar_units_orthogonality (ψ ψ' : MulChar F ℂ) :
    ∑ a : Fˣ, ψ (↑a : F) * star (ψ' (↑a : F))
      = if ψ = ψ' then (Fintype.card Fˣ : ℂ) else 0 := by
  have hpt : ∀ a : Fˣ, ψ (↑a : F) * star (ψ' (↑a : F)) = (ψ * ψ'⁻¹) (↑a : F) := by
    intro a
    simp only [MulChar.star_apply', MulChar.coeToFun_mul, Pi.mul_apply]
  simp_rw [hpt]
  rw [sum_units_eq_sum_sub (fun x => (ψ * ψ'⁻¹) x), MulChar.map_zero, sub_zero]
  by_cases hψ : ψ = ψ'
  · rw [if_pos hψ, show ψ * ψ'⁻¹ = 1 from by rw [hψ]; exact mul_inv_eq_one.mpr rfl,
      MulChar.sum_one_eq_card_units]
  · rw [if_neg hψ]
    exact MulChar.sum_eq_zero_of_ne_one (mul_inv_eq_one.not.mpr hψ)

open Classical in
/-- **Orthogonality of the twisted-group characters.**  Combines the `X`-character
sum with the `A`-character orthogonality; the inner `x`-sum is independent of the
unit, so the two factors separate. -/
lemma gChar_orthogonality (α α' : Vec F Idx) (ψ ψ' : MulChar F ℂ) :
    ∑ p : Twist F Idx, gChar α ψ p * star (gChar α' ψ' p)
      = if α = α' ∧ ψ = ψ' then (Fintype.card (Twist F Idx) : ℂ) else 0 := by
  have hdp_sub : ∀ v : Vec F Idx,
      dotProduct α v - dotProduct α' v = dotProduct (α - α') v := by
    intro v
    simp only [dotProduct, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp [Pi.sub_apply, sub_mul]
  have hinner : ∀ a : Fˣ,
      ∑ x : Vec F Idx, baseChar (F := F) ((a : F) * dotProduct (α - α') x)
        = if α = α' then (Fintype.card (Vec F Idx) : ℂ) else 0 := by
    intro a
    have hsmul : ∀ x : Vec F Idx,
        (a : F) * dotProduct (α - α') x = dotProduct ((a : F) • (α - α')) x := by
      intro x
      simp only [dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [hsmul]
    rw [baseChar_dotProduct_sum]
    congr 1
    rw [smul_eq_zero]
    simp [a.ne_zero, sub_eq_zero]
  have hpt : ∀ p : Twist F Idx, gChar α ψ p * star (gChar α' ψ' p)
      = baseChar (F := F) ((p.unit : F) * dotProduct (α - α') p.vec)
        * (ψ (↑p.unit) * star (ψ' (↑p.unit))) := by
    intro p
    have hcombine : baseChar (F := F) ((p.unit : F) * dotProduct α p.vec)
        * baseChar (F := F) (-((p.unit : F) * dotProduct α' p.vec))
        = baseChar (F := F) ((p.unit : F) * dotProduct (α - α') p.vec) := by
      rw [← AddChar.map_add_eq_mul, ← hdp_sub]
      congr 1
      ring
    simp only [gChar, star_mul', star_baseChar]
    rw [show baseChar (F := F) ((↑p.unit : F) * dotProduct α p.vec) * ψ (↑p.unit)
          * (baseChar (F := F) (-(↑p.unit * dotProduct α' p.vec)) * star (ψ' (↑p.unit)))
        = (baseChar (F := F) ((↑p.unit : F) * dotProduct α p.vec)
            * baseChar (F := F) (-(↑p.unit * dotProduct α' p.vec)))
          * (ψ (↑p.unit) * star (ψ' (↑p.unit))) from by ring]
    rw [hcombine]
  simp_rw [hpt]
  rw [Fintype.sum_equiv (Twist.equivProd (F := F) (Idx := Idx))
      (fun p => baseChar (F := F) ((p.unit : F) * dotProduct (α - α') p.vec)
        * (ψ (↑p.unit) * star (ψ' (↑p.unit))))
      (fun q : Vec F Idx × Fˣ => baseChar (F := F) ((q.2 : F) * dotProduct (α - α') q.1)
        * (ψ (↑q.2) * star (ψ' (↑q.2)))) (fun p => by simp [Twist.equivProd])]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hstep : ∀ a : Fˣ,
      ∑ x : Vec F Idx, baseChar (F := F) ((a : F) * dotProduct (α - α') x)
          * (ψ (↑a) * star (ψ' (↑a)))
        = (if α = α' then (Fintype.card (Vec F Idx) : ℂ) else 0) * (ψ (↑a) * star (ψ' (↑a))) := by
    intro a
    rw [← Finset.sum_mul, hinner a]
  simp_rw [hstep]
  rw [← Finset.mul_sum, mulChar_units_orthogonality, Twist.card_eq, Nat.cast_mul]
  split_ifs <;> simp_all

/-- The character index `(α, ψ) ∈ X × Â` ranges over exactly `|G|` values
(`|X|·|Â| = |X|·|A| = |G|`), matching `dim ℂ^G`. -/
lemma card_gChar_index :
    Nat.card (Vec F Idx × MulChar F ℂ) = Nat.card (Twist F Idx) := by
  rw [Nat.card_prod, MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Twist.card_eq]

open Classical in
/-- Distinct character indices give distinct characters — immediate from
orthogonality (`⟨χ,χ⟩ = |G| ≠ 0` but `⟨χ,χ'⟩ = 0` for `χ ≠ χ'`). -/
lemma gChar_injective :
    Function.Injective (fun p : Vec F Idx × MulChar F ℂ => gChar p.1 p.2) := by
  rintro ⟨α, ψ⟩ ⟨α', ψ'⟩ h
  simp only at h
  have hG : (Fintype.card (Twist F Idx) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  by_contra hne
  apply hG
  have key : ∑ p : Twist F Idx, gChar α ψ p * star (gChar α' ψ' p) = 0 := by
    rw [gChar_orthogonality, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  rw [← key, ← h, gChar_orthogonality, if_pos ⟨rfl, rfl⟩]

/-- `MulChar F ℂ` is finite (no Mathlib instance exists), via the nonempty
multiplicative equivalence to `Fˣ`. -/
noncomputable instance instFintypeMulChar : Fintype (MulChar F ℂ) := by
  have : Finite (MulChar F ℂ) := by
    obtain ⟨e⟩ := MulChar.mulEquiv_units (M := F) (R := ℂ)
    exact Finite.of_equiv _ e.toEquiv.symm
  exact Fintype.ofFinite _

open Classical in
/-- **Second orthogonality** (sum over the characters): for `g h ∈ G`,
`∑_{α,ψ} χ_{α,ψ}(g)·conj(χ_{α,ψ}(h)) = |G|·𝟙(g=h)`.  Obtained from the first
orthogonality and `|{χ_{α,ψ}}| = |G|` by the square-matrix identity
`A Aᴴ = c·1 ⟹ Aᴴ A = c·1`. -/
lemma gChar_second_orthogonality (g h : Twist F Idx) :
    ∑ idx : Vec F Idx × MulChar F ℂ, gChar idx.1 idx.2 g * star (gChar idx.1 idx.2 h)
      = if g = h then (Fintype.card (Twist F Idx) : ℂ) else 0 := by
  have hG : (Fintype.card (Twist F Idx) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard : Fintype.card (Vec F Idx × MulChar F ℂ) = Fintype.card (Twist F Idx) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_gChar_index]
  set A : Matrix (Vec F Idx × MulChar F ℂ) (Twist F Idx) ℂ :=
    (fun idx p => gChar idx.1 idx.2 p) with hA
  have hAAH : A * Aᴴ
      = (Fintype.card (Twist F Idx) : ℂ) •
        (1 : Matrix (Vec F Idx × MulChar F ℂ) (Vec F Idx × MulChar F ℂ) ℂ) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    simp only [hA, Matrix.conjTranspose_apply]
    rw [gChar_orthogonality]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg (by rintro ⟨h1, h2⟩; exact hij (Prod.ext h1 h2)), if_neg hij, mul_zero]
  have hone : A * ((Fintype.card (Twist F Idx) : ℂ)⁻¹ • Aᴴ) = 1 := by
    rw [Matrix.mul_smul, hAAH, smul_smul, inv_mul_cancel₀ hG, one_smul]
  have hAHA : Aᴴ * A
      = (Fintype.card (Twist F Idx) : ℂ) •
        (1 : Matrix (Twist F Idx) (Twist F Idx) ℂ) := by
    have hc : ((Fintype.card (Twist F Idx) : ℂ)⁻¹ • Aᴴ) * A = 1 :=
      (Matrix.mul_eq_one_comm_of_card_eq (Vec F Idx × MulChar F ℂ) (Twist F Idx) ℂ hcard).mp hone
    rw [Matrix.smul_mul] at hc
    rw [← hc, smul_smul, mul_inv_cancel₀ hG, one_smul]
  have hentry := congrFun (congrFun hAHA h) g
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hentry
  simp only [hA, Matrix.conjTranspose_apply] at hentry
  have hflip : ∑ idx : Vec F Idx × MulChar F ℂ,
        gChar idx.1 idx.2 g * star (gChar idx.1 idx.2 h)
      = ∑ idx : Vec F Idx × MulChar F ℂ,
        star (gChar idx.1 idx.2 h) * gChar idx.1 idx.2 g := by
    apply Finset.sum_congr rfl; intro idx _; ring
  rw [hflip, hentry]
  by_cases hgh : g = h
  · subst hgh; simp
  · rw [if_neg hgh, if_neg (fun he : h = g => hgh he.symm), mul_zero]

/-- The Fourier coefficient of `φ : G → ℂ` at the character `χ_{α,ψ}`:
`φ̂(α,ψ) = 𝔼_{p∈G} φ(p)·conj(χ_{α,ψ}(p))`. -/
noncomputable def gFourierCoeff (φ : Twist F Idx → ℂ)
    (idx : Vec F Idx × MulChar F ℂ) : ℂ :=
  (Fintype.card (Twist F Idx) : ℂ)⁻¹ * ∑ p : Twist F Idx, φ p * star (gChar idx.1 idx.2 p)

/-- **Fourier inversion** on `(G, ⋆)`: every `φ : G → ℂ` expands in the characters,
`φ(g) = ∑_{α,ψ} φ̂(α,ψ)·χ_{α,ψ}(g)`.  A direct consequence of the second
orthogonality relation. -/
lemma gChar_fourier_inversion (φ : Twist F Idx → ℂ) (g : Twist F Idx) :
    ∑ idx : Vec F Idx × MulChar F ℂ, gFourierCoeff φ idx * gChar idx.1 idx.2 g = φ g := by
  have hG : (Fintype.card (Twist F Idx) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have step : ∀ idx : Vec F Idx × MulChar F ℂ,
      gFourierCoeff φ idx * gChar idx.1 idx.2 g
        = ∑ p : Twist F Idx, (Fintype.card (Twist F Idx) : ℂ)⁻¹ * φ p
            * (gChar idx.1 idx.2 g * star (gChar idx.1 idx.2 p)) := by
    intro idx
    simp only [gFourierCoeff]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro p _; ring
  simp_rw [step]
  rw [Finset.sum_comm]
  have step2 : ∀ p : Twist F Idx,
      ∑ idx : Vec F Idx × MulChar F ℂ, (Fintype.card (Twist F Idx) : ℂ)⁻¹ * φ p
          * (gChar idx.1 idx.2 g * star (gChar idx.1 idx.2 p))
        = (Fintype.card (Twist F Idx) : ℂ)⁻¹ * φ p
            * (if g = p then (Fintype.card (Twist F Idx) : ℂ) else 0) := by
    intro p
    rw [← Finset.mul_sum, gChar_second_orthogonality]
  simp_rw [step2, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  rw [mul_right_comm, inv_mul_cancel₀ hG, one_mul]

/-- **Parseval** on `(G, ⋆)`: `∑_{α,ψ} φ̂(α,ψ)·conj(φ̂(α,ψ)) = 𝔼_{p∈G} φ(p)·conj(φ(p))`.
Derived from Fourier inversion. -/
lemma gChar_parseval (φ : Twist F Idx → ℂ) :
    ∑ idx : Vec F Idx × MulChar F ℂ, gFourierCoeff φ idx * star (gFourierCoeff φ idx)
      = (Fintype.card (Twist F Idx) : ℂ)⁻¹ * ∑ p : Twist F Idx, φ p * star (φ p) := by
  have hG : (Fintype.card (Twist F Idx) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard : star ((Fintype.card (Twist F Idx) : ℂ)⁻¹) = (Fintype.card (Twist F Idx) : ℂ)⁻¹ := by
    simp
  have hcoeff : ∀ idx : Vec F Idx × MulChar F ℂ,
      (Fintype.card (Twist F Idx) : ℂ) * star (gFourierCoeff φ idx)
        = ∑ p : Twist F Idx, gChar idx.1 idx.2 p * star (φ p) := by
    intro idx
    rw [gFourierCoeff, star_mul', hcard, ← mul_assoc, mul_inv_cancel₀ hG, one_mul, star_sum]
    apply Finset.sum_congr rfl; intro p _
    rw [star_mul', star_star, mul_comm]
  rw [show (∑ p : Twist F Idx, φ p * star (φ p))
        = ∑ p : Twist F Idx,
            (∑ idx : Vec F Idx × MulChar F ℂ, gFourierCoeff φ idx * gChar idx.1 idx.2 p)
              * star (φ p) from by
        apply Finset.sum_congr rfl; intro p _; rw [gChar_fourier_inversion]]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro idx _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← hcoeff, mul_left_comm,
    ← mul_assoc ((Fintype.card (Twist F Idx) : ℂ)⁻¹) (Fintype.card (Twist F Idx) : ℂ),
    inv_mul_cancel₀ hG, one_mul]

/-- The conjugate Fourier coefficient: `conj(φ̂(α,ψ)) = 𝔼_y conj(φ(y))·χ_{α,ψ}(y)`. -/
lemma gFourierCoeff_star (φ : Twist F Idx → ℂ) (idx : Vec F Idx × MulChar F ℂ) :
    star (gFourierCoeff φ idx)
      = (Fintype.card (Twist F Idx) : ℂ)⁻¹ * ∑ y : Twist F Idx, star (φ y) * gChar idx.1 idx.2 y := by
  rw [gFourierCoeff, star_mul',
    show star ((Fintype.card (Twist F Idx) : ℂ)⁻¹) = (Fintype.card (Twist F Idx) : ℂ)⁻¹ from by simp,
    star_sum]
  congr 1
  apply Finset.sum_congr rfl; intro p _
  rw [star_mul', star_star]

/-- Cross-correlation as a character sum (a step toward the spectral form of the
triple correlation): `∑_h conj(φ(h))·φ(g·h) = |G|·∑_{α,ψ} φ̂(α,ψ)·χ_{α,ψ}(g)·conj(φ̂(α,ψ))`.
Proved by Fourier-inverting `φ(g·h)` and using `χ(g·h)=χ(g)χ(h)`. -/
lemma gChar_conv (φ : Twist F Idx → ℂ) (g : Twist F Idx) :
    ∑ h : Twist F Idx, star (φ h) * φ (g * h)
      = (Fintype.card (Twist F Idx) : ℂ)
          * ∑ idx : Vec F Idx × MulChar F ℂ,
              gFourierCoeff φ idx * gChar idx.1 idx.2 g * star (gFourierCoeff φ idx) := by
  have hG : (Fintype.card (Twist F Idx) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum_h : ∀ idx : Vec F Idx × MulChar F ℂ,
      ∑ h : Twist F Idx, star (φ h) * gChar idx.1 idx.2 h
        = (Fintype.card (Twist F Idx) : ℂ) * star (gFourierCoeff φ idx) := by
    intro idx; rw [gFourierCoeff_star, ← mul_assoc, mul_inv_cancel₀ hG, one_mul]
  have hgh : ∀ h : Twist F Idx, φ (g * h)
      = ∑ idx : Vec F Idx × MulChar F ℂ,
          gFourierCoeff φ idx * (gChar idx.1 idx.2 g * gChar idx.1 idx.2 h) := by
    intro h
    rw [← gChar_fourier_inversion φ (g * h)]
    apply Finset.sum_congr rfl; intro idx _
    rw [gChar_mul]
  simp_rw [hgh, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro idx _
  rw [show (∑ h : Twist F Idx,
          star (φ h) * (gFourierCoeff φ idx * (gChar idx.1 idx.2 g * gChar idx.1 idx.2 h)))
        = gFourierCoeff φ idx * gChar idx.1 idx.2 g
            * ∑ h : Twist F Idx, star (φ h) * gChar idx.1 idx.2 h from by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro h _; ring,
      hsum_h idx]
  ring

/-- **Spectral form of the triple correlation** (the linearization the GH route
provides): `𝔼_{g,h}[conj(φ g)·conj(φ h)·φ(g·h)] = ∑_{α,ψ} φ̂(α,ψ)·conj(φ̂(α,ψ))²`.
Two applications of `gChar_conv`. -/
lemma gChar_triple_corr (φ : Twist F Idx → ℂ) :
    (Fintype.card (Twist F Idx) : ℂ)⁻¹ * (Fintype.card (Twist F Idx) : ℂ)⁻¹
        * ∑ g : Twist F Idx, ∑ h : Twist F Idx, star (φ g) * star (φ h) * φ (g * h)
      = ∑ idx : Vec F Idx × MulChar F ℂ,
          gFourierCoeff φ idx * (star (gFourierCoeff φ idx) * star (gFourierCoeff φ idx)) := by
  have hG : (Fintype.card (Twist F Idx) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum_g : ∀ idx : Vec F Idx × MulChar F ℂ,
      ∑ g : Twist F Idx, star (φ g) * gChar idx.1 idx.2 g
        = (Fintype.card (Twist F Idx) : ℂ) * star (gFourierCoeff φ idx) := fun idx => by
    rw [gFourierCoeff_star, ← mul_assoc, mul_inv_cancel₀ hG, one_mul]
  have hdouble : ∑ g : Twist F Idx, ∑ h : Twist F Idx, star (φ g) * star (φ h) * φ (g * h)
      = (Fintype.card (Twist F Idx) : ℂ) * (Fintype.card (Twist F Idx) : ℂ)
          * ∑ idx : Vec F Idx × MulChar F ℂ,
              gFourierCoeff φ idx * (star (gFourierCoeff φ idx) * star (gFourierCoeff φ idx)) := by
    have step : ∀ g : Twist F Idx,
        ∑ h : Twist F Idx, star (φ g) * star (φ h) * φ (g * h)
          = ∑ idx : Vec F Idx × MulChar F ℂ, (Fintype.card (Twist F Idx) : ℂ)
              * (star (φ g) * (gFourierCoeff φ idx * gChar idx.1 idx.2 g * star (gFourierCoeff φ idx))) := by
      intro g
      rw [show (∑ h : Twist F Idx, star (φ g) * star (φ h) * φ (g * h))
            = star (φ g) * ∑ h : Twist F Idx, star (φ h) * φ (g * h) from by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro h _; ring,
        gChar_conv, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro idx _; ring
    simp_rw [step]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro idx _
    rw [show (∑ g : Twist F Idx, (Fintype.card (Twist F Idx) : ℂ)
              * (star (φ g) * (gFourierCoeff φ idx * gChar idx.1 idx.2 g * star (gFourierCoeff φ idx))))
          = (Fintype.card (Twist F Idx) : ℂ) * (gFourierCoeff φ idx * star (gFourierCoeff φ idx))
              * ∑ g : Twist F Idx, star (φ g) * gChar idx.1 idx.2 g from by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro g _; ring,
        hsum_g]
    ring
  rw [hdouble,
    show (Fintype.card (Twist F Idx) : ℂ)⁻¹ * (Fintype.card (Twist F Idx) : ℂ)⁻¹
          * ((Fintype.card (Twist F Idx) : ℂ) * (Fintype.card (Twist F Idx) : ℂ)
              * ∑ idx : Vec F Idx × MulChar F ℂ,
                  gFourierCoeff φ idx * (star (gFourierCoeff φ idx) * star (gFourierCoeff φ idx)))
        = ((Fintype.card (Twist F Idx) : ℂ)⁻¹ * (Fintype.card (Twist F Idx) : ℂ))
            * (((Fintype.card (Twist F Idx) : ℂ)⁻¹ * (Fintype.card (Twist F Idx) : ℂ))
                * ∑ idx : Vec F Idx × MulChar F ℂ,
                    gFourierCoeff φ idx * (star (gFourierCoeff φ idx) * star (gFourierCoeff φ idx)))
        from by ring]
  simp only [inv_mul_cancel₀ hG, one_mul]

/-- **Convexity extraction** (the principle the spectral argument culminates in):
a weighted average `∑ wᵢ sᵢ ≥ c` with non-negative weights summing to `1` forces
some score `sᵢ ≥ c`. -/
lemma convex_extraction {ι : Type*} [Fintype ι] [Nonempty ι] (w s : ι → ℝ) (c : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hc : c ≤ ∑ i, w i * s i) :
    ∃ i, c ≤ s i := by
  obtain ⟨i, hi⟩ := Finite.exists_max s
  refine ⟨i, hc.trans ?_⟩
  calc ∑ j, w j * s j
      ≤ ∑ j, w j * s i :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hi j) (hw j)
    _ = (∑ j, w j) * s i := (Finset.sum_mul ..).symm
    _ = s i := by rw [hsum, one_mul]

/-- The `c`-th diagonal entry of the lift, as a function `G → ℂ`:
`φ_c(x,a) = ω^{Tr(c·a·f(x))}`. -/
noncomputable def liftDiag (f : ScalarFn F Idx) (c : Fˣ) (p : Twist F Idx) : ℂ :=
  baseChar (F := F) ((c : F) * liftPhase f p)

/-- The per-pair trace integrand, rewritten through the diagonals:
`ω^{Tr(c·defect)} = conj(φ_c g)·conj(φ_c h)·φ_c(g·h)`. -/
lemma liftDiag_triple_eq (f : ScalarFn F Idx) (c : Fˣ) (g h : Twist F Idx) :
    star (liftDiag f c g) * star (liftDiag f c h) * liftDiag f c (g * h)
      = baseChar (F := F)
          ((c : F) * (liftPhase f (g * h) - liftPhase f g - liftPhase f h)) := by
  simp only [liftDiag]
  rw [star_baseChar, star_baseChar, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The per-pair σ-trace, written as the diagonal triple-correlation integrand
summed over `c ∈ A` (combines `lift_trace_eq` with `liftDiag_triple_eq`). -/
lemma lift_trace_diag (f : ScalarFn F Idx) (g h : Twist F Idx) :
    Matrix.trace ((liftMatrix f g * liftMatrix f h)ᴴ * liftMatrix f (g * h) * sigmaBLR)
      = (Fintype.card Fˣ : ℂ)⁻¹
          * ∑ c : Fˣ, star (liftDiag f c g) * star (liftDiag f c h) * liftDiag f c (g * h) := by
  rw [lift_trace_eq]
  congr 1
  apply Finset.sum_congr rfl; intro c _
  rw [← liftDiag_triple_eq]

/-- **Spectral form of the pair correlation** (the GH linearization specialized to
`F_f`): `∑_{g,h} ⟨F_f(g)F_f(h), F_f(gh)⟩_σ = |G|²·(1/(q−1))·∑_c ∑_χ φ̂_c(χ)·conj(φ̂_c(χ))²`.
Combines `lift_trace_diag` with `gChar_triple_corr` applied per diagonal `c`. -/
lemma gh_pair_spectralC (f : ScalarFn F Idx) :
    ∑ g : Twist F Idx, ∑ h : Twist F Idx,
        Matrix.trace ((liftMatrix f g * liftMatrix f h)ᴴ * liftMatrix f (g * h) * sigmaBLR)
      = (Fintype.card (Twist F Idx) : ℂ) * (Fintype.card (Twist F Idx) : ℂ)
          * ((Fintype.card Fˣ : ℂ)⁻¹ * ∑ c : Fˣ, ∑ χ : Vec F Idx × MulChar F ℂ,
              gFourierCoeff (liftDiag f c) χ
                * (star (gFourierCoeff (liftDiag f c) χ) * star (gFourierCoeff (liftDiag f c) χ))) := by
  have hGT : (Fintype.card (Twist F Idx) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have htc : ∀ c : Fˣ,
      ∑ g : Twist F Idx, ∑ h : Twist F Idx,
          star (liftDiag f c g) * star (liftDiag f c h) * liftDiag f c (g * h)
        = (Fintype.card (Twist F Idx) : ℂ) * (Fintype.card (Twist F Idx) : ℂ)
            * ∑ χ : Vec F Idx × MulChar F ℂ, gFourierCoeff (liftDiag f c) χ
                * (star (gFourierCoeff (liftDiag f c) χ) * star (gFourierCoeff (liftDiag f c) χ)) := by
    intro c
    rw [← gChar_triple_corr (liftDiag f c),
      show (Fintype.card (Twist F Idx) : ℂ) * (Fintype.card (Twist F Idx) : ℂ)
            * ((Fintype.card (Twist F Idx) : ℂ)⁻¹ * (Fintype.card (Twist F Idx) : ℂ)⁻¹
                * ∑ g : Twist F Idx, ∑ h : Twist F Idx,
                    star (liftDiag f c g) * star (liftDiag f c h) * liftDiag f c (g * h))
          = ((Fintype.card (Twist F Idx) : ℂ) * (Fintype.card (Twist F Idx) : ℂ)⁻¹)
              * ((Fintype.card (Twist F Idx) : ℂ) * (Fintype.card (Twist F Idx) : ℂ)⁻¹)
              * ∑ g : Twist F Idx, ∑ h : Twist F Idx,
                  star (liftDiag f c g) * star (liftDiag f c h) * liftDiag f c (g * h)
          from by ring]
    simp only [mul_inv_cancel₀ hGT, one_mul]
  have hreorder : ∑ g : Twist F Idx, ∑ h : Twist F Idx, ∑ c : Fˣ,
        star (liftDiag f c g) * star (liftDiag f c h) * liftDiag f c (g * h)
      = ∑ c : Fˣ, ∑ g : Twist F Idx, ∑ h : Twist F Idx,
        star (liftDiag f c g) * star (liftDiag f c h) * liftDiag f c (g * h) := by
    rw [Finset.sum_congr rfl (fun g _ => Finset.sum_comm), Finset.sum_comm]
  simp_rw [lift_trace_diag, ← Finset.mul_sum]
  rw [hreorder]
  simp_rw [htc]
  rw [← Finset.mul_sum]
  ring

/-- `Re(z·conj(z)²) = |z|²·Re(z)`. -/
private lemma re_mul_star_sq (z : ℂ) : (z * (star z * star z)).re = Complex.normSq z * z.re := by
  have h1 : (star z).re = z.re := Complex.conj_re z
  have h2 : (star z).im = -z.im := Complex.conj_im z
  simp only [Complex.mul_re, Complex.mul_im, h1, h2, Complex.normSq_apply]
  ring

/-- **Real spectral form of the pair correlation** (`Re` of `gh_pair_spectralC`,
divided by `|G|²`): the σ-correlation is the probability-weighted average
`(1/(q−1))∑_c ∑_χ |φ̂_c(χ)|²·Re(φ̂_c(χ))`. -/
lemma gh_pair_spectral_re (f : ScalarFn F Idx) :
    (Fintype.card (Twist F Idx) : ℝ)⁻¹ * (Fintype.card (Twist F Idx) : ℝ)⁻¹
        * ∑ g : Twist F Idx, ∑ h : Twist F Idx,
            (Matrix.trace ((liftMatrix f g * liftMatrix f h)ᴴ
              * liftMatrix f (g * h) * sigmaBLR)).re
      = (Fintype.card Fˣ : ℝ)⁻¹ * ∑ c : Fˣ, ∑ χ : Vec F Idx × MulChar F ℂ,
          Complex.normSq (gFourierCoeff (liftDiag f c) χ) * (gFourierCoeff (liftDiag f c) χ).re := by
  have hGT : (Fintype.card (Twist F Idx) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hRe : (∑ g : Twist F Idx, ∑ h : Twist F Idx,
        (Matrix.trace ((liftMatrix f g * liftMatrix f h)ᴴ * liftMatrix f (g * h) * sigmaBLR)).re)
      = (∑ g : Twist F Idx, ∑ h : Twist F Idx,
          Matrix.trace ((liftMatrix f g * liftMatrix f h)ᴴ * liftMatrix f (g * h) * sigmaBLR)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro g _
    rw [Complex.re_sum]
  rw [hRe, gh_pair_spectralC,
    show (Fintype.card (Twist F Idx) : ℂ) * (Fintype.card (Twist F Idx) : ℂ)
          * ((Fintype.card Fˣ : ℂ)⁻¹ * ∑ c : Fˣ, ∑ χ : Vec F Idx × MulChar F ℂ,
              gFourierCoeff (liftDiag f c) χ
                * (star (gFourierCoeff (liftDiag f c) χ) * star (gFourierCoeff (liftDiag f c) χ)))
        = (((Fintype.card (Twist F Idx) : ℝ) * (Fintype.card (Twist F Idx) : ℝ)
              * (Fintype.card Fˣ : ℝ)⁻¹ : ℝ) : ℂ)
            * ∑ c : Fˣ, ∑ χ : Vec F Idx × MulChar F ℂ,
                gFourierCoeff (liftDiag f c) χ
                  * (star (gFourierCoeff (liftDiag f c) χ) * star (gFourierCoeff (liftDiag f c) χ))
        from by push_cast; ring]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum]
  simp_rw [Complex.re_sum, re_mul_star_sq]
  rw [show (Fintype.card (Twist F Idx) : ℝ)⁻¹ * (Fintype.card (Twist F Idx) : ℝ)⁻¹
        * ((Fintype.card (Twist F Idx) : ℝ) * (Fintype.card (Twist F Idx) : ℝ) * (Fintype.card Fˣ : ℝ)⁻¹
            * ∑ c : Fˣ, ∑ χ : Vec F Idx × MulChar F ℂ,
                Complex.normSq (gFourierCoeff (liftDiag f c) χ) * (gFourierCoeff (liftDiag f c) χ).re)
      = ((Fintype.card (Twist F Idx) : ℝ)⁻¹ * (Fintype.card (Twist F Idx) : ℝ))
          * ((Fintype.card (Twist F Idx) : ℝ)⁻¹ * (Fintype.card (Twist F Idx) : ℝ))
          * ((Fintype.card Fˣ : ℝ)⁻¹ * ∑ c : Fˣ, ∑ χ : Vec F Idx × MulChar F ℂ,
                Complex.normSq (gFourierCoeff (liftDiag f c) χ) * (gFourierCoeff (liftDiag f c) χ).re)
        from by ring]
  simp only [inv_mul_cancel₀ hGT, one_mul]

/-- **(C) Weight normalization.** Parseval for the unit-modulus diagonal `φ_c`:
`∑_χ |φ̂_c(χ)|² = 𝔼_p |φ_c(p)|² = 1`.  Hence the spectral weights
`(1/(q−1))|φ̂_c(χ)|²` form a probability distribution over `(c,χ)`. -/
lemma liftDiag_parseval (f : ScalarFn F Idx) (c : Fˣ) :
    ∑ χ : Vec F Idx × MulChar F ℂ, Complex.normSq (gFourierCoeff (liftDiag f c) χ) = 1 := by
  have hne : (Fintype.card (Twist F Idx) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hmul : ∀ z : ℂ, z * star z = (Complex.normSq z : ℂ) := fun z => Complex.mul_conj z
  have hφ : ∀ p : Twist F Idx, Complex.normSq (liftDiag f c p) = 1 := by
    intro p
    have h1 : (Complex.normSq (liftDiag f c p) : ℂ) = star (liftDiag f c p) * liftDiag f c p := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    have h2 : star (liftDiag f c p) * liftDiag f c p = 1 := by
      simp only [liftDiag, star_baseChar, ← AddChar.map_add_eq_mul, neg_add_cancel,
        AddChar.map_zero_eq_one]
    rw [h2] at h1
    exact_mod_cast h1
  have h := gChar_parseval (liftDiag f c)
  have hrhs : (Fintype.card (Twist F Idx) : ℂ)⁻¹
      * ∑ p : Twist F Idx, liftDiag f c p * star (liftDiag f c p) = 1 := by
    simp_rw [hmul, hφ, Complex.ofReal_one]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hne]
  rw [hrhs] at h
  simp_rw [hmul] at h
  rw [← Complex.ofReal_sum] at h
  exact_mod_cast h

/-- The reindexing `(x,a) ↦ (x, c·a)` of `G` (scaling the unit coordinate). -/
def unitScale (c : Fˣ) : Twist F Idx ≃ Twist F Idx where
  toFun p := ⟨p.vec, c * p.unit⟩
  invFun q := ⟨q.vec, c⁻¹ * q.unit⟩
  left_inv p := by apply Twist.ext <;> simp [inv_mul_cancel_left]
  right_inv q := by apply Twist.ext <;> simp [mul_inv_cancel_left]

@[simp] lemma unitScale_vec (c : Fˣ) (p : Twist F Idx) : (unitScale c p).vec = p.vec := rfl
@[simp] lemma unitScale_unit (c : Fˣ) (p : Twist F Idx) :
    (unitScale c p).unit = c * p.unit := rfl

/-- Dot product is homogeneous in the left argument: `⟪c•β, v⟫ = c·⟪β,v⟫`. -/
lemma dotProduct_smul_left (c : F) (β v : Vec F Idx) :
    dotProduct (c • β) v = c * dotProduct β v := by
  simp only [dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- The `c`-diagonal at the scaled point is the `1`-diagonal: `φ_c(c⁻¹·a, x) = φ_1(a,x)`. -/
lemma liftDiag_unitScale (f : ScalarFn F Idx) (c : Fˣ) (p : Twist F Idx) :
    liftDiag f c (unitScale c⁻¹ p) = liftDiag f 1 p := by
  have hc : (c : F) ≠ 0 := c.ne_zero
  simp only [liftDiag, liftPhase, unitScale_vec, unitScale_unit, Units.val_mul,
    Units.val_inv_eq_inv_val, Units.val_one, one_mul]
  congr 1
  field_simp

/-- The character at the scaled point factors out `ψ(c⁻¹)`:
`χ_{c•β,ψ}(unitScale c⁻¹ p) = ψ(c⁻¹)·χ_{β,ψ}(p)`. -/
lemma gChar_unitScale (c : Fˣ) (β : Vec F Idx) (ψ : MulChar F ℂ) (p : Twist F Idx) :
    gChar ((c : F) • β) ψ (unitScale c⁻¹ p) = ψ ((c : F)⁻¹) * gChar β ψ p := by
  have hc : (c : F) ≠ 0 := c.ne_zero
  simp only [gChar, unitScale_vec, unitScale_unit, Units.val_mul, Units.val_inv_eq_inv_val,
    dotProduct_smul_left, map_mul]
  rw [show (c : F)⁻¹ * (p.unit : F) * ((c : F) * dotProduct β p.vec)
        = (p.unit : F) * dotProduct β p.vec from by field_simp]
  ring

/-- **The Fourier factorization** (`prop:Ff_fourier`): `φ̂_c(χ_{c•β,ψ}) = ψ(c)·φ̂_1(χ_{β,ψ})`.
The `c`-dependence separates as the multiplicative character value `ψ(c)`.  Proved by
the change of variables `b = c·a` (reindexing by `unitScale c⁻¹`). -/
lemma gFourierCoeff_factor (f : ScalarFn F Idx) (c : Fˣ) (β : Vec F Idx) (ψ : MulChar F ℂ) :
    gFourierCoeff (liftDiag f c) ((c : F) • β, ψ)
      = ψ (c : F) * gFourierCoeff (liftDiag f 1) (β, ψ) := by
  have hterm : ∀ p : Twist F Idx,
      liftDiag f c (unitScale c⁻¹ p) * star (gChar ((c : F) • β) ψ (unitScale c⁻¹ p))
        = ψ (c : F) * (liftDiag f 1 p * star (gChar β ψ p)) := by
    intro p
    rw [liftDiag_unitScale, gChar_unitScale, star_mul',
      show star (ψ ((c : F)⁻¹)) = ψ (c : F) from by
        rw [MulChar.star_apply', MulChar.inv_apply', inv_inv]]
    ring
  rw [gFourierCoeff, gFourierCoeff,
    ← Equiv.sum_comp (unitScale c⁻¹)
      (fun q : Twist F Idx => liftDiag f c q * star (gChar ((c : F) • β) ψ q))]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  ring

open Classical in
/-- Multiplicative-character sum over `A = 𝔽_q^×`: `∑_{c∈A} ψ(c) = (q−1)·𝟙[ψ=ψ₀]`
(the `c`-collapse that kills the non-trivial characters). -/
lemma mulChar_units_sum (ψ : MulChar F ℂ) :
    ∑ c : Fˣ, ψ ((c : F)) = if ψ = 1 then (Fintype.card Fˣ : ℂ) else 0 := by
  rw [sum_units_eq_sum_sub (fun x => ψ x), MulChar.map_zero, sub_zero]
  by_cases hψ : ψ = 1
  · rw [if_pos hψ, hψ, MulChar.sum_one_eq_card_units]
  · rw [if_neg hψ]; exact MulChar.sum_eq_zero_of_ne_one hψ

/-- Scalar multiplication by a unit `c` is a permutation of `X` (used to reindex
`α = c·β` in the `c`-collapse). -/
def smulVecEquiv (c : Fˣ) : Vec F Idx ≃ Vec F Idx where
  toFun v := (c : F) • v
  invFun v := (c : F)⁻¹ • v
  left_inv v := by simp [smul_smul]
  right_inv v := by simp [smul_smul]

/-- A multiplicative character has unit-modulus values on units: `|ψ(c)|² = 1`. -/
lemma mulChar_normSq_unit (ψ : MulChar F ℂ) (c : Fˣ) :
    Complex.normSq (ψ (c : F)) = 1 := by
  have h1 : (Complex.normSq (ψ (c : F)) : ℂ) = ψ (c : F) * star (ψ (c : F)) := by
    rw [Complex.normSq_eq_conj_mul_self, mul_comm, starRingEnd_apply]
  have h2 : ψ (c : F) * star (ψ (c : F)) = 1 := by
    rw [MulChar.star_apply']
    have hmul : ψ (c : F) * ψ⁻¹ (c : F) = (ψ * ψ⁻¹) (c : F) := by
      rw [MulChar.coeToFun_mul, Pi.mul_apply]
    rw [hmul, mul_inv_cancel, MulChar.one_apply_coe]
  rw [h2] at h1
  exact_mod_cast h1

/-- Per-`c` reindex of the spectral inner sum: substituting `α = c·β` and applying
the factorization, the `c`-diagonal terms become `1`-diagonal terms times `ψ(c)`. -/
lemma gh_inner_reindex (f : ScalarFn F Idx) (c : Fˣ) :
    ∑ χ : Vec F Idx × MulChar F ℂ,
        Complex.normSq (gFourierCoeff (liftDiag f c) χ) * (gFourierCoeff (liftDiag f c) χ).re
      = ∑ q : Vec F Idx × MulChar F ℂ,
          Complex.normSq (gFourierCoeff (liftDiag f 1) q)
            * (q.2 (c : F) * gFourierCoeff (liftDiag f 1) q).re := by
  rw [← Equiv.sum_comp ((smulVecEquiv c).prodCongr (Equiv.refl (MulChar F ℂ)))
    (fun χ : Vec F Idx × MulChar F ℂ =>
      Complex.normSq (gFourierCoeff (liftDiag f c) χ) * (gFourierCoeff (liftDiag f c) χ).re)]
  apply Finset.sum_congr rfl; intro q _
  have hfac : gFourierCoeff (liftDiag f c)
        (((smulVecEquiv c).prodCongr (Equiv.refl (MulChar F ℂ))) q)
      = q.2 (c : F) * gFourierCoeff (liftDiag f 1) q := by
    rw [show ((smulVecEquiv c).prodCongr (Equiv.refl (MulChar F ℂ))) q = ((c : F) • q.1, q.2)
        from rfl, gFourierCoeff_factor]
  rw [hfac, Complex.normSq_mul, mulChar_normSq_unit, one_mul]

/-- The **phase-collision score** of `f` against the linear function `ℓ_α`,
`𝔼_{x∈X} 𝔼_{b∈A} ω^{Tr b(ℓ_α(x) − f(x))}` (the quantity `E*` of
`lem:gh_linearity_3`).  By character orthogonality over `A = 𝔽_q^×` the inner
average is `1` where `ℓ_α(x)=f(x)` and `−1/(q−1)` elsewhere. -/
noncomputable def phaseCollisionScore (f : ScalarFn F Idx) (α : Vec F Idx) : ℂ :=
  (Fintype.card (Vec F Idx) : ℂ)⁻¹ * (Fintype.card Fˣ : ℂ)⁻¹ *
    ∑ x : Vec F Idx, ∑ b : Fˣ, baseChar (F := F) ((b : F) * (linearFn α x - f x))

/-- The phase-collision score equals `1 − (q/(q−1))·δ(f, ℓ_α)` — the closed form
at the end of `lem:gh_linearity_3`.  It is real-valued (an `ℝ` cast). -/
lemma phaseCollisionScore_eq_distance (f : ScalarFn F Idx) (α : Vec F Idx) :
    phaseCollisionScore f α
      = (((1 : ℝ) - (Fintype.card F : ℝ) / (Fintype.card Fˣ : ℝ)
            * distance f (linearFn α) : ℝ) : ℂ) := by
  classical
  have hX : (Fintype.card (Vec F Idx) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hU : (Fintype.card Fˣ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcardF : (Fintype.card F : ℂ) = (Fintype.card Fˣ : ℂ) + 1 := by
    rw [Fintype.card_units (α := F), Nat.cast_sub Fintype.card_pos, Nat.cast_one]; ring
  have hinner : ∀ x : Vec F Idx,
      (∑ b : Fˣ, baseChar (F := F) ((b : F) * (linearFn α x - f x)))
        = (Fintype.card Fˣ : ℂ)
          - (Fintype.card F : ℂ) * (if f x ≠ linearFn α x then (1 : ℂ) else 0) := by
    intro x
    rw [baseChar_units_sum]
    by_cases hx : f x = linearFn α x
    · rw [if_pos (sub_eq_zero.mpr hx.symm), if_neg (not_not.mpr hx), mul_zero, sub_zero]
    · rw [if_neg (fun he => hx (sub_eq_zero.mp he).symm), if_pos hx, hcardF]; ring
  have hdist : (distance f (linearFn α) : ℂ)
      = (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          ∑ x : Vec F Idx, (if f x ≠ linearFn α x then (1 : ℂ) else 0) := by
    rw [distance, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  rw [phaseCollisionScore]
  simp only [hinner, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum]
  push_cast
  rw [hdist]
  field_simp

/-- **Final step of `lem:gh_linearity_3`.**  If the dominant linear function
`ℓ_α` achieves phase-collision score `≥ 1 − ε`, then its Hamming distance to
`f` is at most `(q−1)/q · ε`. -/
lemma distance_le_of_phaseCollisionScore_re (f : ScalarFn F Idx) (α : Vec F Idx) (ε : ℝ)
    (h : 1 - ε ≤ (phaseCollisionScore f α).re) :
    distance f (linearFn α) ≤ (Fintype.card Fˣ : ℝ) / (Fintype.card F : ℝ) * ε := by
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hUr : (0 : ℝ) < (Fintype.card Fˣ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hre : (phaseCollisionScore f α).re
      = 1 - (Fintype.card F : ℝ) / (Fintype.card Fˣ : ℝ) * distance f (linearFn α) := by
    rw [phaseCollisionScore_eq_distance, Complex.ofReal_re]
  rw [hre] at h
  have h2 : (Fintype.card F : ℝ) / (Fintype.card Fˣ : ℝ) * distance f (linearFn α) ≤ ε := by
    linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hUr] at h2
  rw [div_mul_eq_mul_div, le_div_iff₀ hF]
  nlinarith [h2]

/-- **Bridge to the combinatorial side.**  The trivial-character Fourier
coefficient of the `1`-diagonal is exactly the phase-collision score:
`φ̂_1(β, ψ₀) = E*(f, ℓ_β)`.  (The sign flip `f − ℓ ↦ ℓ − f` is absorbed by the
negation bijection `b ↦ −b` on `A = 𝔽_q^×`.) -/
lemma gFourierCoeff_one_eq_phaseCollisionScore (f : ScalarFn F Idx) (β : Vec F Idx) :
    gFourierCoeff (liftDiag f 1) (β, 1) = phaseCollisionScore f β := by
  classical
  have hpt : ∀ p : Twist F Idx, liftDiag f 1 p * star (gChar β 1 p)
      = baseChar (F := F) ((p.unit : F) * (f p.vec - dotProduct β p.vec)) := by
    intro p
    simp only [liftDiag, liftPhase, gChar, Units.val_one, one_mul, MulChar.one_apply_coe,
      mul_one, star_baseChar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hneg : ∀ x : Vec F Idx,
      ∑ b : Fˣ, baseChar (F := F) ((b : F) * (f x - dotProduct β x))
        = ∑ b : Fˣ, baseChar (F := F) ((b : F) * (linearFn β x - f x)) := by
    intro x
    apply Fintype.sum_equiv (Equiv.neg Fˣ)
    intro b
    simp only [Equiv.neg_apply, Units.val_neg, linearFn]
    congr 1
    ring
  rw [gFourierCoeff]
  simp only [hpt]
  rw [Fintype.sum_equiv (Twist.equivProd (F := F) (Idx := Idx))
      (fun p => baseChar (F := F) ((p.unit : F) * (f p.vec - dotProduct β p.vec)))
      (fun q : Vec F Idx × Fˣ => baseChar (F := F) ((q.2 : F) * (f q.1 - dotProduct β q.1)))
      (fun p => by simp [Twist.equivProd])]
  rw [Fintype.sum_prod_type]
  simp only [hneg]
  rw [phaseCollisionScore, Twist.card_eq, Nat.cast_mul, mul_inv]

/-- **The `c`-collapse (heart of `lem:gh_linearity_3`).**  Averaging the spectral
weights over the scaling factor `c ∈ A` kills every nontrivial multiplicative
character `ψ ≠ ψ₀` (orthogonality `∑_c ψ(c) = 0`), collapsing the double sum over
`(c, χ)` to a single sum over the trivial-character coefficients `φ̂_1(β, ψ₀)`. -/
lemma gh_collapse (f : ScalarFn F Idx) :
    (Fintype.card Fˣ : ℝ)⁻¹ * ∑ c : Fˣ, ∑ χ : Vec F Idx × MulChar F ℂ,
        Complex.normSq (gFourierCoeff (liftDiag f c) χ) * (gFourierCoeff (liftDiag f c) χ).re
      = ∑ β : Vec F Idx,
          Complex.normSq (gFourierCoeff (liftDiag f 1) (β, 1))
            * (gFourierCoeff (liftDiag f 1) (β, 1)).re := by
  classical
  have hU : (Fintype.card Fˣ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp_rw [gh_inner_reindex]
  rw [Finset.sum_comm]
  have hc : ∀ q : Vec F Idx × MulChar F ℂ,
      ∑ c : Fˣ, Complex.normSq (gFourierCoeff (liftDiag f 1) q)
            * (q.2 (c : F) * gFourierCoeff (liftDiag f 1) q).re
        = Complex.normSq (gFourierCoeff (liftDiag f 1) q)
            * ((if q.2 = 1 then (Fintype.card Fˣ : ℂ) else 0)
                * gFourierCoeff (liftDiag f 1) q).re := by
    intro q
    rw [← Finset.mul_sum, ← Complex.re_sum, ← Finset.sum_mul, mulChar_units_sum]
  simp_rw [hc]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  rw [Finset.sum_eq_single (1 : MulChar F ℂ)
      (fun ψ _ hψ => by rw [if_neg hψ, zero_mul, Complex.zero_re, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h)]
  rw [if_pos rfl, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
  field_simp

/-- **Third-moment max extraction.**  If real scores `rᵢ` have `∑ rᵢ² ≤ 1` and the
weighted third moment `∑ rᵢ²·rᵢ ≥ 1 − ε`, then some score satisfies `rᵢ ≥ 1 − ε`.
The nonnegativity `0 ≤ ∑ rᵢ²·rᵢ` (correlation positivity) is what guarantees the
maximiser is `≥ 0`; it carries no condition on `ε`.  This replaces the convex-combination
extraction in the unnormalized (`∑ wᵢ ≤ 1`) setting produced by the `c`-collapse,
using `rᵢ²·rᵢ ≤ rᵢ²·max r`. -/
lemma cube_max_extraction {ι : Type*} [Fintype ι] [Nonempty ι] (r : ι → ℝ)
    (ε : ℝ) (hsq : ∑ i, (r i) ^ 2 ≤ 1) (hcorr0 : 0 ≤ ∑ i, (r i) ^ 2 * r i)
    (hcorr : 1 - ε ≤ ∑ i, (r i) ^ 2 * r i) :
    ∃ i, 1 - ε ≤ r i := by
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max r
  refine ⟨i₀, ?_⟩
  have hT0 : (0 : ℝ) ≤ ∑ i, (r i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hub : ∑ i, (r i) ^ 2 * r i ≤ r i₀ * ∑ i, (r i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [mul_comm (r i₀) ((r i) ^ 2)]
    exact mul_le_mul_of_nonneg_left (hi₀ i) (sq_nonneg _)
  have hMsq : (r i₀) ^ 2 ≤ ∑ i, (r i) ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ i₀)
  have hM0 : 0 ≤ r i₀ := by
    by_contra hlt
    push_neg at hlt
    have hle0 : r i₀ * ∑ i, (r i) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hlt.le hT0
    have hMT0 : r i₀ * ∑ i, (r i) ^ 2 = 0 :=
      le_antisymm hle0 (by linarith [hcorr0, hub])
    have hTeq : ∑ i, (r i) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hMT0 with h | h
      · exact absurd h (ne_of_lt hlt)
      · exact h
    have hsq0 : (r i₀) ^ 2 ≤ 0 := le_trans hMsq (le_of_eq hTeq)
    nlinarith [hsq0, hlt]
  have hfin : r i₀ * ∑ i, (r i) ^ 2 ≤ r i₀ := mul_le_of_le_one_right hM0 hsq
  linarith [hcorr, hub, hfin]

/-- **`lem:gh_linearity_3` (soundness).**  If the Gowers–Hatami operator
pair-correlation `𝔼_{g,h} Re tr((F_g F_h)ᴴ F_{gh} σ)` is nonnegative and at least
`1 − ε`, then `f` is `(q−1)/q · ε`-close to a linear function `ℓ_α`.  No condition on
`ε` is imposed here: the regime `ε ≤ 1` is only what makes the correlation
nonnegative, and that is assumed structurally via `hCorrpos` (supplied at the
soundness theorem from the BLR rejection bound).

The proof: spectral form (`gh_pair_spectral_re`) ⟶ `c`-collapse onto the trivial
character (`gh_collapse`) ⟶ identify the surviving coefficients with phase-collision
scores (`gFourierCoeff_one_eq_phaseCollisionScore`) ⟶ third-moment max extraction
(`cube_max_extraction`) ⟶ distance bound (`distance_le_of_phaseCollisionScore_re`). -/
theorem gh_linearity_3 (f : ScalarFn F Idx) (ε : ℝ)
    (hCorrpos : 0 ≤ (Fintype.card (Twist F Idx) : ℝ)⁻¹ * (Fintype.card (Twist F Idx) : ℝ)⁻¹
        * ∑ g : Twist F Idx, ∑ h : Twist F Idx,
            (Matrix.trace ((liftMatrix f g * liftMatrix f h)ᴴ
              * liftMatrix f (g * h) * sigmaBLR)).re)
    (hCorr : 1 - ε ≤ (Fintype.card (Twist F Idx) : ℝ)⁻¹ * (Fintype.card (Twist F Idx) : ℝ)⁻¹
        * ∑ g : Twist F Idx, ∑ h : Twist F Idx,
            (Matrix.trace ((liftMatrix f g * liftMatrix f h)ᴴ
              * liftMatrix f (g * h) * sigmaBLR)).re) :
    ∃ α : Vec F Idx, distance f (linearFn α) ≤ (Fintype.card Fˣ : ℝ) / (Fintype.card F : ℝ) * ε := by
  classical
  rw [gh_pair_spectral_re, gh_collapse] at hCorr hCorrpos
  simp_rw [gFourierCoeff_one_eq_phaseCollisionScore] at hCorr hCorrpos
  have hreal : ∀ β : Vec F Idx,
      Complex.normSq (phaseCollisionScore f β) * (phaseCollisionScore f β).re
        = ((phaseCollisionScore f β).re) ^ 2 * (phaseCollisionScore f β).re := by
    intro β
    rw [phaseCollisionScore_eq_distance, Complex.normSq_ofReal, Complex.ofReal_re]
    ring
  simp_rw [hreal] at hCorr hCorrpos
  have hsq : ∑ β : Vec F Idx, ((phaseCollisionScore f β).re) ^ 2 ≤ 1 := by
    have hpar := liftDiag_parseval f 1
    rw [← hpar]
    have hconv : ∀ β : Vec F Idx, ((phaseCollisionScore f β).re) ^ 2
        = Complex.normSq (gFourierCoeff (liftDiag f 1) (β, 1)) := by
      intro β
      rw [gFourierCoeff_one_eq_phaseCollisionScore, phaseCollisionScore_eq_distance,
        Complex.ofReal_re, Complex.normSq_ofReal]
      ring
    simp_rw [hconv]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro β _
    exact Finset.single_le_sum
      (f := fun ψ : MulChar F ℂ => Complex.normSq (gFourierCoeff (liftDiag f 1) (β, ψ)))
      (fun ψ _ => Complex.normSq_nonneg _) (Finset.mem_univ (1 : MulChar F ℂ))
  obtain ⟨α, hα⟩ :=
    cube_max_extraction (fun β => (phaseCollisionScore f β).re) ε hsq hCorrpos hCorr
  exact ⟨α, distance_le_of_phaseCollisionScore_re f α ε hα⟩

/-! ## M8: Gowers–Hatami soundness of the BLR test (`thm:main`) -/

/-- **The operator pair-correlation equals `1 − (q/(q−1))·rejGG`.**  Each per-pair
trace is `1` on accepting pairs and `−1/(q−1)` on rejecting ones
(`lift_pair_correlation`), so the average is `1 − (q/(q−1))·rejGG f`.  Unconditional. -/
lemma gh_pair_correlation_eq (f : ScalarFn F Idx) :
    (Fintype.card (Twist F Idx) : ℝ)⁻¹ * (Fintype.card (Twist F Idx) : ℝ)⁻¹
        * ∑ g : Twist F Idx, ∑ h : Twist F Idx,
            (Matrix.trace ((liftMatrix f g * liftMatrix f h)ᴴ
              * liftMatrix f (g * h) * sigmaBLR)).re
      = 1 - (Fintype.card F / Fintype.card Fˣ : ℝ) * rejGG f := by
  have hcardFx : (Fintype.card Fˣ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcardG : (Fintype.card (Twist F Idx) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard : (Fintype.card F : ℝ) = (Fintype.card Fˣ : ℝ) + 1 := by
    have h1 : 1 ≤ Fintype.card F := Fintype.card_pos
    rw [Fintype.card_units (α := F), Nat.cast_sub h1, Nat.cast_one]; ring
  have hpt : ∀ g h : Twist F Idx,
      (Matrix.trace ((liftMatrix f g * liftMatrix f h)ᴴ
          * liftMatrix f (g * h) * sigmaBLR)).re
        = 1 - (Fintype.card F / Fintype.card Fˣ : ℝ) *
            (if liftPhase f (g * h) - liftPhase f g - liftPhase f h = 0 then (0 : ℝ) else 1) := by
    intro g h
    rw [lift_pair_correlation, apply_ite Complex.re, Complex.one_re]
    have hneg : (-(Fintype.card Fˣ : ℂ)⁻¹).re = -(Fintype.card Fˣ : ℝ)⁻¹ := by
      rw [Complex.neg_re]; congr 1
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
    rw [hneg, hcard]
    split_ifs <;> field_simp <;> ring
  have key : (∑ g : Twist F Idx, ∑ h : Twist F Idx,
        (Matrix.trace ((liftMatrix f g * liftMatrix f h)ᴴ
          * liftMatrix f (g * h) * sigmaBLR)).re)
      = (Fintype.card (Twist F Idx) : ℝ) ^ 2
        - (Fintype.card F / Fintype.card Fˣ : ℝ) *
            (∑ g : Twist F Idx, ∑ h : Twist F Idx,
              if liftPhase f (g * h) - liftPhase f g - liftPhase f h = 0 then (0 : ℝ) else 1) := by
    simp only [hpt, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.mul_sum]
    ring
  rw [key, rejGG]
  field_simp

/-- **`thm:main` (soundness of the BLR test, Gowers–Hatami route).**  In the regime
`rejGG f ≤ (q−1)/q` (equivalently `ε := (q/(q−1))·rejGG ≤ 1`), the distance from `f`
to the nearest linear function is at most the `G×G` rejection fraction `rejGG f`.

This is the *only* statement carrying the regime hypothesis; every intermediate lemma
is unconditional.  The loose factor `q/(q−1)` of the approximate representation cancels
the tight factor `(q−1)/q` of `gh_linearity_3`, leaving the clean bound `δ ≤ rejGG`. -/
theorem gh_blr_soundness (f : ScalarFn F Idx)
    (hrej : rejGG f ≤ (Fintype.card Fˣ : ℝ) / (Fintype.card F : ℝ)) :
    distanceToLinear f ≤ rejGG f := by
  have hcardFx : (0 : ℝ) < (Fintype.card Fˣ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcardF : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hFxne : (Fintype.card Fˣ : ℝ) ≠ 0 := hcardFx.ne'
  have hFne : (Fintype.card F : ℝ) ≠ 0 := hcardF.ne'
  have hcorr_eq := gh_pair_correlation_eq f
  -- regime: `ε := (q/(q−1))·rejGG ≤ 1`, hence the correlation `1 − ε` is nonnegative
  have hεle : (Fintype.card F / Fintype.card Fˣ : ℝ) * rejGG f ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hcardFx, mul_comm, ← le_div_iff₀ hcardF]
    exact hrej
  have hCorrpos : 0 ≤ (Fintype.card (Twist F Idx) : ℝ)⁻¹ * (Fintype.card (Twist F Idx) : ℝ)⁻¹
      * ∑ g : Twist F Idx, ∑ h : Twist F Idx,
          (Matrix.trace ((liftMatrix f g * liftMatrix f h)ᴴ
            * liftMatrix f (g * h) * sigmaBLR)).re := by
    rw [hcorr_eq]; linarith
  have hCorr := hcorr_eq.ge
  obtain ⟨α, hα⟩ :=
    gh_linearity_3 f ((Fintype.card F / Fintype.card Fˣ : ℝ) * rejGG f) hCorrpos hCorr
  -- the `q/(q−1)` and `(q−1)/q` factors cancel: `(q−1)/q · ε = rejGG`
  have hcancel : (Fintype.card Fˣ : ℝ) / (Fintype.card F : ℝ)
      * ((Fintype.card F / Fintype.card Fˣ : ℝ) * rejGG f) = rejGG f := by
    field_simp
  rw [hcancel] at hα
  calc distanceToLinear f ≤ distance f (linearFn α) := by
        rw [distanceToLinear_eq_inf_linearFn]
        exact Finset.inf'_le _ (Finset.mem_univ α)
    _ ≤ rejGG f := hα

end BlrPcp
