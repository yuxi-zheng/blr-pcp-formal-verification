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

@[blueprint "def:ff-linear"
  (statement := /-- A function $f : F^n \to F$ is linear if there exists
  $a \in F^n$ such that
  \[
    f(x) = \sum_i a_i x_i
  \]
  for every $x \in F^n$. -/)]
def IsLinear (f : ScalarFn F Idx) : Prop :=
  ∃ a : Vec F Idx, ∀ x, f x = ∑ i, a i * x i

def LinearSet : Set (ScalarFn F Idx) := {f | IsLinear f}

@[blueprint "def:ff-blr-test"
  (statement := /-- The finite-field BLR test samples $x,y \in F^n$ and
  $a,b \in F \setminus \{0\}$, and accepts iff
  \[
    a f(x) + b f(y) = f(ax + by).
  \] -/)]
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
@[blueprint "def:ff-additive-characters"
  (statement := /-- Write $F=\mathbb{F}_q$ where $q = p^m$ for a prime number $p$ and a positive integer $m$. For each $\alpha \in \mathbb{F}_q^n$, define
  the additive character $\chi_\alpha : \mathbb{F}_q \rightarrow \mathbb{C}$ as
  \[
    \chi_\alpha(x) := \omega_p^{\mathrm{Tr}(\langle \alpha, x\rangle)},
  \]
  where $ \omega_p = \exp(2π i/p)$ and  $\mathrm{Tr} : \mathbb{F}_q \to \mathbb{F}_p $ is the field trace $\mathrm{Tr}(a) = \sum_{j=0}^{m-1} a^{p^j}$. -/)]
noncomputable def charFn (α : Vec F Idx) : ComplexFn F Idx := by
  classical
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  letI : NeZero (ringChar F) := ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
  exact fun x =>
    ZMod.stdAddChar (N := ringChar F) (Algebra.trace (ZMod (ringChar F)) F ⟪α, x⟫ᵥ)

def HasAdditiveCharacters : Prop := True

axiom fourierCoeff : ComplexFn F Idx → Vec F Idx → Complex

@[blueprint "lem:ff-characters-orthonormal"
  (statement := /-- The family $\{\chi_\alpha\}_{\alpha \in \mathbb{F}_q^n}$ is an
  orthonormal basis for the complex-valued functions
  $g : \mathbb{F}_q^n \to \mathbb{C}$ with respect to the inner product
  \[
    \langle g,h\rangle := \mathbb{E}_{x \in \mathbb{F}_q^n}[g(x)\overline{h(x)}].
  \] -/)]
lemma characters_orthonormal_basis : HasAdditiveCharacters := by
  sorry

@[blueprint "lem:ff-fourier-expansion"
  (statement := /-- Every function $g : \mathbb{F}_q^n \to \mathbb{C}$ has a unique
  Fourier expansion
  \[
    g(x) = \sum_{\alpha \in \mathbb{F}_q^n} \widehat g(\alpha)\chi_\alpha(x).
  \] -/)]
lemma fourier_expansion (g : ComplexFn F Idx) : True := by
  sorry

@[blueprint "lem:ff-parseval-plancherel"
  (statement := /-- Parseval and Plancherel hold:
  \[
    \langle g,g\rangle = \sum_\alpha |\widehat g(\alpha)|^2,
    \qquad
    \langle g,h\rangle = \sum_\alpha \widehat g(\alpha)\overline{\widehat h(\alpha)}.
  \] -/)]
lemma parseval_plancherel (g h : ComplexFn F Idx) : True := by
  sorry

@[blueprint "def:ff-fourier-set"
  (statement := /-- For $f : \mathbb{F}_q^n \to \mathbb{F}_q$, define its Fourier set
  \[
    \Phi(f) := \{\varphi_c\}_{c \in \mathbb{F}_q^\times},
    \qquad
    \varphi_c(x) := \omega_p^{\mathrm{Tr}(c f(x))}.
  \] -/)]
def HasFourierSet (f : ScalarFn F Idx) : Prop := True

@[blueprint "lem:ff-distance-formula"
  (statement := /-- If $f,g : \mathbb{F}_q^n \to \mathbb{F}_q$ have Fourier sets
  $\{\varphi_c\}_{c \in \mathbb{F}_q^\times}$ and
  $\{\psi_c\}_{c \in \mathbb{F}_q^\times}$, then
  \[
    \Delta(f,g)
    = 1 - \frac{1}{q}\left(1 + \sum_{c \in \mathbb{F}_q^\times}
      \langle \varphi_c,\psi_c\rangle\right).
  \] -/)]
lemma distance_formula_via_fourier_sets (f g : ScalarFn F Idx) : True := by
  sorry

@[blueprint "lem:ff-distance-to-linearity"
  (statement := /-- If $f$ has Fourier set $\{\varphi_c\}_{c \in \mathbb{F}_q^\times}$,
  then its distance to the linear functions is
  \[
    \Delta(f,\mathrm{LIN})
    = 1 - \frac{1}{q}\left(1 + \max_{\alpha \in \mathbb{F}_q^n}
      \sum_{c \in \mathbb{F}_q^\times} \widehat{\varphi_c}(c\alpha)\right).
  \] -/)]
lemma distance_to_linearity_formula (f : ScalarFn F Idx) : True := by
  sorry

@[blueprint "lem:ff-spectral-bound"
  (statement := /-- A Fourier-analytic calculation shows that the rejection probability
  of the finite-field BLR test dominates the Fourier-set expression for
  $\Delta(f,\mathrm{LIN})$. -/)]
lemma spectral_lower_bound (f : ScalarFn F Idx) :
    distanceToLinear f ≤ rejectionProbabilityBLR f := by
  sorry

@[blueprint "thm:ff-blr-improved-analysis"
  (statement := /-- For every function $f : F^n \to F$, the finite-field BLR test
  satisfies
  \[
    \Pr[V_{BLR}^f = 0] \ge \Delta(f,\mathrm{LIN}).
  \]
  This is the improved finite-field analysis proved via Fourier analysis. -/)]
lemma improved_analysis_finite_fields (f : ScalarFn F Idx) :
    distanceToLinear f ≤ rejectionProbabilityBLR f := by
  exact spectral_lower_bound f

@[blueprint "cor:ff-high-acceptance-close-to-linear"
  (statement := /-- If the finite-field BLR test accepts $f$ with probability at least
  $1 - \varepsilon$, then
  \[
    \Delta(f,\mathrm{LIN}) \le \varepsilon.
  \] -/)]
lemma almost_linear_of_high_acceptance (f : ScalarFn F Idx) {ε : Real}
    (h : 1 - ε ≤ acceptanceProbabilityBLR f) :
    distanceToLinear f ≤ ε := by
  have hmain : distanceToLinear f ≤ rejectionProbabilityBLR f :=
    improved_analysis_finite_fields f
  dsimp [rejectionProbabilityBLR] at hmain
  linarith

@[blueprint "rem:q2-special-case"
  (statement := /-- When $q = 2$, this reduces to the Boolean Fourier-analytic proof
  of the BLR theorem. -/)]
lemma boolean_special_case : True := by
  sorry

end BlrPcp
