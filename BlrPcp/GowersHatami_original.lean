import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Group.Basic
import Mathlib.GroupTheory.GroupAction.Basic

import Architect
/-!
# Gowers–Hatami Stability Theorem

This file formalises the definitions and statements from the chapter on
approximate representations and the Gowers–Hatami theorem.

## Sections

* `SigmaInnerProduct`  — the σ-weighted inner product on matrices
* `RepresentationTheory` — standard representation-theoretic notions
* `GowersHatami`        — the main stability theorem
-/

open scoped Matrix ComplexConjugate ComplexOrder
open BigOperators Finset

variable {d dρ : ℕ} (G : Type*) [Group G] [Fintype G]

/-! ## Section 1: Preliminaries -/

section SigmaInnerProduct

/-!
### σ inner product

\[
  \langle A, B \rangle_{\sigma} = \operatorname{Tr}(A^* B \sigma)
\]
where $\sigma \geq 0$ is a positive semidefinite matrix of trace 1.

Note: `Matrix.PosSemidef` requires `[PartialOrder R]` on the scalar field.
For `ℂ`, this is provided by opening the `ComplexOrder` locale (from
`Mathlib.Analysis.Complex.Basic`), which gives `ℂ` the partial order
$z \leq w \iff z.\mathrm{re} \leq w.\mathrm{re} \wedge z.\mathrm{im} = w.\mathrm{im}$.
-/

noncomputable def sigmaInner {n : ℕ} (σ A B : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  Matrix.trace (Aᴴ * B * σ)

noncomputable def sigmaNormSq {n : ℕ} (σ A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (sigmaInner σ A A).re

/-!
### Identity for unitary matrices

For unitary matrices $A, B$ and a state $\sigma$,
\[
  \|A - B\|_\sigma^2 = 2 - 2\,\Re\langle A, B\rangle_\sigma.
\]
-/

theorem sigmaNormSq_sub_unitary
    (σ A B : Matrix (Fin d) (Fin d) ℂ)
    (hσ : Matrix.PosSemidef σ) (hσtr : Matrix.trace σ = 1)
    (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    sigmaNormSq σ (A - B) = 2 - 2 * (sigmaInner σ A B).re := by
  have hA' : Aᴴ * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hA
  have hB' : Bᴴ * B = 1 := Matrix.mem_unitaryGroup_iff'.mp hB
  have hσH : σᴴ = σ := hσ.1
  have hcross :
      (Matrix.trace (Bᴴ * A * σ)).re = (Matrix.trace (Aᴴ * B * σ)).re := by
    have htrace :
        Matrix.trace (Bᴴ * A * σ) = star (Matrix.trace (Aᴴ * B * σ)) := by
      calc
        Matrix.trace (Bᴴ * A * σ)
            = Matrix.trace (σ * (Bᴴ * A)) := by
                rw [Matrix.trace_mul_cycle]
                simp [Matrix.mul_assoc]
        _ = Matrix.trace ((Aᴴ * B * σ)ᴴ) := by
                congr 1
                simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, hσH]
        _ = star (Matrix.trace (Aᴴ * B * σ)) := Matrix.trace_conjTranspose _
    calc
      (Matrix.trace (Bᴴ * A * σ)).re
          = (star (Matrix.trace (Aᴴ * B * σ))).re := by rw [htrace]
      _ = (Matrix.trace (Aᴴ * B * σ)).re := by
              simp
  unfold sigmaNormSq sigmaInner
  simp only [Matrix.conjTranspose_sub]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [hA', hB']
  simp only [Matrix.sub_mul, Matrix.trace_sub, hσtr, one_mul]
  simp only [Complex.sub_re, Complex.one_re]
  rw [hcross]
  ring

/-!
### ε-proximity in σ-norm vs. inner product

\[
  \mathbb{E}_{x \in G} \|f(x) - f_2(x)\|^2_\sigma \le 2\varepsilon
  \iff
  \mathbb{E}_{x \in G} \Re\langle f(x), f_2(x)\rangle_\sigma \ge 1 - \varepsilon.
\]
-/

theorem sigma_proximity_iff
    (σ : Matrix (Fin d) (Fin d) ℂ)
    (f f₂ : G → Matrix (Fin d) (Fin d) ℂ)
    (ε : ℝ) :
    (∑ x : G, sigmaNormSq σ (f x - f₂ x)) / Fintype.card G ≤ 2 * ε
    ↔
    (∑ x : G, (sigmaInner σ (f x) (f₂ x)).re) / Fintype.card G ≥ 1 - ε := by
  sorry

end SigmaInnerProduct

/-! ## Section 2: Approximate Representations -/

section ApproxRepresentation

/-!
### (ε, σ)-representation

Given a finite group $G$, an integer $d \ge 1$, $\varepsilon \ge 0$, and a
$d$-dimensional density matrix $\sigma$, an $(\varepsilon, \sigma)$-representation
of $G$ is a map $f : G \to U_d(\mathbb{C})$ such that
\[
  \mathbb{E}_{x,y \in G}
  \Re\!\left(\langle f(x)^* f(y),\, f(x^{-1}y)\rangle_\sigma\right) \ge 1 - \varepsilon.
\]
-/

def IsApproxRepresentation
    (σ : Matrix (Fin d) (Fin d) ℂ)
    (f : G → Matrix (Fin d) (Fin d) ℂ)
    (ε : ℝ) : Prop :=
  (∑ x : G, ∑ y : G,
    (sigmaInner σ (f x * f y) (f (x * y))).re) /
    (Fintype.card G ^ 2 : ℝ) ≥ 1 - ε

end ApproxRepresentation

/-! ## Section 3: Representation Theory -/

section RepresentationTheory

/-!
### Representation

A *representation* of a group $G$ on a finite-dimensional $\mathbb{C}$-vector
space $V$ is a group homomorphism $\rho : G \to \mathrm{GL}(V)$, i.e.
\[
  \rho(xy) = \rho(x)\rho(y) \quad \text{for all } x, y \in G.
\]
-/

-- In Mathlib, `Representation k G V` (or `MonoidHom G (GL V k)`) covers this.
-- We record the type alias here for blueprint visibility.

abbrev UnitaryRep (G : Type*) [Group G] (d : ℕ) :=
  G →* Matrix.unitaryGroup (Fin d) ℂ

/-!
### Irreducible representation

A representation $\rho : G \to \mathrm{GL}(V)$ is *irreducible* if the only
$G$-invariant subspaces of $V$ are $\{0\}$ and $V$ itself.
-/

-- Irreducibility is available in Mathlib as `Irreducible` for `Representation`.
-- The blueprint node below records the notion we rely on.

/-!
### Character

The *character* of a representation $\rho$ is
\[
  \chi_\rho(x) = \operatorname{Tr}[\rho(x)].
\]
-/

noncomputable def UnitaryRep.character {d : ℕ} (ρ : UnitaryRep G d) : G → ℂ :=
  fun x => Matrix.trace (ρ x : Matrix (Fin d) (Fin d) ℂ)


/-!
### Maschke theorem

Finite dimensional representations of finite groups are completely reducible:
every representation can be decomposed into a direct sum of irreducible representations.
\[
  \rho \cong \bigoplus_{m} r_m \cdot \rho_m,
\]
where $\rho_m$ are the irreducible representations of $G$ and $r_m$ are their multiplicities.
-/
theorem Maschke (ρ : UnitaryRep G d) :
    ∃ (σ : UnitaryRep G d), True := by
  sorry

/-!
### Regular representation

The regular representation $R : G \to \mathbb{C}[G]$ acts by left multiplication:
\[
  R(x)\,|g\rangle = |xg\rangle.
\]
-/
noncomputable def regularRep : G →* (G →₀ ℂ) →ₗ[ℂ] (G →₀ ℂ) where
  toFun x := Finsupp.lmapDomain ℂ ℂ (x * ·)
  map_one' := sorry
  map_mul' := by sorry
  -- map_one' := by simp [Finsupp.lmapDomain]
  -- map_mul' := fun x y => by simp [Finsupp.lmapDomain, mul_assoc]

/-!
### Character of the regular representation

\[
  \sum_{\rho \in \hat G} d_\rho\, \operatorname{Tr}(\rho(x)) = |G|\,\delta_{x,e}.
\]
-/
theorem regular_repr_character
    [DecidableEq G]
    (irreps : Finset (Σ d : ℕ, UnitaryRep G d))
    (x : G) :
    ∑ p ∈ irreps, (p.1 : ℂ) * p.2.character G x =
    if x = 1 then Fintype.card G else 0 := by
  sorry

/-!
### Dimension formula


-/

 /-- The sum of squares of dimensions of irreducible representations satisfies
\[
  \sum_{\rho \in \hat G} d_\rho^2 = |G|.
\] -/
theorem sum_dim_sq_eq_card
    (irreps : Finset (Σ d : ℕ, UnitaryRep G d)) :
    ∑ p ∈ irreps, (p.1 ^ 2 : ℕ) = Fintype.card G := by
  sorry

end RepresentationTheory

/-! ## Section 4: Group Fourier Transform -/

section FourierTransform

/-!
### Group Fourier transform

For $f : G \to U_d(\mathbb{C})$ and an irrep $\rho : G \to U_{d_\rho}(\mathbb{C})$,
the Fourier transform of $f$ at $\rho$ is
\[
  \hat f(\rho) = \mathbb{E}_{x \in G}\, f(x) \otimes \overline{\rho(x)}.
\]
-/
noncomputable def groupFourierTransform
    {dρ : ℕ}
    (f : G → Matrix (Fin d) (Fin d) ℂ)
    (ρ : UnitaryRep G dρ) :
    Matrix (Fin d × Fin dρ) (Fin d × Fin dρ) ℂ :=
  (Fintype.card G : ℂ)⁻¹ •
    ∑ x : G,
      Matrix.kronecker
        (f x)
        ((ρ x : Matrix (Fin dρ) (Fin dρ) ℂ).map (starRingEnd ℂ))

end FourierTransform

/-! ## Section 5: Gowers–Hatami Theorem -/

section GowersHatami

/-!
### Gowers–Hatami Theorem

Let $G$ be a finite group, $\varepsilon \ge 0$, and $f : G \to U_d(\mathbb{C})$
an $(\varepsilon, \sigma)$-representation of $G$.  Then there exist $d' \ge d$,
an isometry $V : \mathbb{C}^d \to \mathbb{C}^{d'}$, and an exact representation
$g : G \to U_{d'}(\mathbb{C})$ such that
\[
  \mathbb{E}_{x \in G}\,\|f(x) - V^* g(x) V\|_\sigma^2 \le 2\varepsilon.
\]

**Proof sketch.**  The isometry is defined by
\[
  V u = \bigoplus_\rho d_\rho^{1/2}
    \sum_{i=1}^{d_\rho} \bigl(\hat f(\rho)(u \otimes e_i)\bigr) \otimes e_i,
\]
and the exact representation by
\[
  g(x) = \bigoplus_\rho \bigl(I_d \otimes I_{d_\rho} \otimes \rho(x)\bigr).
\]
Both ingredients rely on the character identity for the regular representation
(Fact `character_regular_rep`):
1. $V^* V = I_d$ (isometry).
2. $V^* g(x) V = \mathbb{E}_z f(z)^* f(zx)$ for all $x \in G$.
-/
theorem gowers_hatami
    (σ : Matrix (Fin d) (Fin d) ℂ)
    (hσ : Matrix.PosSemidef σ) (hσtr : Matrix.trace σ = 1)
    (f : G → Matrix (Fin d) (Fin d) ℂ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hf : IsApproxRepresentation G σ f ε) :
    ∃ (d' : ℕ) (_ : d ≤ d')
      (V : Matrix (Fin d) (Fin d') ℂ)  -- isometry V : ℂᵈ → ℂᵈ'
      (hV : Vᴴ * V = 1)               -- V*V = I
      (g : G →* Matrix.unitaryGroup (Fin d') ℂ),
      (∑ x : G,
        sigmaNormSq σ (f x - V * (g x : Matrix (Fin d') (Fin d') ℂ) * Vᴴ)) /
        Fintype.card G ≤ 2 * ε := by
  sorry

end GowersHatami
