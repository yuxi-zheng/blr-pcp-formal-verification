import Architect

import CompPoly.Multivariate.CMvPolynomial
import VCVio

#min_imports

variable {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]

@[blueprint
  (statement := /-- A system of $m$ quadratic equations in $n$ variables
  over a field $𝔽$ is a list of polynomials $p_1, \ldots, p_m \in \F[x_1, \ldots, x_n]$
  where each $p_i$ has total degree at most $2$.

  $\mathrm{QESAT}(𝔽) := \{ (p_1, \ldots, p_m) \mid
    ∃ a_1, \ldots, a_n ∈ 𝔽, \, ∀ i ∈ [m], \, p_i(a_1, \ldots, a_n) = 0 \}$. -/)]
abbrev QESAT : Set (List (CMvPolynomial n F)) := fun polys =>
  polys.all (fun p => p.totalDegree ≤ 2) ∧
  ∃ (a : Fin n → F), polys.all (fun p => CMvPolynomial.eval a p == 0)


def p1 : CMvPolynomial 3 𝔽₂ := C 1 + X 0
def p2 : CMvPolynomial 3 𝔽₂ := C 0 + X 0 * X 1 + X 0 * X 2

#eval QESAT (F := 𝔽₂) (n := 3) [p1, p2] -- withness should be (1, 0, 0) or (1, 1, 1)
