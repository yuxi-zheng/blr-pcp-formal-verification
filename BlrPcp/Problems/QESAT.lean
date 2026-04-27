import Architect
import BlrPcp.Oracle
import CompPoly.Multivariate.CMvPolynomial

/-!
# Quadratic equation satisfiability

This file defines the QESAT language and the exponential-length PCP for it.
-/

open CPoly CMvPolynomial

abbrev QESAT (F : Type) [Field F] (n : ℕ) : Set (List (CMvPolynomial n F)) := fun polys =>
  (∀ p ∈ polys, p.totalDegree ≤ 2) ∧
  ∃ (a : Fin n → F), ∀ p ∈ polys, CMvPolynomial.eval a p = 0

namespace QESAT

/-- The size of a QESAT instance if it was a binary string
TODO: the proper way would be to use this:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/Encoding.html -/
def size (F : Type) [Field F] [Fintype F] (n : ℕ) (polys : List (CMvPolynomial n F)) :
    ℕ :=
  polys.length * (n + 1)^2

end QESAT

example : QESAT (ZMod 2) 3 [X 0 + C 1, X 0 * X 1 + X 2] := by native_decide

@[blueprint]
theorem QESAT_exp_PCP {vars : ℕ} : ∃ (q : ℕ) (r : Polynomial ℕ),
    QESAT (ZMod 2) vars ∈
      PCP (QESAT.size (ZMod 2) vars) 0 (1 / 2) (ZMod 2)
        (fun n => 2 ^ n) (fun _ => q) r.eval := by
  sorry
