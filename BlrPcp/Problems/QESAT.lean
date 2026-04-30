import Architect
import BlrPcp.Oracle
import CompPoly.Multivariate.CMvPolynomial

/-!
# Quadratic equation satisfiability

This file defines the QESAT language and the exponential-length PCP for it.

## Main declarations

- `QESAT`: the language of quadratic equation satisfiability instances.
- `QESAT.size`: the binary-size proxy for QESAT instances.
- `QESAT_exp_PCP`: QESAT over `ZMod 2` has an exponential-length PCP.
-/

open CPoly CMvPolynomial
open scoped ENNReal

abbrev QESAT (F : Type) [Field F] (n : ℕ) : Set (List (CMvPolynomial n F)) :=
  fun polys => (∀ p ∈ polys, p.totalDegree ≤ 2) ∧
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

theorem QESAT_exp_PCP {vars : ℕ} : ∃ (q : ℕ) (r : Polynomial ℕ),
    QESAT (ZMod 2) vars ∈
      PCP (QESAT.size (ZMod 2) vars) 0 (1 / 2) (ZMod 2)
        (fun n => 2 ^ n) (fun _ => q) r.eval := by
  sorry

theorem LPCP_to_PCP_ZMod2 {α : Type} (size : α → ℕ)
    (ε_c ε_s : ℝ≥0∞) (ℓ q r : ℕ → ℕ) :
    LPCP size ε_c ε_s (ZMod 2) ℓ q r
    ⊆ PCP size ε_c (max (7/8) (ε_s + 1/100)) (ZMod 2)
      (fun n => 2 ^ ℓ n)
      (fun n => 3 + 2 * Nat.clog 2 (100 * q n) * q n)
      (fun n => r n + (2 + Nat.clog 2 (100 * q n)) * ℓ n) :=
  sorry
