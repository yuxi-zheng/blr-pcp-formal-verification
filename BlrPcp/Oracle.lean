import Architect

import CompPoly.Multivariate.CMvPolynomial
import VCVio.OracleComp.OracleSpec
import VCVio.OracleComp.OracleComp
import VCVio.OracleComp.OracleContext
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.Constructions.SampleableType

open CPoly CMvPolynomial OracleComp

variable {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]

@[blueprint
  (statement := /-- A system of $m$ quadratic equations in $n$ variables
over a field $\F$ is a list of polynomials $p_1, \ldots, p_m \in \F[x_1, \ldots, x_n]$
where each $p_i$ has total degree at most $2$.

$\mathrm{QESAT}(\F) := \{ (p_1, \ldots, p_m) \mid
  ∃ a_1, \ldots, a_n ∈ \F, \, ∀ i ∈ [m], \, p_i(a_1, \ldots, a_n) = 0 \}$. -/)]
abbrev QESAT : Set (List (CMvPolynomial n F)) := fun polys =>
  polys.all (fun p => p.totalDegree ≤ 2) ∧
  ∃ (a : Fin n → F), polys.all (fun p => CMvPolynomial.eval a p == 0)

namespace QESAT
/-- The size of a QESAT instance if it was a binary string
    TODO: the proper way would be to use this: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/Encoding.html -/
def size (polys : List (CMvPolynomial n F)) : ℕ :=
  polys.length * (n + 1)^2
end QESAT

@[blueprint
  (statement := /-- $(x + 1, xy + z) ∈ \mathrm{QESAT}(\F_2)$. -/)]
example : QESAT (n := 3) (F := (ZMod 2)) [C 1 + X 0, X 0 * X 1 + X 0 * X 2] := by native_decide

abbrev RandOracleSpec : OracleSpec Unit :=
  coinSpec

/- A proof is represented as a function `π : [ℓ] → F`.
  `π(q)` is the answer to query `q`. -/
abbrev ProofOracleSpec (F : Type) (ℓ : ℕ) : OracleSpec (Fin ℓ) :=
  Fin ℓ →ₒ F

abbrev RandOracle : OracleContext Unit ProbComp :=
  { spec := RandOracleSpec,
    impl := fun _ => $ᵗ Bool }

abbrev ProofOracle (proof : Fin ℓ → F) : OracleContext (Fin ℓ) ProbComp :=
  { spec := ProofOracleSpec F ℓ,
    impl := fun q => pure (proof q) }

abbrev PCPOracleSpec (F : Type) (ℓ : ℕ) : OracleSpec (Unit ⊕ Fin ℓ) :=
  RandOracleSpec + ProofOracleSpec F ℓ

/-- `PCPQueryBound oa q r` means `oa` makes at most `q` proof queries
and at most `r` randomness queries. -/
def PCPQueryBound {F α : Type} {ℓ : ℕ}
    (oa : OracleComp (PCPOracleSpec F ℓ) α) (q r : ℕ) : Prop :=
  IsQueryBound oa (q, r)
    (fun
      | .inl _, (_, r) => 0 < r
      | .inr _, (q, _) => 0 < q)
    (fun
      | .inl _, (q, r) => (q, r - 1)
      | .inr _, (q, r) => (q - 1, r))

@[blueprint
  (statement := /-- A \textit{PCP prover} is a function that takes an input $x$ and produces a proof
$\pi : [\ell(|x|)] \to \Sigma$, represented as a function from an index set to the PCP alphabet. -/)]
abbrev PCPProver (α : Type) (size : α → ℕ) (F : Type) (ℓ : ℕ → ℕ) : Type :=
  (x : α) → Fin (ℓ (size x)) → F

@[blueprint
  (statement := /-- A \textit{PCP verifier} is an oracle machine that takes an input $x$ and has access to two oracles:
a randomness oracle, and a proof oracle. -/)]
abbrev PCPVerifier (α : Type) (size : α → ℕ) (F : Type) (ℓ : ℕ → ℕ) : Type :=
  (x : α) → OracleComp (PCPOracleSpec F (ℓ (size x))) Bool

/-- TODO: Runtime bound of a computation `V(x)` -/
def RunsInTime {α : Type} {size : α → ℕ} {F : Type} {ℓ : ℕ → ℕ}
    (_ : PCPVerifier α size F ℓ) (_ : α) (_ : ℕ) : Prop :=
  true

@[blueprint
  (statement := /-- A language $L \subseteq \{0,1\}^*$ is in $\mathrm{PCP}[ε_c, ε_s, Σ, ℓ, q, r]$
if there exists a PCP prover $P$, a PCP verifier $V$ and a polynomial $t$ such that for every $x ∈ \{0,1\}^*$ of size $n$,
$P$ produces a proof $\pi$ of length $\ell(n)$,
$V$ runs in time at most $t(n)$,
makes at most $q(n)$ queries to $\pi$
and uses at most $r(n)$ bits of randomness, and the following holds:
\begin{itemize}
  \item Completeness: If $x \in L$, then $\Pr\left[V^\pi(x)=1 \mid \pi \leftarrow P(x)\right] \geq 1 - \varepsilon_c$.
  \item Soundness: If $x \notin L$, then $\forall \widetilde{\pi},\, \Pr\left[V^{\widetilde{\pi}}(x)=1 \right] \leq \varepsilon_s$.
\end{itemize}-/)]
def PCP {α : Type} (size : α → ℕ) (ε_c ε_s : ENNReal) (F : Type)
    (ℓ q r : ℕ → ℕ) : Set (Set α) :=
  { L | ∃ (V : PCPVerifier α size F ℓ) (t : Polynomial ℕ), ∀ x,
    RunsInTime V x (t.eval (size x)) ∧
    PCPQueryBound (V x) (q (size x)) (r (size x)) ∧
    (x ∈ L → ∃ P : PCPProver α size F ℓ,
      Pr[= true | simulateQ (RandOracle.impl + (ProofOracle (P x)).impl) (V x)] ≥ 1 - ε_c ) ∧
    (x ∉ L → ∀ P' : PCPProver α size F ℓ,
      Pr[= true | simulateQ (RandOracle.impl + (ProofOracle (P' x)).impl) (V x)] ≤ ε_s) }

@[blueprint
  (statement := /-- $\mathrm{QESAT}(\F_2) ∈\mathrm{PCP}[ε_c = 0, ε_s = 1/2, \Sigma = \F_2, ℓ = \exp(n), q = O(1), r = n^{O(1)}]$. -/)]
theorem QESAT_exp_PCP {vars : ℕ} : ∃ (q : ℕ) (r : Polynomial ℕ),
    QESAT (n := vars) (F := (ZMod 2)) ∈
      PCP (QESAT.size (n := vars) (F := (ZMod 2))) 0 (1/2) (ZMod 2)
        (fun n => 2 ^ n) (fun _ => q) r.eval := by
  sorry
