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

$\QESAT(\F) := \{ (p_1, \ldots, p_m) \mid
  \exists a_1, \ldots, a_n \in \F, \, \forall i \in [m], \, p_i(a_1, \ldots, a_n) = 0 \}$. -/)]
abbrev QESAT : Set (List (CMvPolynomial n F)) := fun polys =>
  (∀ p ∈ polys, p.totalDegree ≤ 2) ∧
  ∃ (a : Fin n → F), ∀ p ∈ polys, CMvPolynomial.eval a p = 0

namespace QESAT
/-- The size of a QESAT instance if it was a binary string
    TODO: the proper way would be to use this: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/Encoding.html -/
def size (polys : List (CMvPolynomial n F)) : ℕ :=
  polys.length * (n + 1)^2
end QESAT

blueprint_comment /-- For example, $(x + 1, xy + z) \in \QESAT(\F_2)$. -/
example : QESAT (n := 3) (F := (ZMod 2)) [X 0 + C 1, X 0 * X 1 + X 2] := by native_decide

abbrev RandOracleSpec : OracleSpec Unit :=
  coinSpec

abbrev RandOracle : OracleContext Unit ProbComp :=
  { spec := RandOracleSpec,
    impl := fun _ => $ᵗ Bool }

/-- A proof is represented as a function `π : [ℓ] → F`.
  `π(q)` is the answer to query `q`. -/
abbrev ProofOracleSpec (F : Type) (ℓ : ℕ) : OracleSpec (Fin ℓ) :=
  Fin ℓ →ₒ F

abbrev ProofOracle (proof : Fin ℓ → F) : OracleContext (Fin ℓ) ProbComp :=
  { spec := ProofOracleSpec F ℓ,
    impl := fun q => pure (proof q) }

abbrev PCPOracleSpec (F : Type) (ℓ : ℕ) : OracleSpec (Unit ⊕ Fin ℓ) :=
  RandOracleSpec + ProofOracleSpec F ℓ

@[blueprint
  (statement := /-- A \emph{PCP verifier} is a probabilistic oracle Turing machine
$V$ with query access to a function $\pi : [\ell (|x|)] \to \Sigma$. -/)]
abbrev PCPVerifier (α : Type) (size : α → ℕ) (F : Type) (ℓ : ℕ → ℕ) : Type :=
  (x : α) → OracleComp (PCPOracleSpec F (ℓ (size x))) Bool

/-- TODO: Runtime bound of a computation `V(x)` -/
def RunsInTime {α : Type} {size : α → ℕ} {F : Type} {ℓ : ℕ → ℕ}
    (_ : PCPVerifier α size F ℓ) (_ : α) (_ : ℕ) : Prop :=
  true

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
  (statement := /-- A language $L \subseteq \{0,1\}^*$ is in $\PCP[\varepsilon_c, \varepsilon_s, \Sigma, \ell, q, r]$
if there exists a polynomial-time PCP verifier $V$
such that for every $x \in \{0,1\}^*$,
$V$ makes at most $q(|x|)$ queries to the proof oracle,
uses at most $r(n)$ bits of randomness, and the following holds:
\begin{itemize}
  \item Completeness: If $x \in L$, then $\exists \pi \in \Sigma^{\ell(|x|)}, \,
  \Pr\left[V^\pi(x)=1 \right] \geq 1 - \varepsilon_c$.
  \item Soundness: If $x \notin L$, then $\forall \widetilde{\pi} \in \Sigma^{\ell(|x|)},\,
  \Pr\left[V^{\widetilde{\pi}}(x)=1 \right] \leq \varepsilon_s$.
\end{itemize}-/)]
def PCP {α : Type} (size : α → ℕ) (ε_c ε_s : ENNReal) (F : Type)
    [Fintype F] [DecidableEq F] [Inhabited F]
    (ℓ q r : ℕ → ℕ) : Set (Set α) :=
  { L | ∃ (V : PCPVerifier α size F ℓ) (t : Polynomial ℕ), ∀ x,
    RunsInTime V x (t.eval (size x)) ∧
    PCPQueryBound (V x) (q (size x)) (r (size x)) ∧
    (x ∈ L → ∃ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ (RandOracle.impl + (ProofOracle π).impl) (V x)] ≥ 1 - ε_c) ∧
    (x ∉ L → ∀ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ (RandOracle.impl + (ProofOracle π).impl) (V x)] ≤ ε_s) }

blueprint_comment /-- The following theorem is the main goal of this chapter. -/

@[blueprint
  (statement := /-- $\mathrm{QESAT}(\F_2) \in
\mathrm{PCP}[\varepsilon_c = 0, \varepsilon_s = 1/2, \Sigma = \F_2, \ell = \exp(n), q = O(1), r = n^{O(1)}]$. -/)]
theorem QESAT_exp_PCP {vars : ℕ} : ∃ (q : ℕ) (r : Polynomial ℕ),
    QESAT (n := vars) (F := (ZMod 2)) ∈
      PCP (QESAT.size (n := vars) (F := (ZMod 2))) 0 (1/2) (ZMod 2)
        (fun n => 2 ^ n) (fun _ => q) r.eval := by
  sorry

/-- A linear-query proof oracle: a query is a vector `u`,
and the answer is the inner product `⟨π, u⟩`. -/
abbrev LinProofOracleSpec (F : Type) [Field F] (ℓ : ℕ) : OracleSpec (Fin ℓ → F) :=
  (Fin ℓ → F) →ₒ F

abbrev LinProofOracle {F : Type} [Field F] {ℓ : ℕ} (π : Fin ℓ → F) : OracleContext (Fin ℓ → F) ProbComp :=
  { spec := LinProofOracleSpec F ℓ,
    impl := fun u => pure (∑ i, π i * u i) }

abbrev LPCPOracleSpec (F : Type) [Field F] (ℓ : ℕ) : OracleSpec (Unit ⊕ (Fin ℓ → F)) :=
  RandOracleSpec + LinProofOracleSpec F ℓ

@[blueprint
  (statement := /-- A \emph{LPCP verifier} is a probabilistic oracle Turing machine
$V$ with query access to a linear function $\langle \pi,\cdot \rangle : \Sigma^{\ell(|x|)} \to \Sigma$. -/)]
abbrev LPCPVerifier (α : Type) (size : α → ℕ) (F : Type) [Field F]
    (ℓ : ℕ → ℕ) : Type :=
  (x : α) → OracleComp (LPCPOracleSpec F (ℓ (size x))) Bool

/-- TODO: Avoid code duplication by defining runtime for generic OracleComp -/
def LRunsInTime {α : Type} {size : α → ℕ} {F : Type} {ℓ : ℕ → ℕ} [Field F]
    (_ : LPCPVerifier α size F ℓ) (_ : α) (_ : ℕ) : Prop :=
  true

-- TODO: Avoid code duplication
/-- `LPCPQueryBound oa q r` means `oa` makes at most `q` proof queries
and at most `r` randomness queries. -/
def LPCPQueryBound {F α : Type} {ℓ : ℕ} [Field F]
    (oa : OracleComp (LPCPOracleSpec F ℓ) α) (q r : ℕ) : Prop :=
  IsQueryBound oa (q, r)
    (fun
      | .inl _, (_, r) => 0 < r
      | .inr _, (q, _) => 0 < q)
    (fun
      | .inl _, (q, r) => (q, r - 1)
      | .inr _, (q, r) => (q - 1, r))

@[blueprint
  (statement := /-- A language $L \subseteq \{0,1\}^*$ is in $\LPCP[\varepsilon_c, \varepsilon_s, \Sigma, \ell, q, r]$
if there exists a polynomial-time LPCP verifier $V$
such that for every $x \in \{0,1\}^*$,
$V$ makes at most $q(|x|)$ queries to the linear proof oracle,
uses at most $r(n)$ bits of randomness, and the following holds:
\begin{itemize}
  \item Completeness: If $x \in L$, then $\exists \pi \in \Sigma^{\ell(|x|)}, \,
  \Pr\left[V^{\langle \pi, \cdot \rangle}(x)=1 \right] \geq 1 - \varepsilon_c$.
  \item Soundness: If $x \notin L$, then $\forall \widetilde{\pi} \in \Sigma^{\ell(|x|)},\,
  \Pr\left[V^{\langle \widetilde{\pi}, \cdot \rangle}(x)=1 \right] \leq \varepsilon_s$.
\end{itemize}-/)]
def LPCP {α : Type} (size : α → ℕ) (ε_c ε_s : ENNReal) (F : Type)
    [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
    (ℓ q r : ℕ → ℕ) : Set (Set α) :=
  { L | ∃ (V : LPCPVerifier α size F ℓ) (t : Polynomial ℕ), ∀ x,
    LRunsInTime V x (t.eval (size x)) ∧
    LPCPQueryBound (V x) (q (size x)) (r (size x)) ∧
    (x ∈ L → ∃ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ (RandOracle.impl + (LinProofOracle π).impl) (V x)] ≥ 1 - ε_c) ∧
    (x ∉ L → ∀ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ (RandOracle.impl + (LinProofOracle π).impl) (V x)] ≤ ε_s) }
