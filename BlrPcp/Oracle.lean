import Architect

import CompPoly.Multivariate.CMvPolynomial
import VCVio.OracleComp.OracleSpec
import VCVio.OracleComp.OracleComp
import VCVio.OracleComp.OracleContext
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.CostModel
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

/- A coinflip oracle -/
abbrev RandOracle : OracleContext Unit ProbComp :=
  { spec := coinSpec,
    impl := fun _ => $ᵗ Bool }

/- A proof is represented as a function `π : [n] → F`.
  `π(q)` is the answer to query `q`. -/
abbrev ProofOracle (proof : Fin n → F) : OracleContext (Fin n) ProbComp :=
  { spec := Fin n →ₒ F,
    impl := fun q => pure (proof q) }

/- Defining the costs for randomness and query complexity
  TODO: make more ergonomic -/

def randCanQuery : Sum Unit (Fin n) → ℕ → Prop
  | Sum.inl _, b => 0 < b
  | Sum.inr _, _ => True

def randCost : Sum Unit (Fin n) → ℕ → ℕ
  | Sum.inl _, b => b - 1
  | Sum.inr _, b => b

def funcCanQuery : Sum Unit (Fin n) → ℕ → Prop
  | Sum.inl _, _ => True
  | Sum.inr _, b => 0 < b

def funcCost : Sum Unit (Fin n) → ℕ → ℕ
  | Sum.inl _, b => b
  | Sum.inr _, b => b - 1

@[blueprint
  (statement := /-- A \textit{PCP prover} is a function that takes an input $x$ and produces a proof $\pi : [ℓ] → \Sigma$,
represented as a function from an index set to the PCP alphabet. $ℓ$ is the \textit{proof length}. -/)]
abbrev PCPProver (α : Type) (F : Type) (ℓ : ℕ) : Type :=
  α → (Fin ℓ → F)

@[blueprint
  (statement := /-- A \textit{PCP verifier} is an oracle machine that takes an input $x$ and has access to two oracles:
a randomness oracle, and a proof oracle. -/)]
abbrev PCPVerifier (α : Type) (F : Type) (ℓ : ℕ) : Type :=
  α → OracleComp (RandOracle.spec + (Fin ℓ →ₒ F)) Bool

/-- TODO: Runtime bound of a computation `V(x)` -/
def RunsInTime {α : Type} {F : Type} {ℓ : ℕ} (_ : PCPVerifier α F ℓ) (_ : α) (_ : ℕ) : Prop :=
  true

@[blueprint
  (statement := /-- A language $L$ is in $\mathrm{PCP}[ε_c, ε_s, Σ, ℓ, q, r]$
if there exists a prover $P$, a verifier $V$ and a polynomial $t$ such that for every $x ∈ L$ of size $n = |x|$,
$P$ produces a proof $\pi$ of length $\ell(n)$,
$V$ runs in time at most $t(n)$,
makes at most $q(n)$ queries to $\pi$
and uses at most $r(n)$ bits of randomness, and such that the following holds:
\begin{itemize}
  \item Completeness: $\forall x \in L,\, \Pr\left[V^\pi(x)=1 \mid \pi \leftarrow P(x)\right] \geq 1 - \varepsilon_c$.
  \item Soundness: $\forall x \notin L,\, \forall \widetilde{\pi},\, \Pr\left[V^{\widetilde{\pi}}(x)=1 \right] \leq \varepsilon_s$.
\end{itemize}-/)]
def PCP {α : Type} (size : α → ℕ) (ε_c ε_s : ENNReal) (F : Type) (ℓ q r : ℕ) : Set (Set α) :=
  { L | ∃ (V : PCPVerifier α F ℓ) (t : Polynomial ℕ), ∀ x,
    RunsInTime V x (t.eval (size x)) ∧
    IsQueryBound (V x) q funcCanQuery funcCost ∧
    IsQueryBound (V x) r randCanQuery randCost ∧
    (x ∈ L → ∃ P : PCPProver α F ℓ,
      Pr[= true | simulateQ (RandOracle.impl + (ProofOracle (P x)).impl) (V x)] ≥ 1 - ε_c ) ∧
    (x ∉ L → ∀ P' : PCPProver α F ℓ,
      Pr[= true | simulateQ (RandOracle.impl + (ProofOracle (P' x)).impl) (V x)] ≤ ε_s) }

@[blueprint
  (statement := /-- $\mathrm{QESAT}(\F_2) ∈\mathrm{PCP}[ε_c = 0, ε_s = 1/2, \Sigma = \F_2, ℓ = \exp(n), q = O(1), r = n^{O(1)}]$. -/)]
theorem QESAT_exp_PCP {n : ℕ} : ∃ (q : ℕ) (r : Polynomial ℕ),
    QESAT (n := n) (F := (ZMod 2)) ∈ PCP QESAT.size 0 (1/2) (ZMod 2) 0 0 0 := by -- TODO: change ℓ q r to the correct values (for that we need to change the definition of PCP)
  sorry
