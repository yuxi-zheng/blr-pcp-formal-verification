import Architect

import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import CompPoly.Multivariate.CMvPolynomial
import VCVio.OracleComp.OracleSpec
import VCVio.OracleComp.OracleComp
import VCVio.OracleComp.OracleContext
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.Constructions.SampleableType

open CPoly CMvPolynomial OracleComp
open scoped Matrix

variable {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]

instance instEncodableZModOfNeZero (q : ℕ) [NeZero q] : Encodable (ZMod q) :=
  Encodable.ofEquiv (Fin q) (ZMod.finEquiv q).symm

@[blueprint
  (statement := /-- A system of $m$ quadratic equations in $n$ variables
over a field $\F$ is a list of polynomials $p_1, \ldots, p_m \in \F[x_1, \ldots, x_n]$
where each $p_i$ has total degree at most $2$.

\[\QESAT(\F) := \{ (p_1, \ldots, p_m) \mid
  \exists a_1, \ldots, a_n \in \F, \, \forall i \in [m], \, p_i(a_1, \ldots, a_n) = 0 \}.\] -/)]
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

abbrev RandOracleSpec : OracleSpec ℕ :=
  unifSpec

abbrev RandOracle : OracleContext ℕ ProbComp :=
  { spec := RandOracleSpec,
    impl := fun n => $ᵗ Fin (n + 1) }

/-- A proof is represented as a function `π : [ℓ] → F`.
  `π(q)` is the answer to query `q`. -/
abbrev ProofOracleSpec (F : Type) (ℓ : ℕ) : OracleSpec (Fin ℓ) :=
  Fin ℓ →ₒ F

abbrev ProofOracle (proof : Fin ℓ → F) : OracleContext (Fin ℓ) ProbComp :=
  { spec := ProofOracleSpec F ℓ,
    impl := fun q => pure (proof q) }

abbrev PCPOracleSpec (F : Type) (ℓ : ℕ) : OracleSpec (ℕ ⊕ Fin ℓ) :=
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
      | .inl n, (_, r) => Nat.clog 2 (n + 1) ≤ r
      | .inr _, (q, _) => 0 < q)
    (fun
      | .inl n, (q, r) => (q, r - Nat.clog 2 (n + 1))
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
    impl := fun u => pure (π ⬝ᵥ u) }

abbrev LPCPOracleSpec (F : Type) [Field F] (ℓ : ℕ) : OracleSpec (ℕ ⊕ (Fin ℓ → F)) :=
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
      | .inl n, (_, r) => Nat.clog 2 (n + 1) ≤ r
      | .inr _, (q, _) => 0 < q)
    (fun
      | .inl n, (q, r) => (q, r - Nat.clog 2 (n + 1))
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

abbrev LINEQ (m n : ℕ) (F : Type) [Field F] :
    Set (Matrix (Fin m) (Fin n) F × (Fin m → F)) :=
  { (M, c) | ∃ b, M *ᵥ b = c }

namespace LINEQ
def size {m n : ℕ} (_ : (Matrix (Fin m) (Fin n) F) × (Fin m → F)) : ℕ :=
  (m * n + m) * Nat.clog 2 (Fintype.card F)

omit [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma dotProduct_transpose_mulVec_eq {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) F) (b : Fin n → F) (c r : Fin m → F)
    (h : M *ᵥ b = c) :
    b ⬝ᵥ (Mᵀ *ᵥ r) = c ⬝ᵥ r := by
  rw [← h, Matrix.mulVec_transpose]
  rw [dotProduct_comm b (r ᵥ* M)]
  rw [← Matrix.dotProduct_mulVec r M b]
  rw [dotProduct_comm r (M *ᵥ b)]

omit [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma dotProduct_sub_right {m : ℕ} (a b c : Fin m → F) :
    a ⬝ᵥ (b - c) = a ⬝ᵥ b - a ⬝ᵥ c := by
  simp [dotProduct, sub_eq_add_neg, mul_add, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]

omit [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma sub_dotProduct {m : ℕ} (a b c : Fin m → F) :
    (a - b) ⬝ᵥ c = a ⬝ᵥ c - b ⬝ᵥ c := by
  simp [dotProduct, sub_mul, Finset.sum_sub_distrib]

omit [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma dotProduct_eq_add_sum_erase {m : ℕ} (a b : Fin m → F) (k : Fin m) :
    a ⬝ᵥ b = a k * b k + ∑ i ∈ (Finset.univ.erase k), a i * b i := by
  rw [dotProduct]
  exact (Finset.add_sum_erase Finset.univ (fun i => a i * b i) (Finset.mem_univ k)).symm

noncomputable def normalizeLinearForm {m : ℕ} (a : Fin m → F) (k : Fin m) :
    (Fin m → F) → (Fin m → F) :=
  fun r i => if i = k then (a ⬝ᵥ r) / a k else r i

noncomputable def normalizeLinearFormInv {m : ℕ} (a : Fin m → F) (k : Fin m) :
    (Fin m → F) → (Fin m → F) :=
  fun r i =>
    if i = k then
      r k - (∑ j ∈ (Finset.univ.erase k), a j * r j) / a k
    else
      r i

omit [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma normalizeLinearForm_left_inv {m : ℕ} {a : Fin m → F} {k : Fin m}
    (hk : a k ≠ 0) :
    Function.LeftInverse (normalizeLinearFormInv (F := F) a k)
      (normalizeLinearForm (F := F) a k) := by
  intro r
  funext i
  by_cases hi : i = k
  · rw [hi]
    have hsum :
        (∑ j ∈ (Finset.univ.erase k),
            a j * normalizeLinearForm (F := F) a k r j) =
          ∑ j ∈ (Finset.univ.erase k), a j * r j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
      simp [normalizeLinearForm, hjk]
    simp only [normalizeLinearFormInv]
    rw [hsum]
    simp only [normalizeLinearForm]
    rw [dotProduct_eq_add_sum_erase (a := a) (b := r) (k := k)]
    simp
    field_simp [hk]
    ring_nf
  · simp [normalizeLinearForm, normalizeLinearFormInv, hi]

omit [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma normalizeLinearForm_right_inv {m : ℕ} {a : Fin m → F} {k : Fin m}
    (hk : a k ≠ 0) :
    Function.RightInverse (normalizeLinearFormInv (F := F) a k)
      (normalizeLinearForm (F := F) a k) := by
  intro r
  funext i
  by_cases hi : i = k
  · rw [hi]
    have hsum :
        (∑ j ∈ (Finset.univ.erase k),
            a j * normalizeLinearFormInv (F := F) a k r j) =
          ∑ j ∈ (Finset.univ.erase k), a j * r j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
      simp [normalizeLinearFormInv, hjk]
    simp only [normalizeLinearForm]
    rw [dotProduct_eq_add_sum_erase (a := a)
      (b := normalizeLinearFormInv (F := F) a k r) (k := k)]
    rw [hsum]
    simp only [normalizeLinearFormInv]
    simp
    field_simp [hk]
    ring_nf
  · simp [normalizeLinearForm, normalizeLinearFormInv, hi]

omit [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma normalizeLinearForm_bijective {m : ℕ} {a : Fin m → F} {k : Fin m}
    (hk : a k ≠ 0) :
    Function.Bijective (normalizeLinearForm (F := F) a k) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨normalizeLinearFormInv (F := F) a k,
      normalizeLinearForm_left_inv (F := F) hk,
      normalizeLinearForm_right_inv (F := F) hk⟩

omit [Inhabited F] [SampleableType F] in
lemma coordinate_zero_card_div_le {m : ℕ} (k : Fin m) :
    (((Finset.univ.filter fun r : Fin m → F => r k = 0).card : NNReal) /
        (Fintype.card F : NNReal) ^ m) ≤
      1 / (Fintype.card F : NNReal) := by
  have hsz :=
    MvPolynomial.schwartz_zippel_sum_degreeOf
      (R := F) (p := (MvPolynomial.X k : MvPolynomial (Fin m) F))
      (MvPolynomial.X_ne_zero k)
      (fun _ : Fin m => (Finset.univ : Finset F))
  have hsz' :
      (((Finset.univ.filter fun r : Fin m → F => r k = 0).card : ℚ≥0) /
          (Fintype.card F ^ m : ℚ≥0)) ≤
        1 / (Fintype.card F : ℚ≥0) := by
    calc
      (((Finset.univ.filter fun r : Fin m → F => r k = 0).card : ℚ≥0) /
          (Fintype.card F ^ m : ℚ≥0)) ≤
        ∑ i : Fin m, (if i = k then (1 : ℚ≥0) else 0) /
          (Fintype.card F : ℚ≥0) := by
          simpa [MvPolynomial.eval_X, MvPolynomial.degreeOf_X, Fintype.card_piFinset_const]
            using hsz
      _ = 1 / (Fintype.card F : ℚ≥0) := by
        rw [← Finset.sum_div]
        simp
  simpa using (NNRat.cast_mono (K := NNReal) hsz')

lemma uniform_coordinate_zero_prob_mul_card_le_one {m : ℕ} (k : Fin m) :
    Pr[fun r : Fin m → F => r k = 0 |
        ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] *
      (Fintype.card F : ENNReal) ≤ 1 := by
  have hF0 : (Fintype.card F : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := F)).ne'
  have hFtop : (Fintype.card F : ENNReal) ≠ ⊤ := by simp
  have hsz := coordinate_zero_card_div_le (F := F) k
  have hszENN :
      (((Finset.univ.filter fun r : Fin m → F => r k = 0).card : ENNReal) /
          (Fintype.card F : ENNReal) ^ m) ≤
        1 / (Fintype.card F : ENNReal) := by
    have hF0NN : (Fintype.card F : NNReal) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := F)).ne'
    have hpow0NN : (Fintype.card F : NNReal) ^ m ≠ 0 := pow_ne_zero _ hF0NN
    rw [← ENNReal.coe_natCast ((Finset.univ.filter fun r : Fin m → F => r k = 0).card),
      ← ENNReal.coe_natCast (Fintype.card F), ← ENNReal.coe_pow, ← ENNReal.coe_one,
      ← ENNReal.coe_div hpow0NN, ← ENNReal.coe_div hF0NN]
    exact ENNReal.coe_le_coe.mpr hsz
  rw [probEvent_uniformSample]
  rw [Fintype.card_fun, Fintype.card_fin]
  norm_num [Nat.cast_pow]
  calc
    ((Finset.univ.filter fun r : Fin m → F => r k = 0).card : ENNReal) /
          (Fintype.card F : ENNReal) ^ m * (Fintype.card F : ENNReal)
        ≤ (1 / (Fintype.card F : ENNReal)) * (Fintype.card F : ENNReal) := by
          exact mul_le_mul_left hszENN _
    _ = 1 := by
      exact ENNReal.div_mul_cancel hF0 hFtop
    _ ≤ 1 := le_rfl

lemma linear_form_uniform_prob_mul_card_le_one {m : ℕ} {a : Fin m → F}
    (ha : a ≠ 0) :
    Pr[fun r : Fin m → F => a ⬝ᵥ r = 0 |
        ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] *
      (Fintype.card F : ENNReal) ≤ 1 := by
  obtain ⟨k, hk⟩ : ∃ k, a k ≠ 0 := by
    by_contra h
    apply ha
    funext k
    exact by
      simpa using not_exists.mp h k
  let T : (Fin m → F) → (Fin m → F) := normalizeLinearForm (F := F) a k
  have hprob :
      Pr[fun r : Fin m → F => a ⬝ᵥ r = 0 |
          ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] =
        Pr[fun r : Fin m → F => r k = 0 |
          ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] := by
    calc
      Pr[fun r : Fin m → F => a ⬝ᵥ r = 0 |
          ($ᵗ (Fin m → F) : ProbComp (Fin m → F))]
          = Pr[fun r : Fin m → F => T r k = 0 |
              ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] := by
            apply probEvent_ext
            intro r _hr
            simp [T, normalizeLinearForm, hk]
      _ = Pr[fun r : Fin m → F => r k = 0 |
              T <$> ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] := by
            exact (probEvent_map
              (mx := ($ᵗ (Fin m → F) : ProbComp (Fin m → F)))
              (f := T) (q := fun r : Fin m → F => r k = 0)).symm
      _ = Pr[fun r : Fin m → F => r k = 0 |
              ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] := by
            have hdist :
                evalDist (T <$> ($ᵗ (Fin m → F) : ProbComp (Fin m → F))) =
                  evalDist ($ᵗ (Fin m → F) : ProbComp (Fin m → F)) := by
              exact evalDist_map_bijective_uniform_cross
                (α := Fin m → F) (β := Fin m → F) T
                (normalizeLinearForm_bijective (F := F) hk)
            simp [probEvent_def, hdist]
  rw [hprob]
  exact uniform_coordinate_zero_prob_mul_card_le_one (F := F) k

def decodeUniformFin (α : Type) [Fintype α] [Encodable α] [Nonempty α] :
    Fin (Fintype.card α - 1 + 1) → α :=
  fun i => (Encodable.fintypeEquivFin (α := α)).symm (Fin.cast (by
    have h : 0 < Fintype.card α := Fintype.card_pos
    omega) i)

lemma decodeUniformFin_bijective (α : Type) [Fintype α] [Encodable α] [Nonempty α] :
    Function.Bijective (decodeUniformFin α) := by
  constructor
  · intro i j hij
    apply Fin.ext
    have h :=
      congrArg (Encodable.fintypeEquivFin (α := α)) hij
    exact congrArg Fin.val (by simpa [decodeUniformFin] using h)
  · intro a
    refine ⟨Fin.cast (by
      have h : 0 < Fintype.card α := Fintype.card_pos
      omega) ((Encodable.fintypeEquivFin (α := α)) a), ?_⟩
    simp [decodeUniformFin]

lemma probEvent_decodeUniformFin (α : Type) [Fintype α] [Encodable α] [Nonempty α]
    [SampleableType α] (p : α → Prop) :
    Pr[p | decodeUniformFin α <$>
        ($ᵗ Fin (Fintype.card α - 1 + 1) : ProbComp (Fin (Fintype.card α - 1 + 1)))] =
      Pr[p | ($ᵗ α : ProbComp α)] := by
  have hdist :
      evalDist (decodeUniformFin α <$>
          ($ᵗ Fin (Fintype.card α - 1 + 1) :
            ProbComp (Fin (Fintype.card α - 1 + 1)))) =
        evalDist ($ᵗ α : ProbComp α) := by
    exact evalDist_map_bijective_uniform_cross
      (α := Fin (Fintype.card α - 1 + 1)) (β := α)
      (decodeUniformFin α) (decodeUniformFin_bijective α)
  simp [probEvent_def, hdist]

def sampleRandomVector (m n : ℕ) (F : Type) [Field F] [Fintype F]
    [Encodable F] [DecidableEq F] [Inhabited F] :
    OracleComp (LPCPOracleSpec F n) (Fin m → F) :=
  if _ : m = 0 then
    pure default
  else do
    let i ← OracleComp.query (spec := LPCPOracleSpec F n)
      (.inl (Fintype.card (Fin m → F) - 1))
    pure (decodeUniformFin (Fin m → F) i)

def verifier {m n : ℕ} [Encodable F]
    (x : Matrix (Fin m) (Fin n) F × (Fin m → F)) :
    OracleComp (LPCPOracleSpec F n) Bool := do
  let r ← sampleRandomVector m n F
  let u : Fin n → F := x.1ᵀ *ᵥ r
  let y ← OracleComp.query (spec := LPCPOracleSpec F n) (.inr u)
  pure (y = x.2 ⬝ᵥ r)

omit [Field F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma randomVector_card_clog_le (m : ℕ) :
    Nat.clog 2 (Fintype.card (Fin m → F)) ≤
      m * Nat.clog 2 (Fintype.card F) := by
  rw [Fintype.card_pi_const]
  have hcard : Fintype.card F ≤ 2 ^ Nat.clog 2 (Fintype.card F) :=
    Nat.le_pow_clog (by decide) _
  have hpow := Nat.pow_le_pow_left hcard m
  rw [← Nat.pow_mul, Nat.mul_comm] at hpow
  exact Nat.clog_le_of_le_pow hpow

omit [SampleableType F] in
lemma verifier_queryBound {m n : ℕ} [Encodable F]
    (x : Matrix (Fin m) (Fin n) F × (Fin m → F)) :
    LPCPQueryBound (verifier (F := F) x) 1 (m * Nat.clog 2 (Fintype.card F)) := by
  by_cases hm : m = 0
  · simp [verifier, sampleRandomVector, LPCPQueryBound, hm]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hcardSample :
        Fintype.card (Fin m → F) - 1 + 1 = Fintype.card (Fin m → F) := by
      have hpos : 0 < Fintype.card (Fin m → F) := Fintype.card_pos
      omega
    have hbits :
        Nat.clog 2 (Fintype.card (Fin m → F) - 1 + 1) ≤
          m * Nat.clog 2 (Fintype.card F) := by
      rw [hcardSample]
      exact randomVector_card_clog_le (F := F) m
    simp only [verifier, sampleRandomVector, LPCPQueryBound, hm, ↓reduceDIte]
    simp only [bind_assoc, pure_bind]
    rw [OracleComp.isQueryBound_query_bind_iff]
    exact ⟨hbits, by
      intro a
      simp [map_eq_bind_pure_comp, OracleComp.isQueryBound_query_bind_iff]⟩
end LINEQ

theorem LINEQ_LPCP {m n : ℕ} :
    LINEQ m n (F := F) ∈ LPCP (LINEQ.size) 0 (1 / (Fintype.card F)) F
      (fun _ => n) (fun _ => 1) (fun _ => m * Nat.clog 2 (Fintype.card F)) := by
  letI : Encodable F := Encodable.ofCountable F
  refine ⟨LINEQ.verifier (F := F), 0, ?_⟩
  intro x
  refine ⟨by simp [LRunsInTime], LINEQ.verifier_queryBound (F := F) x, ?_, ?_⟩
  · intro hx
    rcases x with ⟨M, c⟩
    rcases hx with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    simp [LINEQ.verifier, LINEQ.sampleRandomVector, LINEQ.dotProduct_transpose_mulVec_eq,
      hb]
  · intro hx π
    rcases x with ⟨M, c⟩
    by_cases hm : m = 0
    · exfalso
      apply hx
      refine ⟨π, ?_⟩
      ext i
      exact Fin.elim0 (hm ▸ i)
    · have hd : M *ᵥ π - c ≠ 0 := by
        intro h
        apply hx
        exact ⟨π, sub_eq_zero.mp h⟩
      have hbound :
          Pr[fun r : Fin m → F => (M *ᵥ π - c) ⬝ᵥ r = 0 |
              ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] *
            (Fintype.card F : ENNReal) ≤ 1 :=
        LINEQ.linear_form_uniform_prob_mul_card_le_one (F := F) hd
      simp [LINEQ.verifier, LINEQ.sampleRandomVector, hm]
      rw [← probEvent_eq_eq_probOutput]
      rw [probEvent_map]
      change
        Pr[fun a : Fin (Fintype.card (Fin m → F) - 1 + 1) =>
            decide (π ⬝ᵥ (Mᵀ *ᵥ LINEQ.decodeUniformFin (Fin m → F) a) =
              c ⬝ᵥ LINEQ.decodeUniformFin (Fin m → F) a) = true |
          ($ᵗ Fin (Fintype.card (Fin m → F) - 1 + 1) :
            ProbComp (Fin (Fintype.card (Fin m → F) - 1 + 1)))] *
          (Fintype.card F : ENNReal) ≤ 1
      have hdecode :
          Pr[fun a : Fin (Fintype.card (Fin m → F) - 1 + 1) =>
              decide (π ⬝ᵥ (Mᵀ *ᵥ LINEQ.decodeUniformFin (Fin m → F) a) =
                c ⬝ᵥ LINEQ.decodeUniformFin (Fin m → F) a) = true |
            ($ᵗ Fin (Fintype.card (Fin m → F) - 1 + 1) :
              ProbComp (Fin (Fintype.card (Fin m → F) - 1 + 1)))] =
            Pr[fun r : Fin m → F =>
              decide (π ⬝ᵥ (Mᵀ *ᵥ r) = c ⬝ᵥ r) = true |
              ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] := by
        calc
          Pr[fun a : Fin (Fintype.card (Fin m → F) - 1 + 1) =>
              decide (π ⬝ᵥ (Mᵀ *ᵥ LINEQ.decodeUniformFin (Fin m → F) a) =
                c ⬝ᵥ LINEQ.decodeUniformFin (Fin m → F) a) = true |
            ($ᵗ Fin (Fintype.card (Fin m → F) - 1 + 1) :
              ProbComp (Fin (Fintype.card (Fin m → F) - 1 + 1)))]
              = Pr[fun r : Fin m → F =>
                  decide (π ⬝ᵥ (Mᵀ *ᵥ r) = c ⬝ᵥ r) = true |
                LINEQ.decodeUniformFin (Fin m → F) <$>
                  ($ᵗ Fin (Fintype.card (Fin m → F) - 1 + 1) :
                    ProbComp (Fin (Fintype.card (Fin m → F) - 1 + 1)))] := by
                simp [Function.comp_def]
          _ = Pr[fun r : Fin m → F =>
                  decide (π ⬝ᵥ (Mᵀ *ᵥ r) = c ⬝ᵥ r) = true |
                ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] := by
                exact LINEQ.probEvent_decodeUniformFin (Fin m → F)
                  (fun r : Fin m → F =>
                    decide (π ⬝ᵥ (Mᵀ *ᵥ r) = c ⬝ᵥ r) = true)
      rw [hdecode]
      have hevent :
          Pr[fun r : Fin m → F => decide (π ⬝ᵥ (Mᵀ *ᵥ r) = c ⬝ᵥ r) = true |
              ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] =
            Pr[fun r : Fin m → F => (M *ᵥ π - c) ⬝ᵥ r = 0 |
              ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] := by
        apply probEvent_ext
        intro r _hr
        have htranspose :
            π ⬝ᵥ (Mᵀ *ᵥ r) = (M *ᵥ π) ⬝ᵥ r :=
          LINEQ.dotProduct_transpose_mulVec_eq (F := F) M π (M *ᵥ π) r rfl
        constructor
        · intro h
          rw [LINEQ.sub_dotProduct]
          rw [← htranspose]
          exact sub_eq_zero.mpr (of_decide_eq_true h)
        · intro h
          rw [LINEQ.sub_dotProduct] at h
          have h' : π ⬝ᵥ (Mᵀ *ᵥ r) = c ⬝ᵥ r := by
            rw [htranspose]
            exact sub_eq_zero.mp h
          exact decide_eq_true h'
      rw [hevent]
      exact hbound
