import Architect
import BlrPcp.Oracle
import CompPoly.Multivariate.CMvPolynomial
import VCVio.OracleComp.Constructions.Replicate

/-!
# Quadratic equation satisfiability

This file defines the QESAT language and the exponential-length PCP for it.

## Main declarations

- `QESAT`: the language of quadratic equation satisfiability instances.
- `QESAT.size`: the binary-size proxy for QESAT instances.
- `QESAT_exp_LPCP`: QESAT over `ZMod 2` has an exponential-length LPCP.
- `LPCP_to_PCP_ZMod2`: the conversion lemma from LPCP to PCP for `ZMod 2`.
- `QESAT_exp_PCP`: QESAT over `ZMod 2` has an exponential-length PCP.
-/

open CPoly CMvPolynomial
open OracleComp
open scoped ENNReal

abbrev QESAT (F : Type) [Field F] (n : ℕ) : Set (List (CMvPolynomial n F)) :=
  fun polys => (∀ p ∈ polys, p.totalDegree ≤ 2) ∧
    ∃ (a : Fin n → F), ∀ p ∈ polys, CMvPolynomial.eval a p = 0

example : QESAT (ZMod 2) 3 [X 0 + C 1, X 0 * X 1 + X 2] := by native_decide

namespace QESAT

/-- The size of a QESAT instance if it was a binary string
TODO: the proper way would be to use this:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/Encoding.html -/
def size (F : Type) [Field F] [Fintype F] (n : ℕ) (polys : List (CMvPolynomial n F)) :
    ℕ :=
  polys.length * (n + 1)^2

private lemma length_eq_zero_of_not_pow_le {vars : ℕ}
    (x : List (CMvPolynomial vars (ZMod 2)))
    (hlen : ¬2 ^ (vars + vars ^ 2) ≤ 2 ^ (QESAT.size (ZMod 2) vars x)) :
    x.length = 0 := by
  by_contra hx
  have hpos : 0 < x.length := Nat.pos_of_ne_zero hx
  have hpow : 2 ^ (vars + vars ^ 2) ≤ 2 ^ (QESAT.size (ZMod 2) vars x) := by
    unfold QESAT.size
    apply Nat.pow_le_pow_right
    · norm_num
    · nlinarith [sq_nonneg (vars : ℤ), hpos]
  exact hlen hpow

private lemma mem_of_length_eq_zero {vars : ℕ} (x : List (CMvPolynomial vars (ZMod 2)))
    (hx : x.length = 0) :
    x ∈ QESAT (ZMod 2) vars := by
  have hxnil : x = [] := List.eq_nil_of_length_eq_zero hx
  subst hxnil
  constructor
  · simp
  · exact ⟨fun _ => 0, by simp⟩

private lemma soundness_before_repetition :
    max (7 / 8 : ℝ≥0∞) (3 / 4 + 1 / 100) = 7 / 8 := by
  rw [max_eq_left]
  refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
  · exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.div_ne_top (by simp) (by norm_num),
        ENNReal.div_ne_top (by simp) (by norm_num)⟩
  · exact ENNReal.div_ne_top (by simp) (by norm_num)
  · rw [ENNReal.toReal_add]
    · rw [ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]
      norm_num
    · exact ENNReal.div_ne_top (by simp) (by norm_num)
    · exact ENNReal.div_ne_top (by simp) (by norm_num)

end QESAT

namespace PCP

private def padImpl (F : Type) {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) :
    QueryImpl (PCP.spec F n₀) (OracleComp (PCP.spec F n₁))
  | .inl () => query (spec := PCP.spec F n₁) (.inl ())
  | .inr i => query (spec := PCP.spec F n₁) (.inr (Fin.castLE h i))

private lemma queryBound_simulateQ_padImpl {F : Type} {n₀ n₁ : ℕ} (h : n₀ ≤ n₁)
    {α : Type} {oa : OracleComp (PCP.spec F n₀) α} {q r : ℕ}
    (hoa : QueryBound oa q r) :
    QueryBound (simulateQ (padImpl F h) oa) q r := by
  revert q r
  induction oa using OracleComp.inductionOn with
  | pure _ =>
      intro q r hoa
      simp
  | query_bind t mx ih =>
      intro q r hoa
      rw [QueryBound, OracleComp.isQueryBound_query_bind_iff] at hoa
      cases t with
      | inl u =>
          rcases u
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
            OracleQuery.input_query, padImpl]
          rw [QueryBound, OracleComp.isQueryBound_query_bind_iff]
          exact ⟨hoa.1, fun y => ih y (hoa.2 y)⟩
      | inr _ =>
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
            OracleQuery.input_query, padImpl]
          rw [QueryBound, OracleComp.isQueryBound_query_bind_iff]
          exact ⟨hoa.1, fun y => ih y (hoa.2 y)⟩

private lemma simulateQ_padImpl_eq {F : Type} [SampleableType F] {n₀ n₁ : ℕ}
    (h : n₀ ≤ n₁) {α : Type} (oa : OracleComp (PCP.spec F n₀) α)
    (π₀ : Fin n₀ → F) (π₁ : Fin n₁ → F)
    (hπ : ∀ i, π₁ (Fin.castLE h i) = π₀ i) :
    simulateQ ((rand F).impl + (PCP.proof π₁).impl) (simulateQ (padImpl F h) oa) =
      simulateQ ((rand F).impl + (PCP.proof π₀).impl) oa := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  apply QueryImpl.ext
  intro t
  cases t with
  | inl u =>
      rcases u
      simp [padImpl]
  | inr i =>
      simp [padImpl, hπ i]

end PCP

private lemma queryBound_map {ρ ι α β : Type} {randSpec : OracleSpec ρ}
    {proofSpec : OracleSpec ι} {oa : OracleComp (randSpec + proofSpec) α}
    {q r : ℕ} (f : α → β) (hoa : QueryBound oa q r) :
    QueryBound (f <$> oa) q r := by
  simpa [QueryBound] using
    (OracleComp.isQueryBound_map_iff oa f (r, q)
      (fun
        | .inl _, (r, _) => 0 < r
        | .inr _, (_, q) => 0 < q)
      (fun
        | .inl _, (r, q) => (r - 1, q)
        | .inr _, (r, q) => (r, q - 1))).2 hoa

private lemma queryBound_replicate {ρ ι α : Type} {randSpec : OracleSpec ρ}
    {proofSpec : OracleSpec ι} {oa : OracleComp (randSpec + proofSpec) α}
    {q r : ℕ} (n : ℕ) (hoa : QueryBound oa q r) :
    QueryBound (OracleComp.replicate n oa) (n * q) (n * r) := by
  induction n with
  | zero =>
      simp [OracleComp.replicate, QueryBound]
  | succ n ih =>
      rw [OracleComp.replicate_succ_bind]
      simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        queryBound_bind hoa fun x => queryBound_map (List.cons x) ih

private lemma simulateQ_replicate {ι ι' α : Type} {spec : OracleSpec ι}
    {spec' : OracleSpec ι'} (impl : QueryImpl spec (OracleComp spec')) (n : ℕ)
    (oa : OracleComp spec α) :
    simulateQ impl (OracleComp.replicate n oa) =
      OracleComp.replicate n (simulateQ impl oa) := by
  induction n with
  | zero =>
      simp [OracleComp.replicate]
  | succ n ih =>
      simp [OracleComp.replicate_succ_bind, ih]

private lemma probOutput_true_all_replicate (mx : ProbComp Bool) (n : ℕ) :
    Pr[= true | do
      let xs ← OracleComp.replicate n mx
      pure (xs.all id)] = Pr[= true | mx] ^ n := by
  have hEvent :
      Pr[= true | do
        let xs ← OracleComp.replicate n mx
        pure (xs.all id)] =
        Pr[fun xs : List Bool => xs.all id = true | OracleComp.replicate n mx] := by
    rw [show (do
        let xs ← OracleComp.replicate n mx
        pure (xs.all id)) =
        (fun xs : List Bool => xs.all id) <$> OracleComp.replicate n mx by rfl]
    rw [probOutput_map_eq_tsum_ite, probEvent_eq_tsum_ite]
    apply tsum_congr
    intro xs
    by_cases h : xs.all id = true <;> simp [h]
  rw [hEvent]
  simpa using OracleComp.probEvent_replicate_of_probEvent_cons mx n
    (p := fun xs : List Bool => xs.all id = true)
    (by simp)
    (q := fun b : Bool => b = true)
    (by intro x xs; cases x <;> simp)

private lemma repeated_accept_le {mx : ProbComp Bool} {ε : ℝ≥0∞} {n : ℕ}
    (hmx : Pr[= true | mx] ≤ ε) :
    Pr[= true | do
      let xs ← OracleComp.replicate n mx
      pure (xs.all id)] ≤ ε ^ n := by
  rw [probOutput_true_all_replicate]
  exact pow_le_pow_left₀ (by simp) hmx n

private lemma repeated_accept_ge_one {mx : ProbComp Bool} {n : ℕ}
    (hmx : Pr[= true | mx] ≥ 1) :
    Pr[= true | do
      let xs ← OracleComp.replicate n mx
      pure (xs.all id)] ≥ 1 := by
  rw [probOutput_true_all_replicate]
  exact one_le_pow₀ hmx

private lemma seven_eighths_pow_six_le_half : ((7 / 8 : ℝ≥0∞) ^ 6) ≤ 1 / 2 := by
  refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
  · simp [ENNReal.div_ne_top]
  · exact ENNReal.div_ne_top (by simp) (by norm_num)
  · rw [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_div]
    norm_num

theorem QESAT_exp_LPCP {vars : ℕ} :
    QESAT (ZMod 2) vars ∈
      LPCP (QESAT.size (ZMod 2) vars) 0 (3 / 4) (ZMod 2)
        (fun _ => vars + vars ^ 2) (fun _ => 4) (fun n => n + 2 * vars) := by
  sorry

theorem LPCP_to_PCP_ZMod2 {α : Type} (size : α → ℕ)
    (ε_c ε_s : ℝ≥0∞) (ℓ q r : ℕ → ℕ) :
    LPCP size ε_c ε_s (ZMod 2) ℓ q r
    ⊆ PCP size ε_c (max (7 / 8) (ε_s + 1 / 100)) (ZMod 2)
      (fun n => 2 ^ ℓ n)
      (fun n => 3 + 2 * Nat.clog 2 (100 * q n) * q n)
      (fun n => r n + (2 + Nat.clog 2 (100 * q n)) * ℓ n) :=
  sorry

theorem QESAT_exp_PCP_before_repetition {vars : ℕ} : ∃ (q : ℕ) (r : Polynomial ℕ),
    QESAT (ZMod 2) vars ∈
      PCP (QESAT.size (ZMod 2) vars) 0 (7 / 8) (ZMod 2)
        (fun n => 2 ^ n) (fun _ => q) r.eval := by
  let q' := 3 + 2 * Nat.clog 2 (100 * 4) * 4
  let c := 2 + Nat.clog 2 (100 * 4)
  let r' : Polynomial ℕ :=
    Polynomial.X + Polynomial.C (2 * vars) + Polynomial.C c * Polynomial.C (vars + vars ^ 2)
  refine ⟨q', r', ?_⟩
  have hConverted := (LPCP_to_PCP_ZMod2 (QESAT.size (ZMod 2) vars)
    0 (3 / 4) (fun _ => vars + vars ^ 2) (fun _ => 4) (fun n => n + 2 * vars))
      (QESAT_exp_LPCP (vars := vars))
  rw [QESAT.soundness_before_repetition] at hConverted
  rcases hConverted with ⟨V₀, t, hV₀⟩
  let V : PCPVerifier (List (CMvPolynomial vars (ZMod 2))) (QESAT.size (ZMod 2) vars)
      (ZMod 2) (fun n => 2 ^ n) := fun x =>
    if hlen : 2 ^ (vars + vars ^ 2) ≤ 2 ^ (QESAT.size (ZMod 2) vars x) then
      simulateQ (PCP.padImpl (ZMod 2) hlen) (V₀ x)
    else pure true
  refine ⟨V, t, fun x => ?_⟩
  rcases hV₀ x with ⟨_, hQuery, hComplete, hSound⟩
  refine ⟨by simp [RunsInTime], ?_, ?_, ?_⟩
  · by_cases hlen : 2 ^ (vars + vars ^ 2) ≤ 2 ^ (QESAT.size (ZMod 2) vars x)
    · simp only [V, hlen, ↓reduceDIte]
      simpa [q', r', c, Polynomial.eval_add, Polynomial.eval_mul] using
        PCP.queryBound_simulateQ_padImpl hlen hQuery
    · simp [V, hlen, QueryBound]
  · intro hxL
    by_cases hlen : 2 ^ (vars + vars ^ 2) ≤ 2 ^ (QESAT.size (ZMod 2) vars x)
    · rcases hComplete hxL with ⟨π₀, hπ₀⟩
      let π₁ : Fin (2 ^ QESAT.size (ZMod 2) vars x) → ZMod 2 := fun j =>
        if hj : j.val < 2 ^ (vars + vars ^ 2) then π₀ ⟨j.val, hj⟩ else default
      refine ⟨π₁, ?_⟩
      have hπ : ∀ i, π₁ (Fin.castLE hlen i) = π₀ i := by
        intro i
        simp [π₁]
      simp only [V, hlen, ↓reduceDIte]
      rw [PCP.simulateQ_padImpl_eq hlen (V₀ x) π₀ π₁ hπ]
      exact hπ₀
    · refine ⟨fun _ => default, ?_⟩
      simp [V, hlen]
  · intro hxNot π₁
    by_cases hlen : 2 ^ (vars + vars ^ 2) ≤ 2 ^ (QESAT.size (ZMod 2) vars x)
    · let π₀ : Fin (2 ^ (vars + vars ^ 2)) → ZMod 2 := fun i => π₁ (Fin.castLE hlen i)
      have hπ : ∀ i, π₁ (Fin.castLE hlen i) = π₀ i := by
        intro i
        rfl
      simp only [V, hlen, ↓reduceDIte]
      rw [PCP.simulateQ_padImpl_eq hlen (V₀ x) π₀ π₁ hπ]
      exact hSound hxNot π₀
    · exfalso
      exact hxNot (QESAT.mem_of_length_eq_zero x (QESAT.length_eq_zero_of_not_pow_le x hlen))

theorem QESAT_exp_PCP {vars : ℕ} : ∃ (q : ℕ) (r : Polynomial ℕ),
    QESAT (ZMod 2) vars ∈
      PCP (QESAT.size (ZMod 2) vars) 0 (1 / 2) (ZMod 2)
        (fun n => 2 ^ n) (fun _ => q) r.eval := by
  rcases QESAT_exp_PCP_before_repetition (vars := vars) with ⟨q₀, r₀, hBefore⟩
  rcases hBefore with ⟨V₀, t, hV₀⟩
  let V : PCPVerifier (List (CMvPolynomial vars (ZMod 2))) (QESAT.size (ZMod 2) vars)
      (ZMod 2) (fun n => 2 ^ n) := fun x => do
    let xs ← OracleComp.replicate 6 (V₀ x)
    pure (xs.all id)
  refine ⟨6 * q₀, Polynomial.C 6 * r₀, V, t, fun x => ?_⟩
  rcases hV₀ x with ⟨_, hQuery, hComplete, hSound⟩
  refine ⟨by simp [RunsInTime], ?_, ?_, ?_⟩
  · simpa [V, Polynomial.eval_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      queryBound_map (fun xs : List Bool => xs.all id) (queryBound_replicate 6 hQuery)
  · intro hxL
    rcases hComplete hxL with ⟨π, hπ⟩
    refine ⟨π, ?_⟩
    simp only [V, simulateQ_bind, simulateQ_pure]
    rw [simulateQ_replicate]
    simpa using repeated_accept_ge_one (n := 6) (by simpa using hπ)
  · intro hxNot π
    have hBase := hSound hxNot π
    simp only [V, simulateQ_bind, simulateQ_pure]
    rw [simulateQ_replicate]
    exact (repeated_accept_le (n := 6) hBase).trans seven_eighths_pow_six_le_half
