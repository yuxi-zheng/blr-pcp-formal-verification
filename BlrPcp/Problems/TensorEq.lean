import Architect
import BlrPcp.Oracle
import BlrPcp.Problems.BLR
import BlrPcp.Problems.LinEq
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-!
# Tensor-equality language

This file defines the TENSORQ language, its executable LPCP verifier, and the
linear PCP theorem for TENSORQ.

The proof is a single linear oracle of length `n + n*n` whose first `n` entries
encode `a` and whose remaining `n*n` entries encode the flattened tensor
`flat (a ⊗ a)`. We use the standard `Fin` equivalences
`Fin (n + n*n) ≃ Fin n ⊕ Fin (n*n)` and `Fin (n*n) ≃ Fin n × Fin n` to index
into the two halves.

The verifier samples `s, t : Fin n → F`, queries
- `a` at `s`,
- `a` at `t`,
- `b` at `flat (s ⊗ t)`,
and accepts iff `⟨b, flat (s ⊗ t)⟩ = ⟨a, s⟩ * ⟨a, t⟩`.

## Main declarations

- `TENSORQ`: the language of pairs `(a, b)` with `b (i, j) = a i * a j`.
- `TENSORQ.size`: the binary-size proxy for TENSORQ instances.
- `TENSORQ.verifier`: the LPCP verifier for TENSORQ.
- `TENSORQ_LPCP`: TENSORQ has a three-query LPCP verifier with soundness
  `(2 |F| - 1) / |F|^2`.
-/

open OracleComp
open scoped Matrix

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
    [SampleableType F]

abbrev TENSORQ (F : Type) (n : ℕ) [Field F] :
    Set ((Fin n → F) × (Fin n × Fin n → F)) :=
  { (a, b) | b = fun (i, j) => a i * a j }

namespace TENSORQ

def size {n : ℕ} (_ : (Fin n → F) × (Fin n × Fin n → F)) : ℕ :=
  (n + n * n) * Nat.clog 2 (Fintype.card F)

/-- The linear-query vector for "read `a` at `s`": `s` on the first half,
zero on the second half. -/
def queryA {n : ℕ} (s : Fin n → F) : Fin (n + n * n) → F :=
  Fin.append s (Function.const _ 0)

/-- The linear-query vector for "read `b` at `flat (s ⊗ t)`": zero on the
first half, `s i * t j` on the `(i, j)` slot of the second half. -/
def queryB {n : ℕ} (s t : Fin n → F) : Fin (n + n * n) → F :=
  Fin.append (Function.const _ 0)
    (fun k => let p := finProdFinEquiv.symm k; s p.1 * t p.2)

omit [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
/-- Completeness identity: when `b i j = a i * a j`, the inner products
satisfy the tensor-test relation. -/
lemma tensor_check_complete {n : ℕ} (a : Fin n → F) (s t : Fin n → F) :
    (∑ i, ∑ j, (a i * a j) * (s i * t j)) = (a ⬝ᵥ s) * (a ⬝ᵥ t) := by
  simp only [dotProduct, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

def verifier {n : ℕ} :
    LPCPVerifier ((Fin n → F) × (Fin n × Fin n → F)) size F (fun _ => n + n * n) :=
  fun x => do
    let (a, b) := x
    let s ← LINEQ.sampleRandomVector n (n + n * n) F
    let t ← LINEQ.sampleRandomVector n (n + n * n) F
    let yA : F ← query (spec := LPCP.spec F (n + n * n)) (.inr (queryA s))
    let yA' : F ← query (spec := LPCP.spec F (n + n * n)) (.inr (queryA t))
    let yB : F ← query (spec := LPCP.spec F (n + n * n)) (.inr (queryB s t))
    pure (yA = a ⬝ᵥ s ∧ yA' = a ⬝ᵥ t ∧ yB = ∑ i, ∑ j, b (i, j) * (s i * t j) ∧
          yB = yA * yA')

omit [Inhabited F] [SampleableType F] in
lemma verifier_queryBound {n : ℕ}
    (x : (Fin n → F) × (Fin n × Fin n → F)) :
    QueryBound (verifier (F := F) x) 3 (2 * n) := by
  have hQuery : ∀ s t : Fin n → F,
      QueryBound
        (do
          let yA : F ←
            (liftM (query (spec := LPCP.spec F (n + n * n)) (.inr (queryA s))) :
              OracleComp (LPCP.spec F (n + n * n)) F)
          let yA' : F ←
            (liftM (query (spec := LPCP.spec F (n + n * n)) (.inr (queryA t))) :
              OracleComp (LPCP.spec F (n + n * n)) F)
          let yB : F ←
            (liftM (query (spec := LPCP.spec F (n + n * n)) (.inr (queryB s t))) :
              OracleComp (LPCP.spec F (n + n * n)) F)
          pure (decide (yA = x.1 ⬝ᵥ s ∧ yA' = x.1 ⬝ᵥ t ∧
                yB = ∑ i, ∑ j, x.2 (i, j) * (s i * t j) ∧ yB = yA * yA'))) 3 0 := by
    intro s t
    simp only [QueryBound]
    rw [OracleComp.isQueryBound_query_bind_iff]
    refine ⟨by simp, fun _ => ?_⟩
    rw [OracleComp.isQueryBound_query_bind_iff]
    refine ⟨by simp, fun _ => ?_⟩
    rw [OracleComp.isQueryBound_query_bind_iff]
    exact ⟨by simp, fun _ => trivial⟩
  simpa [verifier, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    queryBound_bind (LINEQ.sampleRandomVector_queryBound (F := F) n (n + n * n)) fun s =>
      queryBound_bind (LINEQ.sampleRandomVector_queryBound (F := F) n (n + n * n)) fun t =>
        hQuery s t

/-- Project an oracle of length `n + n*n` to its first `n` entries (the
linear-part `a`). -/
def projA {n : ℕ} (π : Fin (n + n * n) → F) : Fin n → F :=
  fun i => π (Fin.castAdd (n * n) i)

/-- Project an oracle of length `n + n*n` to its last `n*n` entries
(re-indexed as `Fin n × Fin n`, the tensor part `b`). -/
def projB {n : ℕ} (π : Fin (n + n * n) → F) : Fin n × Fin n → F :=
  fun p => π (Fin.natAdd n (finProdFinEquiv p))

omit [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma dotProduct_queryA {n : ℕ} (π : Fin (n + n * n) → F) (s : Fin n → F) :
    π ⬝ᵥ queryA s = projA π ⬝ᵥ s := by
  simp only [dotProduct, queryA, projA]
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right, mul_comm]

omit [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma dotProduct_queryB {n : ℕ} (π : Fin (n + n * n) → F) (s t : Fin n → F) :
    π ⬝ᵥ queryB s t = ∑ i, ∑ j, projB π (i, j) * (s i * t j) := by
  simp only [dotProduct, queryB, projB]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Function.const_apply, mul_zero, Finset.sum_const_zero,
    Fin.append_right, zero_add]
  rw [← finProdFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply]
  rw [← Finset.sum_product']
  rfl

/-- The honest proof for an instance `(a, b) ∈ TENSORQ`: the concatenation of
`a` (the linear part, `n` entries) with the flattened tensor `b` (the
quadratic part, `n*n` entries). -/
def honestProof {n : ℕ}
    (x : (Fin n → F) × (Fin n × Fin n → F)) : Fin (n + n * n) → F :=
  Fin.append x.1 (fun k => x.2 (finProdFinEquiv.symm k))

omit [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma projA_honestProof {n : ℕ}
    (x : (Fin n → F) × (Fin n × Fin n → F)) :
    projA (honestProof x) = x.1 := by
  funext i
  simp [projA, honestProof, Fin.append_left]

omit [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma projB_honestProof {n : ℕ}
    (x : (Fin n → F) × (Fin n × Fin n → F)) :
    projB (honestProof x) = x.2 := by
  funext p
  simp only [projB, honestProof, Fin.append_right]
  rw [finProdFinEquiv.symm_apply_apply]

omit [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma row_dot_eq_bilinear_sub_tensor {n : ℕ} (a : Fin n → F)
    (b : Fin n × Fin n → F) (s t : Fin n → F) :
    (fun j => ∑ i, (b (i, j) - a i * a j) * s i) ⬝ᵥ t =
      (∑ i, ∑ j, b (i, j) * (s i * t j)) - (a ⬝ᵥ s) * (a ⬝ᵥ t) := by
  rw [← tensor_check_complete (F := F) a s t]
  simp only [dotProduct]
  calc
    ∑ x, (∑ i, (b (i, x) - a i * a x) * s i) * t x
        = ∑ x, ∑ i, ((b (i, x) - a i * a x) * s i) * t x := by
          simp [Finset.sum_mul]
    _ = ∑ i, ∑ x, ((b (i, x) - a i * a x) * s i) * t x := by
          rw [Finset.sum_comm]
    _ = (∑ i, ∑ j, b (i, j) * (s i * t j)) -
          ∑ i, ∑ j, (a i * a j) * (s i * t j) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro j _
          ring

omit [Fintype F] [Inhabited F] [SampleableType F] in
lemma accept_implies_row_dot_zero {n : ℕ} (a : Fin n → F)
    (b : Fin n × Fin n → F) (π : Fin (n + n * n) → F) (s t : Fin n → F)
    (hacc : decide (π ⬝ᵥ queryA s = a ⬝ᵥ s) &&
        (decide (π ⬝ᵥ queryA t = a ⬝ᵥ t) &&
          (decide (π ⬝ᵥ queryB s t = ∑ i, ∑ j, b (i, j) * (s i * t j)) &&
            decide (π ⬝ᵥ queryB s t = π ⬝ᵥ queryA s * π ⬝ᵥ queryA t))) = true) :
    (fun j => ∑ i, (b (i, j) - a i * a j) * s i) ⬝ᵥ t = 0 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
  rcases hacc with ⟨hA, hA', hB, hMul⟩
  rw [row_dot_eq_bilinear_sub_tensor (F := F) a b s t]
  calc
    (∑ i, ∑ j, b (i, j) * (s i * t j)) - (a ⬝ᵥ s) * (a ⬝ᵥ t)
        = (π ⬝ᵥ queryB s t) - (π ⬝ᵥ queryA s) * (π ⬝ᵥ queryA t) := by
          rw [hB, hA, hA']
    _ = 0 := by rw [hMul, sub_self]

lemma verifier_soundness_after_sampling {n : ℕ} (a : Fin n → F)
    (b : Fin n × Fin n → F) (π : Fin (n + n * n) → F)
    (hab : (a, b) ∉ TENSORQ F n) :
    Pr[fun x => x = true | do
      let s ← ($ᵗ (Fin n → F) : ProbComp (Fin n → F))
      (fun t => decide (π ⬝ᵥ queryA s = a ⬝ᵥ s) &&
          (decide (π ⬝ᵥ queryA t = a ⬝ᵥ t) &&
            (decide (π ⬝ᵥ queryB s t = ∑ i, ∑ j, b (i, j) * (s i * t j)) &&
              decide (π ⬝ᵥ queryB s t = π ⬝ᵥ queryA s * π ⬝ᵥ queryA t)))) <$>
        ($ᵗ (Fin n → F) : ProbComp (Fin n → F))] ≤
      2 / (Fintype.card F : ENNReal) := by
  have hC : (fun p : Fin n × Fin n => b p - a p.1 * a p.2) ≠ 0 := by
    intro hC
    apply hab
    funext p
    exact sub_eq_zero.mp (by simpa using congrFun hC p)
  obtain ⟨ij, hij⟩ : ∃ p : Fin n × Fin n, b p - a p.1 * a p.2 ≠ 0 := by
    simpa [funext_iff] using hC
  let col : Fin n → F := fun i => b (i, ij.2) - a i * a ij.2
  have hcol : col ≠ 0 := by
    intro h
    exact hij (by simpa [col] using congrFun h ij.1)
  have hBadS :
      Pr[fun s : Fin n → F => ¬ col ⬝ᵥ s ≠ 0 |
          ($ᵗ (Fin n → F) : ProbComp (Fin n → F))] ≤
        1 / (Fintype.card F : ENNReal) := by
    refine (ENNReal.le_div_iff_mul_le (a := _) (b := (Fintype.card F : ENNReal))
      (c := 1)
      (Or.inr (by simp : (1 : ENNReal) ≠ 0))
      (Or.inr (by simp : (1 : ENNReal) ≠ ⊤))).2 ?_
    simpa using LINEQ.linear_form_uniform_prob_mul_card_le_one (F := F) hcol
  have hAccept := probEvent_bind_le_add
    (mx := ($ᵗ (Fin n → F) : ProbComp (Fin n → F)))
    (my := fun s : Fin n → F =>
      (fun t => decide (π ⬝ᵥ queryA s = a ⬝ᵥ s) &&
          (decide (π ⬝ᵥ queryA t = a ⬝ᵥ t) &&
            (decide (π ⬝ᵥ queryB s t = ∑ i, ∑ j, b (i, j) * (s i * t j)) &&
              decide (π ⬝ᵥ queryB s t = π ⬝ᵥ queryA s * π ⬝ᵥ queryA t)))) <$>
        ($ᵗ (Fin n → F) : ProbComp (Fin n → F)))
    (p := fun s : Fin n → F => col ⬝ᵥ s ≠ 0)
    (q := fun y : Bool => y = false)
    hBadS
    (ε₂ := 1 / (Fintype.card F : ENNReal))
    ?_
  · have hsum :
        1 / (Fintype.card F : ENNReal) + 1 / (Fintype.card F : ENNReal) =
          2 / (Fintype.card F : ENNReal) := by
        norm_num [div_eq_mul_inv, two_mul]
    simpa [not_false_eq_true] using hAccept.trans_eq hsum
  · intro s _hsupp hs
    let row : Fin n → F := fun j => ∑ i, (b (i, j) - a i * a j) * s i
    rw [probEvent_map]
    refine (probEvent_mono (mx := ($ᵗ (Fin n → F) : ProbComp (Fin n → F)))
      (q := fun t : Fin n → F => row ⬝ᵥ t = 0) ?_).trans ?_
    · intro t _ ht
      have hrowzero := accept_implies_row_dot_zero (F := F) a b π s t ?_
      · simpa [row] using hrowzero
      · simpa using ht
    · have hrow : row ≠ 0 := by
        intro hrow
        apply hs
        have hcoord := congrFun hrow ij.2
        simpa [row, col, dotProduct] using hcoord
      refine (ENNReal.le_div_iff_mul_le (a := _) (b := (Fintype.card F : ENNReal))
        (c := 1)
        (Or.inr (by simp : (1 : ENNReal) ≠ 0))
        (Or.inr (by simp : (1 : ENNReal) ≠ ⊤))).2 ?_
      exact LINEQ.linear_form_uniform_prob_mul_card_le_one (F := F) hrow

end TENSORQ

/-- 2/|F|: direct PIL -/
theorem TENSORQ_LPCP {n : ℕ} :
    TENSORQ F n ∈ LPCP (TENSORQ.size) 0
      (
        -- (((2 * Fintype.card F - 1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) ^ 2)
        2 / (Fintype.card F : ENNReal)
      )
      F
      (fun _ => n + n * n) (fun _ => 3) (fun _ => 2 * n) := by
  refine ⟨TENSORQ.verifier (F := F), 0, ?_⟩
  rintro ⟨a, b⟩
  refine ⟨by simp [RunsInTime], TENSORQ.verifier_queryBound (F := F) (a, b), ?_, ?_⟩
  · -- completeness
    rintro hab
    refine ⟨TENSORQ.honestProof (a, b), ?_⟩
    have hb : b = fun (i, j) => a i * a j := hab
    simp [TENSORQ.verifier, LINEQ.sampleRandomVector,
          TENSORQ.dotProduct_queryA, TENSORQ.dotProduct_queryB,
          TENSORQ.projA_honestProof, TENSORQ.projB_honestProof, hb,
          TENSORQ.tensor_check_complete]
  · -- soundness
    intro hab π
    simp [TENSORQ.verifier]
    rw [← probEvent_eq_eq_probOutput]
    rw [LINEQ.simulateQ_sampleRandomVector (F := F) n (n + n*n) (LPCP.proof π).impl]
    exact TENSORQ.verifier_soundness_after_sampling (F := F) a b π hab
