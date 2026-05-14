import Architect
import BlrPcp.Oracle
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

open OracleComp OracleUtil
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
    let s ← OracleUtil.sampleVector ((liftM (query (spec := fullSpec_fin_vector F (n + n * n)) (.inl ())) : OracleComp (fullSpec_fin_vector F (n + n * n)) F)) n
    let t ← OracleUtil.sampleVector ((liftM (query (spec := fullSpec_fin_vector F (n + n * n)) (.inl ())) : OracleComp (fullSpec_fin_vector F (n + n * n)) F)) n
    let yA : F ← query (spec := fullSpec_fin_vector F (n + n * n)) (.inr (queryA s))
    let yA' : F ← query (spec := fullSpec_fin_vector F (n + n * n)) (.inr (queryA t))
    let yB : F ← query (spec := fullSpec_fin_vector F (n + n * n)) (.inr (queryB s t))
    pure (yA = a ⬝ᵥ s ∧ yA' = a ⬝ᵥ t ∧ yB = ∑ i, ∑ j, b (i, j) * (s i * t j) ∧
          yB = yA * yA')

omit [Inhabited F] [SampleableType F] in
lemma verifier_queryBound {n : ℕ}
    (x : (Fin n → F) × (Fin n × Fin n → F)) :
    QueryBound (verifier (F := F) x) (2 * n) 3 := by
  have hQuery : ∀ s t : Fin n → F,
      QueryBound
        (do
          let yA : F ←
            (liftM (query (spec := fullSpec_fin_vector F (n + n * n)) (.inr (queryA s))) :
              OracleComp (fullSpec_fin_vector F (n + n * n)) F)
          let yA' : F ←
            (liftM (query (spec := fullSpec_fin_vector F (n + n * n)) (.inr (queryA t))) :
              OracleComp (fullSpec_fin_vector F (n + n * n)) F)
          let yB : F ←
            (liftM (query (spec := fullSpec_fin_vector F (n + n * n)) (.inr (queryB s t))) :
              OracleComp (fullSpec_fin_vector F (n + n * n)) F)
          pure (decide (yA = x.1 ⬝ᵥ s ∧ yA' = x.1 ⬝ᵥ t ∧
                yB = ∑ i, ∑ j, x.2 (i, j) * (s i * t j) ∧ yB = yA * yA'))) 0 3 := by
    intro s t
    simp only [QueryBound]
    rw [OracleComp.isQueryBound_query_bind_iff]
    refine ⟨by simp, fun _ => ?_⟩
    rw [OracleComp.isQueryBound_query_bind_iff]
    refine ⟨by simp, fun _ => ?_⟩
    rw [OracleComp.isQueryBound_query_bind_iff]
    exact ⟨by simp, fun _ => trivial⟩
  simpa [verifier, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    queryBound_bind (OracleUtil.sampleVector_queryBound n (n + n * n) (F := F)) fun s =>
      queryBound_bind (OracleUtil.sampleVector_queryBound n (n + n * n) (F := F)) fun t =>
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

/-- 2/|F|: direct PIL --/
lemma verifier_soundness_after_sampling_weak {n : ℕ} (a : Fin n → F)
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

/-- 2/|F| - 1/|F|^2: apply PIL twice --/
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
      (2 * ↑(Fintype.card F) - 1) / ↑(Fintype.card F) ^ 2:= by
  have hC : (fun p : Fin n × Fin n => b p - a p.1 * a p.2) ≠ 0 := by
    intro hC
    apply hab
    funext p
    exact sub_eq_zero.mp (by simpa using congrFun hC p)
  obtain ⟨ij_star, hij_star⟩ : ∃ p : Fin n × Fin n, b p - a p.1 * a p.2 ≠ 0 := by
    simpa [funext_iff] using hC
  /- The index where a[i] * a[j] != b[i,j]-/
  let i_star : Fin n := ij_star.1
  let j_star : Fin n := ij_star.2
  let col : Fin n → F := fun i => b (i, j_star) - a i * a j_star
  let row : Fin n → F := fun j => b (i_star, j) - a i_star * a j
  have hcol : col ≠ 0 := by
    intro h
    exact hij_star (by simpa [col] using congrFun h i_star)
  have hrow : row ≠ 0 := by
    intro h
    exact hij_star (by simpa [col] using congrFun h j_star)

  /- For each \(i \in [n]\) define the linear polynomial \(p_i(t) := \sum_{j \in [n]} (b_{ij} - a_i a_j)\, t_j\).
  Here p_poly maps each i to p_i and p_i maps t to p_i(t) =  -/
  let p_poly: Fin n → ((Fin n → F) → F):= fun i => fun t => ∑ j, (b (i, j) - a i * a j) * t j
  have h_first_pil :
    Pr[fun t : Fin n → F => p_poly i_star t = 0 |
          ($ᵗ (Fin n → F) : ProbComp (Fin n → F))] ≤
        1 / (Fintype.card F : ENNReal) := by
    refine (ENNReal.le_div_iff_mul_le (a := _) (b := (Fintype.card F : ENNReal))
      (c := 1)
      (Or.inr (by simp : (1 : ENNReal) ≠ 0))
      (Or.inr (by simp : (1 : ENNReal) ≠ ⊤))).2 ?_
    simpa using LINEQ.linear_form_uniform_prob_mul_card_le_one (F := F) hrow

  --  ∑ i, (p_poly i t) * s i = 0
  let p_poly_t_to_i : (Fin n → F) → (Fin n → F):= fun t => (fun i => (p_poly i t))
  have h_second_pil :
    ∀ t: Fin n → F, p_poly i_star t ≠ 0 →
    Pr[fun s : Fin n → F => (p_poly_t_to_i t) ⬝ᵥ s = 0  |
          ($ᵗ (Fin n → F) : ProbComp (Fin n → F))] ≤
        1 / (Fintype.card F : ENNReal) := by
    intro t h_p_poly_neq
    refine (ENNReal.le_div_iff_mul_le (a := _) (b := (Fintype.card F : ENNReal))
      (c := 1)
      (Or.inr (by simp : (1 : ENNReal) ≠ 0))
      (Or.inr (by simp : (1 : ENNReal) ≠ ⊤))).2 ?_
    have h_p_poly_t_neq: (p_poly_t_to_i t) ≠ 0 := by
      simp [p_poly_t_to_i]
      intro h
      exact h_p_poly_neq (congr_fun h i_star)
    simpa using LINEQ.linear_form_uniform_prob_mul_card_le_one (F := F) h_p_poly_t_neq


  have h_first_pil_good : Pr[fun t => p_poly i_star t ≠ 0 | $ᵗ(Fin n → F)] ≥ 1 - 1 / ↑(Fintype.card F) :=
    probEvent_ge_of_compl_le (by simp) (by simpa using h_first_pil)

  have h_second_pil_good : ∀ t, p_poly i_star t ≠ 0 →
      Pr[fun s => p_poly_t_to_i t ⬝ᵥ s ≠ 0 | $ᵗ(Fin n → F)] ≥ 1 - 1 / ↑(Fintype.card F) := by
    intro t ht
    exact probEvent_ge_of_compl_le (by simp) (by simpa using h_second_pil t ht)

  have h_main_inq:
    Pr[fun (t, s) => p_poly_t_to_i t ⬝ᵥ s ≠ 0 | do
        let t ← $ᵗ(Fin n → F)
        let s ← $ᵗ(Fin n → F)
        return (t, s)
      ] ≥ (1 - 1 / ↑(Fintype.card F)) ^ 2 := by
    rw [sq]
    refine mul_le_probEvent_bind (p := fun t => p_poly i_star t ≠ 0)
      h_first_pil_good ?_
    intro t _ ht
    have hgood := h_second_pil_good t ht
    have heq :
        Pr[fun (x : (Fin n → F) × (Fin n → F)) => p_poly_t_to_i x.1 ⬝ᵥ x.2 ≠ 0 |
            ($ᵗ(Fin n → F) >>= fun s => (pure (t, s) : ProbComp _))] =
          Pr[fun s => p_poly_t_to_i t ⬝ᵥ s ≠ 0 | $ᵗ(Fin n → F)] := by
      rw [show (fun s : Fin n → F => (pure (t, s) : ProbComp _)) =
            pure ∘ (fun s : Fin n → F => (t, s)) from rfl,
          probEvent_bind_pure_comp]
      rfl
    exact heq ▸ hgood

  -- Step 1: bound LHS by Pr over `do let s; let t; pure (t, s)` of dot = 0.
  have hLHS_le :
      Pr[fun x => x = true | do
          let s ← ($ᵗ (Fin n → F) : ProbComp (Fin n → F))
          (fun t => decide (π ⬝ᵥ queryA s = a ⬝ᵥ s) &&
              (decide (π ⬝ᵥ queryA t = a ⬝ᵥ t) &&
                (decide (π ⬝ᵥ queryB s t = ∑ i, ∑ j, b (i, j) * (s i * t j)) &&
                  decide (π ⬝ᵥ queryB s t = π ⬝ᵥ queryA s * π ⬝ᵥ queryA t)))) <$>
            ($ᵗ (Fin n → F) : ProbComp (Fin n → F))] ≤
      Pr[fun p : (Fin n → F) × (Fin n → F) => p_poly_t_to_i p.1 ⬝ᵥ p.2 = 0 | do
          let s ← ($ᵗ (Fin n → F) : ProbComp (Fin n → F))
          let t ← ($ᵗ (Fin n → F) : ProbComp (Fin n → F))
          pure (t, s)] := by
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine ENNReal.tsum_le_tsum fun s => ?_
    refine mul_le_mul' le_rfl ?_
    rw [probEvent_map]
    rw [show (fun t : Fin n → F => (pure ((t, s) : (Fin n → F) × (Fin n → F)) : ProbComp _)) =
          pure ∘ (fun t : Fin n → F => ((t, s) : (Fin n → F) × (Fin n → F))) from rfl]
    rw [probEvent_bind_pure_comp]
    refine probEvent_mono ?_
    intro t _ ht
    have hacc : decide (π ⬝ᵥ queryA s = a ⬝ᵥ s) &&
        (decide (π ⬝ᵥ queryA t = a ⬝ᵥ t) &&
          (decide (π ⬝ᵥ queryB s t = ∑ i, ∑ j, b (i, j) * (s i * t j)) &&
            decide (π ⬝ᵥ queryB s t = π ⬝ᵥ queryA s * π ⬝ᵥ queryA t))) = true := by
      simpa [Function.comp] using ht
    have hrowzero := accept_implies_row_dot_zero (F := F) a b π s t hacc
    show p_poly_t_to_i t ⬝ᵥ s = 0
    have hsum :
        p_poly_t_to_i t ⬝ᵥ s =
          (fun j => ∑ i, (b (i, j) - a i * a j) * s i) ⬝ᵥ t := by
      simp only [p_poly_t_to_i, p_poly, dotProduct]
      rw [show (∑ x, (∑ j, (b (x, j) - a x * a j) * t j) * s x) =
            ∑ x, ∑ j, (b (x, j) - a x * a j) * t j * s x from
          Finset.sum_congr rfl (fun x _ => Finset.sum_mul _ _ _)]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hsum]; exact hrowzero
  -- Step 2: swap order of independent draws to match `h_main_inq`.
  have hswap :
      Pr[fun p : (Fin n → F) × (Fin n → F) => p_poly_t_to_i p.1 ⬝ᵥ p.2 = 0 | do
          let s ← ($ᵗ (Fin n → F) : ProbComp (Fin n → F))
          let t ← ($ᵗ (Fin n → F) : ProbComp (Fin n → F))
          pure (t, s)] =
      Pr[fun p : (Fin n → F) × (Fin n → F) => p_poly_t_to_i p.1 ⬝ᵥ p.2 = 0 | do
          let t ← ($ᵗ (Fin n → F) : ProbComp (Fin n → F))
          let s ← ($ᵗ (Fin n → F) : ProbComp (Fin n → F))
          pure (t, s)] :=
    probEvent_bind_bind_swap _ _ (fun s t => pure (t, s)) _
  -- Step 3: bound by complement of `h_main_inq`.
  have hfail :
      Pr[⊥ | do
          let t ← ($ᵗ (Fin n → F) : ProbComp (Fin n → F))
          let s ← ($ᵗ (Fin n → F) : ProbComp (Fin n → F))
          pure ((t, s) : (Fin n → F) × (Fin n → F))] = 0 := by simp
  have h_quad_le_one : (1 - 1 / (Fintype.card F : ENNReal))^2 ≤ 1 :=
    pow_le_one' tsub_le_self 2
  have h_main_inq' :
      Pr[fun p : (Fin n → F) × (Fin n → F) => p_poly_t_to_i p.1 ⬝ᵥ p.2 ≠ 0 | do
          let t ← ($ᵗ (Fin n → F) : ProbComp (Fin n → F))
          let s ← ($ᵗ (Fin n → F) : ProbComp (Fin n → F))
          pure (t, s)] ≥ 1 - (1 - (1 - 1 / (Fintype.card F : ENNReal))^2) := by
    rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top h_quad_le_one]
    exact h_main_inq
  have hcompl_raw := probEvent_compl_le_of_ge hfail h_main_inq'
  have hpred_eq :
      (fun p : (Fin n → F) × (Fin n → F) => p_poly_t_to_i p.1 ⬝ᵥ p.2 = 0) =
        (fun p : (Fin n → F) × (Fin n → F) => ¬ p_poly_t_to_i p.1 ⬝ᵥ p.2 ≠ 0) := by
    funext p; simp
  have hcompl :
      Pr[fun p : (Fin n → F) × (Fin n → F) => p_poly_t_to_i p.1 ⬝ᵥ p.2 = 0 | do
          let t ← ($ᵗ (Fin n → F) : ProbComp (Fin n → F))
          let s ← ($ᵗ (Fin n → F) : ProbComp (Fin n → F))
          pure (t, s)] ≤ 1 - (1 - 1 / (Fintype.card F : ENNReal))^2 := by
    rw [hpred_eq]; exact hcompl_raw
  refine (hLHS_le.trans (hswap.le.trans hcompl)).trans ?_
  -- Step 4: ENNReal arithmetic 1 - (1 - 1/k)^2 = (2k - 1)/k^2 when k = Fintype.card F ≥ 1.
  set q : ENNReal := (Fintype.card F : ENNReal) with hq_def
  have hq_pos : (0 : ENNReal) < q := by
    rw [hq_def]; exact_mod_cast Fintype.card_pos
  have hq_ne_top : q ≠ ⊤ := by rw [hq_def]; exact ENNReal.natCast_ne_top _
  have hq_ge_one : (1 : ENNReal) ≤ q := by
    rw [hq_def]; exact_mod_cast (Fintype.card_pos : 1 ≤ Fintype.card F)
  have h_inv_le_one : 1 / q ≤ 1 := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl hq_pos.ne') (Or.inl hq_ne_top)]
    simpa using hq_ge_one
  have hq2_ne_zero : q^2 ≠ 0 := pow_ne_zero _ hq_pos.ne'
  have hq2_ne_top : q^2 ≠ ⊤ := ENNReal.pow_ne_top hq_ne_top
  have hone_sub_inv : 1 - 1 / q = (q - 1) / q := by
    rw [ENNReal.sub_div (fun _ _ => hq_pos.ne'), ENNReal.div_self hq_pos.ne' hq_ne_top]
  have hdiv_pow : ((q - 1) / q)^2 = (q - 1)^2 / q^2 := by
    rw [ENNReal.div_eq_inv_mul, mul_pow, ← ENNReal.inv_pow, ← ENNReal.div_eq_inv_mul]
  rw [hone_sub_inv, hdiv_pow]
  have hqm1_le_q : q - 1 ≤ q := tsub_le_self
  have hqm1_ne_top : q - 1 ≠ ⊤ := ne_top_of_le_ne_top hq_ne_top hqm1_le_q
  have hqm1_sq_le_qsq : (q - 1)^2 ≤ q^2 := pow_le_pow_left' hqm1_le_q 2
  have hqm1_sq_ne_top : (q - 1)^2 ≠ ⊤ := ENNReal.pow_ne_top hqm1_ne_top
  have hstep1 : (1 : ENNReal) - (q - 1)^2 / q^2 = (q^2 - (q - 1)^2) / q^2 := by
    rw [ENNReal.sub_div (fun _ _ => hq2_ne_zero), ENNReal.div_self hq2_ne_zero hq2_ne_top]
  rw [hstep1]
  -- Reduce to numerator: q^2 - (q-1)^2 = 2*q - 1.
  have h_two_q_le : (1 : ENNReal) ≤ 2 * q := le_trans hq_ge_one (by
    nth_rewrite 1 [show (2 * q : ENNReal) = q + q from by ring]
    simp)
  have h2qm1_ne_top : 2 * q - 1 ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) hq_ne_top) tsub_le_self
  have hadd : (q - 1)^2 + (2 * q - 1) = q^2 := by
    -- Lift to ℕ via Fintype.card.
    have hk : 1 ≤ Fintype.card F := Fintype.card_pos
    have hqm1_eq : q - 1 = ((Fintype.card F - 1 : ℕ) : ENNReal) := by
      rw [hq_def, show (1 : ENNReal) = ((1 : ℕ) : ENNReal) from by simp, ← ENNReal.natCast_sub]
    have h2qm1_eq : 2 * q - 1 = ((2 * Fintype.card F - 1 : ℕ) : ENNReal) := by
      rw [hq_def, show (1 : ENNReal) = ((1 : ℕ) : ENNReal) from by simp,
          show (2 * (Fintype.card F : ENNReal)) = ((2 * Fintype.card F : ℕ) : ENNReal) from by
            push_cast; ring,
          ← ENNReal.natCast_sub]
    have hqsq_eq : q^2 = ((Fintype.card F ^ 2 : ℕ) : ENNReal) := by
      rw [hq_def]; push_cast; ring
    rw [hqm1_eq, h2qm1_eq, hqsq_eq, ← Nat.cast_pow, ← Nat.cast_add]
    congr 1
    have : (Fintype.card F - 1) ^ 2 + (2 * Fintype.card F - 1) = Fintype.card F ^ 2 := by
      have hk' : 1 ≤ Fintype.card F := hk
      noncomm_ring
      simp
      have h2 : 1 ≤ 2 * Fintype.card F := by omega
      zify [hk', h2]
      ring
    exact this
  have heq_num : q^2 - (q - 1)^2 = 2 * q - 1 := by
    have := hadd
    -- (q-1)^2 + (2q-1) = q^2 → q^2 - (q-1)^2 = 2q-1.
    rw [← this, ENNReal.add_sub_cancel_left hqm1_sq_ne_top]
  rw [heq_num]

end TENSORQ

theorem TENSORQ_LPCP_weak {n : ℕ} :
    TENSORQ F n ∈ LPCP (TENSORQ.size) 0 (2 / (Fintype.card F : ENNReal)) F
      (fun _ => n + n * n) (fun _ => 3) (fun _ => 2 * n) := by
  refine ⟨TENSORQ.verifier (F := F), 0, ?_⟩
  rintro ⟨a, b⟩
  refine ⟨by simp [RunsInTime], TENSORQ.verifier_queryBound (F := F) (a, b), ?_, ?_⟩
  · -- completeness
    rintro hab
    refine ⟨TENSORQ.honestProof (a, b), ?_⟩
    have hb : b = fun (i, j) => a i * a j := hab
    simp [TENSORQ.verifier, OracleUtil.sampleVector,
          TENSORQ.dotProduct_queryA, TENSORQ.dotProduct_queryB,
          TENSORQ.projA_honestProof, TENSORQ.projB_honestProof, hb,
          TENSORQ.tensor_check_complete]
  · -- soundness
    intro hab π
    simp [TENSORQ.verifier]
    rw [← probEvent_eq_eq_probOutput]
    rw [OracleUtil.simulateQ_sampleVector (F := F) n (n + n*n) (LPCP.proofOracle π).impl]
    exact TENSORQ.verifier_soundness_after_sampling_weak (F := F) a b π hab


theorem TENSORQ_LPCP {n : ℕ} :
    TENSORQ F n ∈ LPCP (TENSORQ.size) 0 (((2 * Fintype.card F - 1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) ^ 2) F
      (fun _ => n + n * n) (fun _ => 3) (fun _ => 2 * n) := by
    refine ⟨TENSORQ.verifier (F := F), 0, ?_⟩
    rintro ⟨a, b⟩
    refine ⟨by simp [RunsInTime], TENSORQ.verifier_queryBound (F := F) (a, b), ?_, ?_⟩
    · -- completeness
      rintro hab
      refine ⟨TENSORQ.honestProof (a, b), ?_⟩
      have hb : b = fun (i, j) => a i * a j := hab
      simp [TENSORQ.verifier, OracleUtil.sampleVector,
            TENSORQ.dotProduct_queryA, TENSORQ.dotProduct_queryB,
            TENSORQ.projA_honestProof, TENSORQ.projB_honestProof, hb,
            TENSORQ.tensor_check_complete]
    . -- soundness
      intro hab π
      simp [TENSORQ.verifier]
      rw [← probEvent_eq_eq_probOutput]
      rw [OracleUtil.simulateQ_sampleVector (F := F) n (n + n*n) (LPCP.proofOracle π).impl]
      exact TENSORQ.verifier_soundness_after_sampling (F := F) a b π hab

theorem TENSORQ_LPCP_Zmod2 {n : ℕ} :
    TENSORQ (ZMod 2) n ∈ LPCP (TENSORQ.size) 0 (3 / 4) (ZMod 2)
      (fun _ => n + n^2) (fun _ => 3) (fun _ => 2 * n) := by
  have h := TENSORQ_LPCP (F := ZMod 2) (n := n)
  have hcard : (Fintype.card (ZMod 2) : ℕ) = 2 := ZMod.card 2
  have hbound :
      ((2 * Fintype.card (ZMod 2) - 1 : ℕ) : ENNReal)
        / (Fintype.card (ZMod 2) : ENNReal) ^ 2 = 3 / 4 := by
    rw [hcard]; norm_num
  rw [hbound] at h
  simpa [sq] using h
