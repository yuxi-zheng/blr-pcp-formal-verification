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
    sorry
