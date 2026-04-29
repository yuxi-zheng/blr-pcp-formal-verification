import BlrPcp.Oracle
import BlrPcp.Bridge

/-!
# BLR linearity test

The BLR test, defined as an oracle computation.
-/

open OracleComp

namespace BLR

abbrev spec (F : Type) (n : ℕ) : OracleSpec (Unit ⊕ (Fin n → F)) :=
  randSpec F + (LPCP.proofSpec F n)

/-- Sample a vector in `F^n` using `n` calls to the field-valued randomness oracle. -/
def sampleVector (F : Type) (n : ℕ) : OracleComp (spec F n) (Fin n → F) :=
  Fin.mOfFn n fun _ =>
    (liftM (query (spec := spec F n) (.inl ())) : OracleComp (spec F n) F)

/-- The basic version of the BLR test (is sound only for fields of prime cardinality)-/
def verifier1 {F : Type} [Field F] [DecidableEq F] {n : ℕ} :
    OracleComp (spec F n) Bool := do
  let x ← sampleVector F n
  let y ← sampleVector F n
  let fx : F ← query (spec := spec F n) (.inr x)
  let fy : F ← query (spec := spec F n) (.inr y)
  let fxy : F ← query (spec := spec F n) (.inr (x + y))
  return decide (fx + fy = fxy)

end BLR

lemma BLR.sampleVector_queryBoundAux (F : Type) (m n : ℕ) :
    QueryBound
      (Fin.mOfFn m fun _ =>
        (liftM (query (spec := BLR.spec F n) (.inl ())) :
          OracleComp (BLR.spec F n) F)) 0 m := by
  induction m with
  | zero =>
      simp [Fin.mOfFn, QueryBound]
  | succ m ih =>
      simp only [Fin.mOfFn]
      have hHead :
          QueryBound
            ((liftM (query (spec := BLR.spec F n) (.inl ())) :
              OracleComp (BLR.spec F n) F)) 0 1 := by
        simp [QueryBound]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        queryBound_bind hHead fun _ => by
          simpa [QueryBound] using ih

lemma BLR.sampleVector_queryBound (F : Type) (n : ℕ) :
    QueryBound (BLR.sampleVector F n) 0 n := by
  simpa [BLR.sampleVector] using BLR.sampleVector_queryBoundAux F n n

/-- `BLR.verifier1` makes three queries to `f` and uses two random vectors in `F^n`. -/
theorem BLR_query_complexity1 {F : Type} [Field F] [DecidableEq F] {n : ℕ} :
    QueryBound (BLR.verifier1 (F := F) (n := n)) 3 (2 * n) := by
  have hProof : ∀ x y : Fin n → F,
      QueryBound
        (do
          let fx : F ←
            (liftM (query (spec := BLR.spec F n) (.inr x)) :
              OracleComp (BLR.spec F n) F)
          let fy : F ←
            (liftM (query (spec := BLR.spec F n) (.inr y)) :
              OracleComp (BLR.spec F n) F)
          let fxy : F ←
            (liftM (query (spec := BLR.spec F n) (.inr (x + y))) :
              OracleComp (BLR.spec F n) F)
          return decide (fx + fy = fxy)) 3 0 := by
    intro x y
    simp only [QueryBound]
    rw [OracleComp.isQueryBound_query_bind_iff]
    refine ⟨by simp, fun _ => ?_⟩
    rw [OracleComp.isQueryBound_query_bind_iff]
    refine ⟨by simp, fun _ => ?_⟩
    rw [OracleComp.isQueryBound_query_bind_iff]
    exact ⟨by simp, fun _ => trivial⟩
  simp only [BLR.verifier1]
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    queryBound_bind (BLR.sampleVector_queryBound F n) fun x =>
      queryBound_bind (BLR.sampleVector_queryBound F n) fun y =>
        hProof x y

/-- If `F` has prime cardinality, then the basic BLR test (without sampling a,b ∈ 𝔽ˣ)
has same rejection probability on `f` as `rejectionProbabilityBLR f`. -/
theorem blrSoundnessCompEqAnalytical1 {F : Type} {n : ℕ}
    [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
    (hF : Nat.Prime (Fintype.card F)) (f : (Fin n → F) → F) :
    Pr[= false | simulateQ ((rand F).impl + fun x => (return f x : ProbComp F))
      (BLR.verifier1 (F := F) (n := n))] =
      rejectionProbabilityBLR f := by
  sorry

/-- Soundness of `BLR.verifier1` for finite fields of prime cardinality. -/
theorem BLR_soundness1 {F : Type} {n : ℕ}
    [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
    (hF : Nat.Prime (Fintype.card F)) (f : (Fin n → F) → F) :
    Pr[= false | simulateQ ((rand F).impl + fun x => (return f x : ProbComp F))
      (BLR.verifier1 (F := F) (n := n))] ≥ distanceToLin f := by
  sorry
