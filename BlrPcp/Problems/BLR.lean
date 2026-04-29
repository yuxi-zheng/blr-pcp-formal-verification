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

lemma probOutput_finCons_map_eq {m : Type _ → Type _} [Monad m] [LawfulMonad m]
    [HasEvalSPMF m] {F : Type} [DecidableEq F] {n : ℕ}
    (mx : m (Fin n → F)) (x : Fin (n + 1) → F) :
    Pr[= x | (Fin.cons (x 0)) <$> mx] = Pr[= Fin.tail x | mx] := by
  rw [show x = Fin.cons (x 0) (Fin.tail x) from (Fin.cons_self_tail x).symm]
  exact probOutput_map_injective mx
    (Fin.cons_right_injective (α := fun _ => F) (x 0)) (Fin.tail x)

lemma probOutput_finCons_map_ne {m : Type _ → Type _} [Monad m] [LawfulMonad m]
    [HasEvalSPMF m] {F : Type} [DecidableEq F] [Fintype F] {n : ℕ}
    (mx : m (Fin n → F)) (x : Fin (n + 1) → F) {a : F}
    (ha : a ≠ x 0) :
    Pr[= x | (Fin.cons a) <$> mx] = 0 := by
  rw [probOutput_map_eq_sum_fintype_ite]
  have hfalse : ∀ y : Fin n → F, x ≠ Fin.cons a y := by
    intro y hxy
    apply ha
    simpa using (congrFun hxy 0).symm
  simp [hfalse]

lemma probOutput_simulateQ_BLR_sampleVectorAux {F : Type}
    [Nonempty F] [DecidableEq F] [Fintype F] [SampleableType F]
    (m n : ℕ) (impl : QueryImpl ((Fin n → F) →ₒ F) ProbComp)
    (x : Fin m → F) :
    Pr[= x |
      simulateQ ((rand F).impl + impl)
        (Fin.mOfFn m fun _ =>
          (liftM (query (spec := BLR.spec F n) (.inl ())) :
            OracleComp (BLR.spec F n) F))] =
      (Fintype.card (Fin m → F) : ENNReal)⁻¹ := by
  induction m with
  | zero =>
      have hx : x = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      subst hx
      simp [Fin.mOfFn]
  | succ m ih =>
      simp only [Fin.mOfFn, simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        id_map, OracleQuery.input_query]
      rw [probOutput_bind_eq_tsum, tsum_fintype]
      rw [Finset.sum_eq_single (x 0)]
      · change Pr[= x 0 | ($ᵗ F : ProbComp F)] *
            Pr[= x |
              (Fin.cons (x 0)) <$>
                simulateQ ((rand F).impl + impl)
                  (Fin.mOfFn m fun _ =>
                    (liftM (query (spec := BLR.spec F n) (.inl ())) :
                      OracleComp (BLR.spec F n) F))] = _
        rw [probOutput_uniformSample, probOutput_finCons_map_eq, ih]
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin]
        rw [Nat.pow_succ]
        simp only [Nat.cast_mul, Nat.cast_pow]
        rw [ENNReal.mul_inv]
        · rw [mul_comm]
        · left
          exact_mod_cast pow_ne_zero m (Fintype.card_ne_zero (α := F))
        · left
          simp
      · intro a _ ha
        change Pr[= a | ($ᵗ F : ProbComp F)] *
            Pr[= x |
              (Fin.cons a) <$>
                simulateQ ((rand F).impl + impl)
                  (Fin.mOfFn m fun _ =>
                    (liftM (query (spec := BLR.spec F n) (.inl ())) :
                      OracleComp (BLR.spec F n) F))] = 0
        rw [probOutput_finCons_map_ne _ x ha]
        simp
      · intro h
        simp at h

@[simp]
lemma probOutput_simulateQ_BLR_sampleVector {F : Type}
    [Nonempty F] [DecidableEq F] [Fintype F] [SampleableType F] {n : ℕ}
    (impl : QueryImpl ((Fin n → F) →ₒ F) ProbComp) (x : Fin n → F) :
    Pr[= x | simulateQ (((fun _ : Unit => $ᵗ F) + impl)) (BLR.sampleVector F n)] =
      (Fintype.card (Fin n → F) : ENNReal)⁻¹ := by
  simpa [rand, BLR.sampleVector] using
    probOutput_simulateQ_BLR_sampleVectorAux (F := F) n n impl x

lemma probOutput_true_map_simulateQ_BLR_sampleVector {F : Type}
    [Nonempty F] [DecidableEq F] [Fintype F] [SampleableType F] {n : ℕ}
    (impl : QueryImpl ((Fin n → F) →ₒ F) ProbComp)
    (g : (Fin n → F) → Bool) :
    Pr[= true | g <$> simulateQ (((fun _ : Unit => $ᵗ F) + impl)) (BLR.sampleVector F n)] =
      ∑ y : Fin n → F,
        (Fintype.card (Fin n → F) : ENNReal)⁻¹ * if g y = true then 1 else 0 := by
  rw [probOutput_map_eq_sum_fintype_ite]
  apply Finset.sum_congr rfl
  intro y _
  rw [probOutput_simulateQ_BLR_sampleVector (impl := impl) y]
  by_cases hy : g y = true <;> simp [hy]

lemma blrVerifier_acceptanceProbability {F : Type} {n : ℕ}
    [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
    (f : (Fin n → F) → F) :
    Pr[= true | simulateQ ((rand F).impl + fun x => (return f x : ProbComp F))
      (BLR.verifier1 (F := F) (n := n))] = acceptanceProbabilityBLR f := by
  simp only [BLR.verifier1, simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
    id_map, OracleQuery.input_query]
  rw [probOutput_bind_eq_tsum, tsum_fintype]
  have hProofQuery : ∀ q : Fin n → F,
      (((fun _ : Unit => ($ᵗ F : ProbComp F)) +
          (fun x : Fin n → F => (pure (f x) : ProbComp F))) (Sum.inr q)) =
        (pure (f q) : ProbComp F) := by
    intro q
    rfl
  simp_rw [hProofQuery]
  simp [probOutput_true_map_simulateQ_BLR_sampleVector, acceptanceProbabilityBLR,
    BLRAcceptsAt, mul_assoc, mul_comm]

/-- The basic BLR test has the same rejection probability on `f` as
`rejectionProbabilityBLR f`. -/
theorem blrSoundnessCompEqAnalytical1 {F : Type} {n : ℕ}
    [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
    (f : (Fin n → F) → F) :
    Pr[= false | simulateQ ((rand F).impl + fun x => (return f x : ProbComp F))
      (BLR.verifier1 (F := F) (n := n))] =
      rejectionProbabilityBLR f := by
  rw [probOutput_false_eq_sub]
  simp [blrVerifier_acceptanceProbability (F := F) (n := n) f, rejectionProbabilityBLR]

/-- Soundness of `BLR.verifier1` for finite fields of prime cardinality. -/
theorem BLR_soundness1 {F : Type} {n : ℕ}
    [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
    (hF : Nat.Prime (Fintype.card F)) (f : (Fin n → F) → F) :
    distanceToLin f ≤ 2 *
      Pr[= false | simulateQ ((rand F).impl + fun x => (return f x : ProbComp F))
        (BLR.verifier1 (F := F) (n := n))] := by
  rw [blrSoundnessCompEqAnalytical1 f]
  exact blrSoundnessAnalytical hF f
