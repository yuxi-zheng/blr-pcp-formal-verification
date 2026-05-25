import BlrPcp.QESATExpSizePCP.PCPs
import BlrPcp.FnFiniteFIelds.BLR

/-!
# BLR linearity test with finite-function oracle access

The finite-field BLR verifier as an oracle computation, plus the additive
`ZMod 2` verifier used by the LPCP-to-PCP construction.

## Main declarations

- `distanceToLin`: the `ENNReal` version of analytical distance to linearity.
- `BLR.basicSampleVector`: samples a vector using the standard field-valued randomness oracle.
- `BLR.basicVerifier`: the additive BLR linearity test, which makes three queries
  to the proof oracle and uses two random vectors, but no scalar randomness.
- `BLR_basic_query_complexity`: query complexity of `BLR.basicVerifier`.
- `BLR_soundness`: finite-field BLR soundness as an acceptance-probability upper bound.
- `BLR_completeness`: finite-field BLR completeness.
- `BLR_basic_soundness_ZMod2`: soundness of `BLR.basicVerifier` over `ZMod 2`.
- `BLR_basic_completeness_ZMod2`: completeness of `BLR.basicVerifier` over `ZMod 2`.
-/

open OracleComp

/-! ## Bridge from analytical BLR to oracle probabilities -/

/-- The `ENNReal` version of the analytical distance from `f` to linearity. -/
noncomputable def distanceToLin {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    [Nonempty (Fin n)] (f : (Fin n → F) → F) : ENNReal :=
  ENNReal.ofReal (BlrPcp.distanceToLinear (F := F) (Idx := Fin n) f)

/-- The `ENNReal` version of the analytical finite-field BLR acceptance probability. -/
private noncomputable def acceptanceProbabilityBLR {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} [Nonempty (Fin n)] (f : (Fin n → F) → F) : ENNReal :=
  ENNReal.ofReal (BlrPcp.acceptanceProbabilityBLR (F := F) (Idx := Fin n) f)

/-- The real-valued distance to linearity is nonnegative. -/
private lemma distanceToLinear_nonneg {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} [Nonempty (Fin n)] (f : (Fin n → F) → F) :
    0 ≤ BlrPcp.distanceToLinear (F := F) (Idx := Fin n) f := by
  classical
  rw [BlrPcp.distanceToLinear_eq_inf_linearFn]
  apply Finset.le_inf'
  intro α _
  unfold BlrPcp.distance
  positivity

/-- The analytical finite-field BLR soundness theorem, converted to `ENNReal`
and stated in terms of acceptance probability. -/
private theorem blrSoundnessAnalytical {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    [Nonempty (Fin n)] (f : (Fin n → F) → F) :
    acceptanceProbabilityBLR f ≤ 1 - distanceToLin f := by
  classical
  have hDistNonneg := distanceToLinear_nonneg (F := F) (n := n) f
  have hReal := BlrPcp.blr_soundness (F := F) (Idx := Fin n) f
  rw [acceptanceProbabilityBLR, distanceToLin]
  rw [← ENNReal.ofReal_one]
  rw [← ENNReal.ofReal_sub (1 : ℝ) hDistNonneg]
  exact ENNReal.ofReal_le_ofReal hReal

namespace BLR

/-! ### Finite-Field BLR Verifier -/

/-- Randomness used by the finite-field BLR verifier. -/
private inductive Rand (F : Type) where
  | field
  | unit

/-- BLR randomness is either a field element or a nonzero scalar. -/
private def randRange (F : Type) [Field F] : Rand F → Type
  | .field => F
  | .unit => Fˣ

/-- Oracle specification for finite-field BLR randomness. -/
private abbrev normalRandOracleSpec (F : Type) [Field F] : OracleSpec (Rand F) :=
  OracleSpec.ofFn (randRange F)

/-- Combined randomness and proof-oracle specification for the finite-field BLR verifier. -/
private abbrev fullSpec (F : Type) [Field F] (n : ℕ) : OracleSpec (Rand F ⊕ (Fin n → F)) :=
  normalRandOracleSpec F + proofOracleSpec_fin_vector F n

/-- The BLR randomness implementation: field samples for vector coordinates,
and unit samples for the scalar coefficients. -/
private abbrev normalRandOracle (F : Type) [Field F] [SampleableType F] [SampleableType Fˣ] :
    OracleContext (Rand F) ProbComp where
  spec := normalRandOracleSpec F
  impl
    | .field => $ᵗ F
    | .unit => $ᵗ Fˣ

/-- Sample one scalar. -/
private def sampleScalar {F : Type} [Field F] {n : ℕ} : OracleComp (fullSpec F n) F :=
  query (spec := fullSpec F n) (.inl .field)

/-- Sample one nonzero scalar. -/
private def sampleUnit {F : Type} [Field F] {n : ℕ} : OracleComp (fullSpec F n) Fˣ :=
  query (spec := fullSpec F n) (.inl .unit)

/-- Sample a vector in `F^n` using `n` calls to the field-valued randomness oracle. -/
private def sampleVector (F : Type) [Field F] (n : ℕ) : OracleComp (fullSpec F n) (Fin n → F) :=
  OracleUtil.sampleVector (sampleScalar (F := F) (n := n)) n

/-- The finite-field BLR verifier. -/
private def verifier {F : Type} [Field F] [DecidableEq F] {n : ℕ} :
    OracleComp (fullSpec F n) Bool := do
  let x : Fin n → F ← sampleVector F n
  let y : Fin n → F ← sampleVector F n
  let a : Fˣ ← sampleUnit (F := F)
  let b : Fˣ ← sampleUnit (F := F)
  let fx : F ← query (spec := fullSpec F n) (.inr x)
  let fy : F ← query (spec := fullSpec F n) (.inr y)
  let fxy : F ← query (spec := fullSpec F n) (.inr fun i => (a : F) * x i + (b : F) * y i)
  return decide ((a : F) * fx + (b : F) * fy = fxy)

/-! ### Additive BLR Verifier -/

/-- Sample a vector in `F^n` using the standard randomness oracle. -/
def basicSampleVector (F : Type) (n : ℕ) : OracleComp (LPCP.fullSpec F n) (Fin n → F) :=
  OracleUtil.sampleRandomVector F n n

/-- The additive BLR verifier, using only the standard field-valued randomness oracle. -/
def basicVerifier {F : Type} [Add F] [DecidableEq F] {n : ℕ} :
    OracleComp (LPCP.fullSpec F n) Bool := do
  let x : Fin n → F ← basicSampleVector F n
  let y : Fin n → F ← basicSampleVector F n
  let fx : F ← query (spec := LPCP.fullSpec F n) (.inr x)
  let fy : F ← query (spec := LPCP.fullSpec F n) (.inr y)
  let fxy : F ← query (spec := LPCP.fullSpec F n) (.inr fun i => x i + y i)
  return decide (fx + fy = fxy)

/-- Sampling one scalar makes one randomness query and no proof queries. -/
private lemma sampleScalar_queryBound {F : Type} [Field F] {n : ℕ} :
    QueryBound (sampleScalar (F := F) (n := n)) 1 0 := by
  simp [sampleScalar, QueryBound]

/-- Sampling a finite-field BLR vector makes `n` randomness queries and no proof queries. -/
private lemma sampleVector_queryBound (F : Type) [Field F] (n : ℕ) :
    QueryBound (sampleVector F n) n 0 :=
  OracleUtil.sampleVector_queryBound' (sampleScalar_queryBound (F := F) (n := n)) n

/-- Sampling one nonzero scalar makes one randomness query and no proof queries. -/
private lemma sampleUnit_queryBound {F : Type} [Field F] {n : ℕ} :
    QueryBound (sampleUnit (F := F) (n := n)) 1 0 := by
  simp [sampleUnit, QueryBound]

/-- `BLR.basicSampleVector` uses `n` randomness queries and no proof queries. -/
private lemma basicSampleVector_queryBound (F : Type) (n : ℕ) :
    QueryBound (basicSampleVector F n) n 0 := by
  simpa [basicSampleVector] using
    (OracleUtil.sampleRandomVector_queryBound (F := F) n n)

end BLR

/-! ## Query Complexity -/

/-- `BLR.verifier` makes three queries to `f` and uses two random vectors and two scalars. -/
theorem BLR_query_complexity {F : Type} [Field F] [DecidableEq F] {n : ℕ} :
    QueryBound (BLR.verifier (F := F) (n := n)) (2 * n + 2) 3 := by
  have hProof : ∀ (x y : Fin n → F) (a b : Fˣ),
      QueryBound
        (do
          let fx : F ←
            (liftM (query (spec := BLR.fullSpec F n) (.inr x)) :
              OracleComp (BLR.fullSpec F n) F)
          let fy : F ←
            (liftM (query (spec := BLR.fullSpec F n) (.inr y)) :
              OracleComp (BLR.fullSpec F n) F)
          let fxy : F ←
            (liftM
              (query (spec := BLR.fullSpec F n) (.inr fun i => (a : F) * x i + (b : F) * y i)) :
              OracleComp (BLR.fullSpec F n) F)
          return decide ((a : F) * fx + (b : F) * fy = fxy)) 0 3 := by
    intro x y a b
    simp only [QueryBound]
    rw [OracleComp.isQueryBound_query_bind_iff]
    refine ⟨by simp, fun _ => ?_⟩
    rw [OracleComp.isQueryBound_query_bind_iff]
    refine ⟨by simp, fun _ => ?_⟩
    rw [OracleComp.isQueryBound_query_bind_iff]
    exact ⟨by simp, fun _ => trivial⟩
  simp only [BLR.verifier]
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    queryBound_bind (BLR.sampleVector_queryBound F n) fun x =>
      queryBound_bind (BLR.sampleVector_queryBound F n) fun y =>
        queryBound_bind (BLR.sampleUnit_queryBound (F := F) (n := n)) fun a =>
          queryBound_bind (BLR.sampleUnit_queryBound (F := F) (n := n)) fun b =>
            hProof x y a b

/-- `BLR.basicVerifier` makes three queries to `f` and uses two random vectors. -/
theorem BLR_basic_query_complexity {F : Type} [Add F] [DecidableEq F] {n : ℕ} :
    QueryBound (BLR.basicVerifier (F := F) (n := n)) (2 * n) 3:= by
  have hProof : ∀ x y : Fin n → F,
      QueryBound
        (do
          let fx : F ←
            (liftM (query (spec := LPCP.fullSpec F n) (.inr x)) :
              OracleComp (LPCP.fullSpec F n) F)
          let fy : F ←
            (liftM (query (spec := LPCP.fullSpec F n) (.inr y)) :
              OracleComp (LPCP.fullSpec F n) F)
          let fxy : F ←
            (liftM (query (spec := LPCP.fullSpec F n) (.inr fun i => x i + y i)) :
              OracleComp (LPCP.fullSpec F n) F)
          return decide (fx + fy = fxy)) 0 3 := by
    intro x y
    simp only [QueryBound]
    rw [OracleComp.isQueryBound_query_bind_iff]
    refine ⟨by simp, fun _ => ?_⟩
    rw [OracleComp.isQueryBound_query_bind_iff]
    refine ⟨by simp, fun _ => ?_⟩
    rw [OracleComp.isQueryBound_query_bind_iff]
    exact ⟨by simp, fun _ => trivial⟩
  simp only [BLR.basicVerifier]
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    queryBound_bind (BLR.basicSampleVector_queryBound F n) fun x =>
      queryBound_bind (BLR.basicSampleVector_queryBound F n) fun y =>
        hProof x y

/-! ## Oracle Probability Expansions -/

/-- Simulating one finite-field BLR scalar sample gives the uniform distribution on `F`. -/
private lemma simulateQ_BLR_sampleScalar {F : Type} [Field F] [Fintype F] [SampleableType F]
    [SampleableType Fˣ] {n : ℕ}
    (impl : QueryImpl (proofOracleSpec_fin_vector F n) ProbComp) :
    simulateQ ((BLR.normalRandOracle F).impl + impl) (BLR.sampleScalar (F := F) (n := n)) =
      $ᵗ F := by
  simp [BLR.sampleScalar, BLR.normalRandOracle]

/-- Simulating a finite-field BLR vector sample gives the uniform distribution on `F^n`. -/
private lemma simulateQ_BLR_sampleVector {F : Type} [Field F] [DecidableEq F] [Fintype F]
    [SampleableType F] [SampleableType Fˣ] {n : ℕ}
    (impl : QueryImpl (proofOracleSpec_fin_vector F n) ProbComp) :
    simulateQ ((BLR.normalRandOracle F).impl + impl) (BLR.sampleVector F n) =
      $ᵗ (Fin n → F) :=
  OracleUtil.simulateQ_sampleVector' _ (simulateQ_BLR_sampleScalar impl) n

/-- Point probability for a simulated finite-field BLR vector sample. -/
@[simp]
private lemma probOutput_simulateQ_BLR_sampleVector {F : Type}
    [Field F] [DecidableEq F] [Fintype F] [SampleableType F] [SampleableType Fˣ]
    {n : ℕ}
    (impl : QueryImpl (proofOracleSpec_fin_vector F n) ProbComp) (x : Fin n → F) :
    Pr[= x | simulateQ ((BLR.normalRandOracle F).impl + impl) (BLR.sampleVector F n)] =
      (Fintype.card (Fin n → F) : ENNReal)⁻¹ := by
  rw [simulateQ_BLR_sampleVector impl]
  exact probOutput_uniformSample (α := Fin n → F) x

/-- Point probability for a simulated additive BLR vector sample. -/
@[simp]
private lemma probOutput_simulateQ_BLR_basicSampleVector {F : Type}
    [Nonempty F] [DecidableEq F] [Fintype F] [SampleableType F] {n : ℕ}
    (impl : QueryImpl (proofOracleSpec_fin_vector F n) ProbComp) (x : Fin n → F) :
    Pr[= x | simulateQ ((randOracle F).impl + impl) (BLR.basicSampleVector F n)] =
      (Fintype.card (Fin n → F) : ENNReal)⁻¹ := by
  rw [show
      simulateQ ((randOracle F).impl + impl) (BLR.basicSampleVector F n) =
        ($ᵗ (Fin n → F) : ProbComp (Fin n → F)) by
    simpa [BLR.basicSampleVector] using
      (OracleUtil.simulateQ_sampleRandomVector (F := F) n n impl)]
  exact probOutput_uniformSample (α := Fin n → F) x

/-- Point probability for a simulated nonzero scalar sample. -/
@[simp]
private lemma probOutput_simulateQ_BLR_sampleUnit {F : Type}
    [Field F] [Fintype Fˣ] [SampleableType F] [SampleableType Fˣ] {n : ℕ}
    (impl : QueryImpl (proofOracleSpec_fin_vector F n) ProbComp) (a : Fˣ) :
    Pr[= a | simulateQ ((BLR.normalRandOracle F).impl + impl) (BLR.sampleUnit (F := F) (n := n))] =
      (Fintype.card Fˣ : ENNReal)⁻¹ := by
  simp [BLR.sampleUnit, BLR.normalRandOracle, probOutput_uniformSample]

/-- Replace the classical-decider `if` used by `ofReal` conversion with the ambient `if`. -/
private lemma ite_classical_eq {α : Type} [Zero α] [One α] {p : Prop} [Decidable p] :
    @ite α p (Classical.propDecidable p) 1 0 = if p then 1 else 0 := by
  by_cases hp : p <;> simp [hp]

/-- Rewrite a sum over units as a sum over the nonzero field elements. -/
private lemma sum_units_eq_sum_nonzero {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (G : F → ENNReal) :
    (∑ a : Fˣ, G a) = ∑ a ∈ BlrPcp.nonzeroF (F := F), G a := by
  calc
    (∑ a : Fˣ, G a) =
        ∑ a : {a : F // a ≠ 0}, G a := by
          exact Fintype.sum_equiv unitsEquivNeZero _ _ fun _ => rfl
    _ = ∑ a ∈ BlrPcp.nonzeroF (F := F), G a := by
          simpa [BlrPcp.nonzeroF] using
            (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
              (f := G) (p := fun a : F => a ≠ 0))

/-- The number of units equals the number of nonzero field elements. -/
private lemma card_units_eq_card_nonzeroF {F : Type}
    [Field F] [Fintype F] [DecidableEq F] :
    (Fintype.card Fˣ : ENNReal) = ((BlrPcp.nonzeroF (F := F)).card : ENNReal) := by
  have h : Fintype.card Fˣ = (BlrPcp.nonzeroF (F := F)).card := by
    rw [Fintype.card_congr unitsEquivNeZero]
    exact Fintype.card_of_subtype (p := fun a : F => a ≠ 0)
      (BlrPcp.nonzeroF (F := F)) (by
        intro a
        simp [BlrPcp.nonzeroF])
  exact_mod_cast h

/-- Rewrite the nested unit sums in the BLR acceptance expansion over nonzero elements. -/
private lemma sum_units_nested_eq_nonzero {F V : Type}
    [Field F] [Fintype F] [DecidableEq F] [Fintype V]
    (c : ENNReal) (I : F → F → V → V → ENNReal) :
    (∑ x : V,
      c * ∑ y : V,
        c * ∑ a : Fˣ,
          (Fintype.card Fˣ : ENNReal)⁻¹ * ∑ b : Fˣ,
            (Fintype.card Fˣ : ENNReal)⁻¹ * I a b x y) =
      ∑ x : V,
        c * ∑ y : V,
          c * ∑ a ∈ BlrPcp.nonzeroF (F := F),
            ((BlrPcp.nonzeroF (F := F)).card : ENNReal)⁻¹ *
              ∑ b ∈ BlrPcp.nonzeroF (F := F),
                ((BlrPcp.nonzeroF (F := F)).card : ENNReal)⁻¹ * I a b x y := by
  rw [card_units_eq_card_nonzeroF (F := F)]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  rw [sum_units_eq_sum_nonzero (F := F)
    (G := fun a =>
      ((BlrPcp.nonzeroF (F := F)).card : ENNReal)⁻¹ *
        ∑ b : Fˣ,
          ((BlrPcp.nonzeroF (F := F)).card : ENNReal)⁻¹ * I a b x y)]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [sum_units_eq_sum_nonzero (F := F)
    (G := fun b =>
      ((BlrPcp.nonzeroF (F := F)).card : ENNReal)⁻¹ * I a b x y)]

/-- Pull uniform normalization factors outside the expanded BLR acceptance sum. -/
private lemma blrAcceptance_sum_normalize {F V : Type}
    [Fintype F] [Fintype V] [DecidableEq F]
    (s : Finset F) (c d : ENNReal) (I : F → F → V → V → ENNReal) :
    (∑ x : V,
      c * ∑ y : V,
        c * ∑ a ∈ s,
          d * ∑ b ∈ s,
            d * I a b x y) =
      d * d * c * c * ∑ a ∈ s, ∑ b ∈ s, ∑ x : V, ∑ y : V, I a b x y := by
  classical
  calc
    (∑ x : V,
      c * ∑ y : V,
        c * ∑ a ∈ s,
          d * ∑ b ∈ s,
            d * I a b x y) =
        ∑ x : V, ∑ y : V, ∑ a ∈ s, ∑ b ∈ s,
          c * (c * (d * (d * I a b x y))) := by
          simp only [Finset.mul_sum]
    _ = ∑ x : V, ∑ a ∈ s, ∑ y : V, ∑ b ∈ s,
          c * (c * (d * (d * I a b x y))) := by
          apply Finset.sum_congr rfl
          intro x _
          simpa using
            (Finset.sum_comm (s := (Finset.univ : Finset V)) (t := s)
              (f := fun y a => ∑ b ∈ s, c * (c * (d * (d * I a b x y)))))
    _ = ∑ a ∈ s, ∑ x : V, ∑ y : V, ∑ b ∈ s,
          c * (c * (d * (d * I a b x y))) := by
          simpa using
            (Finset.sum_comm (s := (Finset.univ : Finset V)) (t := s)
              (f := fun x a => ∑ y : V, ∑ b ∈ s, c * (c * (d * (d * I a b x y)))))
    _ = ∑ a ∈ s, ∑ x : V, ∑ b ∈ s, ∑ y : V,
          c * (c * (d * (d * I a b x y))) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro x _
          simpa using
            (Finset.sum_comm (s := (Finset.univ : Finset V)) (t := s)
              (f := fun y b => c * (c * (d * (d * I a b x y)))))
    _ = ∑ a ∈ s, ∑ b ∈ s, ∑ x : V, ∑ y : V,
          c * (c * (d * (d * I a b x y))) := by
          apply Finset.sum_congr rfl
          intro a _
          simpa using
            (Finset.sum_comm (s := (Finset.univ : Finset V)) (t := s)
              (f := fun x b => ∑ y : V, c * (c * (d * (d * I a b x y)))))
    _ = d * d * c * c * ∑ a ∈ s, ∑ b ∈ s, ∑ x : V, ∑ y : V, I a b x y := by
          symm
          simp only [Finset.mul_sum]
          simp only [mul_comm, mul_left_comm]

/-- Convert the real BLR acceptance count to an `ENNReal` sum. -/
private lemma ofReal_BLR_acceptance_sum {F : Type} {n : ℕ}
    [Field F] [DecidableEq F] [Fintype F] [Nonempty (Fin n)]
    (f : (Fin n → F) → F)
    [∀ a b x y, Decidable (BlrPcp.BLRAcceptsAt (F := F) (Idx := Fin n) f a b x y)] :
    ENNReal.ofReal
      (∑ a ∈ BlrPcp.nonzeroF (F := F),
        ∑ b ∈ BlrPcp.nonzeroF (F := F),
          ∑ x : Fin n → F, ∑ y : Fin n → F,
            if BlrPcp.BLRAcceptsAt (F := F) (Idx := Fin n) f a b x y
            then (1 : Real) else 0) =
      ∑ a ∈ BlrPcp.nonzeroF (F := F),
        ∑ b ∈ BlrPcp.nonzeroF (F := F),
          ∑ x : Fin n → F, ∑ y : Fin n → F,
            if BlrPcp.BLRAcceptsAt (F := F) (Idx := Fin n) f a b x y
            then (1 : ENNReal) else 0 := by
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro a _
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro b _
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro x _
        rw [ENNReal.ofReal_sum_of_nonneg]
        · apply Finset.sum_congr rfl
          intro y _
          by_cases h : BlrPcp.BLRAcceptsAt (F := F) (Idx := Fin n) f a b x y <;> simp [h]
        · intro y _
          by_cases h : BlrPcp.BLRAcceptsAt (F := F) (Idx := Fin n) f a b x y <;> simp [h]
      · intro x _
        positivity
    · intro b _
      positivity
  · intro a _
    positivity

/-- Expand analytical BLR acceptance probability as a normalized `ENNReal` sum. -/
private lemma acceptanceProbabilityBLR_eq_sum {F : Type} {n : ℕ}
    [Field F] [DecidableEq F] [Fintype F] [Nonempty (Fin n)]
    (f : (Fin n → F) → F)
    [∀ a b x y, Decidable (BlrPcp.BLRAcceptsAt (F := F) (Idx := Fin n) f a b x y)] :
    acceptanceProbabilityBLR f =
      ((BlrPcp.nonzeroF (F := F)).card : ENNReal)⁻¹ *
        ((BlrPcp.nonzeroF (F := F)).card : ENNReal)⁻¹ *
          (Fintype.card (Fin n → F) : ENNReal)⁻¹ *
            (Fintype.card (Fin n → F) : ENNReal)⁻¹ *
              ∑ a ∈ BlrPcp.nonzeroF (F := F),
                ∑ b ∈ BlrPcp.nonzeroF (F := F),
                  ∑ x : Fin n → F, ∑ y : Fin n → F,
                    if BlrPcp.BLRAcceptsAt (F := F) (Idx := Fin n) f a b x y
                    then (1 : ENNReal) else 0 := by
  have hnz_nonempty : (BlrPcp.nonzeroF (F := F)).Nonempty := by
    exact ⟨1, by simp [BlrPcp.nonzeroF]⟩
  have hnz_pos : 0 < ((BlrPcp.nonzeroF (F := F)).card : Real) := by
    exact_mod_cast hnz_nonempty.card_pos
  have hvec_pos : 0 < (Fintype.card (Fin n → F) : Real) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨0⟩
  rw [acceptanceProbabilityBLR, BlrPcp.acceptanceProbabilityBLR]
  simp only [ite_classical_eq]
  symm
  simp only [BlrPcp.Vec]
  rw [ENNReal.ofReal_mul]
  · rw [ENNReal.ofReal_mul]
    · rw [ENNReal.ofReal_mul]
      · rw [ENNReal.ofReal_mul]
        · symm
          have hsum := ofReal_BLR_acceptance_sum (F := F) (n := n) f
          simpa only [ENNReal.ofReal_inv_of_pos hnz_pos, ENNReal.ofReal_inv_of_pos hvec_pos,
            ENNReal.ofReal_natCast] using congrArg
              (fun z =>
                ENNReal.ofReal (((BlrPcp.nonzeroF (F := F)).card : Real)⁻¹) *
                  ENNReal.ofReal (((BlrPcp.nonzeroF (F := F)).card : Real)⁻¹) *
                    ENNReal.ofReal ((Fintype.card (Fin n → F) : Real)⁻¹) *
                      ENNReal.ofReal ((Fintype.card (Fin n → F) : Real)⁻¹) * z)
              hsum
        · positivity
      · positivity
    · positivity
  · positivity

/-- Expand the finite-field BLR oracle verifier acceptance probability over units. -/
private lemma blrVerifier_acceptanceProbability_units {F : Type} {n : ℕ}
    [Field F] [DecidableEq F] [Fintype F]
    [SampleableType F] [SampleableType Fˣ]
    (f : (Fin n → F) → F) :
    Pr[= true | simulateQ ((BLR.normalRandOracle F).impl + fun x => (return f x : ProbComp F))
      (BLR.verifier (F := F) (n := n))] =
      ∑ x : Fin n → F,
        (Fintype.card (Fin n → F) : ENNReal)⁻¹ *
          ∑ y : Fin n → F,
            (Fintype.card (Fin n → F) : ENNReal)⁻¹ *
              ∑ a : Fˣ,
                (Fintype.card Fˣ : ENNReal)⁻¹ *
                  ∑ b : Fˣ,
                    (Fintype.card Fˣ : ENNReal)⁻¹ *
                      if (a : F) * f x + (b : F) * f y =
                          f (fun i => (a : F) * x i + (b : F) * y i)
                      then 1 else 0 := by
  simp only [BLR.verifier, simulateQ_bind, simulateQ_query, simulateQ_pure,
    OracleQuery.cont_query, id_map, OracleQuery.input_query]
  simp only [probOutput_bind_eq_tsum, tsum_fintype]
  simp_rw [probOutput_simulateQ_BLR_sampleVector
    (impl := fun x => (return f x : ProbComp F))]
  simp_rw [probOutput_simulateQ_BLR_sampleUnit
    (impl := fun x => (return f x : ProbComp F))]
  dsimp [HAdd.hAdd, QueryImpl.add]
  simp only [probOutput_pure, ite_mul, zero_mul, one_mul, tsum_ite_eq]
  simp

/-- The additive BLR verifier accepts with the uniform probability over `x,y ∈ F^n`. -/
private theorem blrBasicVerifier_acceptanceProbability_sum {F : Type} {n : ℕ}
    [Add F] [DecidableEq F] [Fintype F] [Nonempty F] [SampleableType F]
    (f : (Fin n → F) → F) :
    Pr[= true | simulateQ ((randOracle F).impl + fun x => (return f x : ProbComp F))
      (BLR.basicVerifier (F := F) (n := n))] =
      ∑ x : Fin n → F,
        (Fintype.card (Fin n → F) : ENNReal)⁻¹ *
          ∑ y : Fin n → F,
            (Fintype.card (Fin n → F) : ENNReal)⁻¹ *
              if f x + f y = f (fun i => x i + y i) then 1 else 0 := by
  simp only [BLR.basicVerifier, simulateQ_bind, simulateQ_query, simulateQ_pure,
    OracleQuery.cont_query, id_map, OracleQuery.input_query]
  simp only [probOutput_bind_eq_tsum, tsum_fintype]
  simp_rw [probOutput_simulateQ_BLR_basicSampleVector
    (impl := fun x => (return f x : ProbComp F))]
  dsimp [HAdd.hAdd, QueryImpl.add]
  simp only [probOutput_pure, ite_mul, zero_mul, one_mul]
  simp

/-! ## Finite-Field BLR Guarantees -/

/-- The oracle BLR verifier has the analytical finite-field BLR acceptance probability. -/
private theorem blrVerifier_acceptanceProbability {F : Type} {n : ℕ}
    [Field F] [DecidableEq F] [Fintype F] [Nonempty (Fin n)]
    [SampleableType F] [SampleableType Fˣ]
    (f : (Fin n → F) → F) :
    Pr[= true | simulateQ ((BLR.normalRandOracle F).impl + fun x => (return f x : ProbComp F))
      (BLR.verifier (F := F) (n := n))] = acceptanceProbabilityBLR f := by
  classical
  rw [blrVerifier_acceptanceProbability_units (F := F) (n := n) f]
  rw [acceptanceProbabilityBLR_eq_sum (F := F) (n := n) f]
  simp only [BlrPcp.BLRAcceptsAt, ite_classical_eq]
  rw [sum_units_nested_eq_nonzero (F := F) (V := Fin n → F)
    (c := (Fintype.card (Fin n → F) : ENNReal)⁻¹)
    (I := fun a b x y =>
      if a * f x + b * f y = f (fun i => a * x i + b * y i)
      then (1 : ENNReal) else 0)]
  rw [blrAcceptance_sum_normalize]

/-- Soundness of `BLR.verifier` for finite fields as an acceptance-probability upper bound. -/
theorem BLR_soundness {F : Type} {n : ℕ}
    [Field F] [DecidableEq F] [Fintype F] [Nonempty (Fin n)]
    [SampleableType F] [SampleableType Fˣ]
    (f : (Fin n → F) → F) :
    Pr[= true | simulateQ ((BLR.normalRandOracle F).impl + fun x => (return f x : ProbComp F))
      (BLR.verifier (F := F) (n := n))] ≤ 1 - distanceToLin f := by
  rw [blrVerifier_acceptanceProbability]
  exact blrSoundnessAnalytical f

/-- Completeness of `BLR.verifier`: linear functions are accepted with probability one. -/
theorem BLR_completeness {F : Type} {n : ℕ}
    [Field F] [DecidableEq F] [Fintype F] [Nonempty (Fin n)]
    [SampleableType F] [SampleableType Fˣ]
    {f : (Fin n → F) → F}
    (hf : f ∈ BlrPcp.LinearSet (F := F) (Idx := Fin n)) :
    Pr[= true | simulateQ ((BLR.normalRandOracle F).impl + fun x => (return f x : ProbComp F))
      (BLR.verifier (F := F) (n := n))] = 1 := by
  rw [blrVerifier_acceptanceProbability]
  simp [acceptanceProbabilityBLR, BlrPcp.blr_completeness (F := F) (Idx := Fin n) hf]

/-! ## `ZMod 2` Transfer to the Additive Verifier -/

/-- Every unit of `ZMod 2` coerces to `1`. -/
private lemma zmod2_unit_coe (a : (ZMod 2)ˣ) : (a : ZMod 2) = 1 := by
  have hne : (a : ZMod 2).val ≠ 0 := by
    simp [Units.ne_zero a]
  have hlt : (a : ZMod 2).val < 2 := ZMod.val_lt _
  have hval : (a : ZMod 2).val = 1 := by omega
  exact (ZMod.val_eq_one (by norm_num) _).mp hval

/-- The unit group of `ZMod 2` is trivial. -/
private instance : Unique (ZMod 2)ˣ where
  default := 1
  uniq a := Units.ext (zmod2_unit_coe a)

/-- Over `ZMod 2`, the additive BLR verifier has the same acceptance probability
as the scalar-sampling finite-field BLR verifier, because every nonzero scalar is `1`. -/
private theorem blrBasicVerifier_acceptanceProbability_eq_verifier_ZMod2 {n : ℕ}
    [SampleableType (ZMod 2)]
    (f : (Fin n → ZMod 2) → ZMod 2) :
    Pr[= true | simulateQ ((randOracle (ZMod 2)).impl +
        fun x => (return f x : ProbComp (ZMod 2)))
      (BLR.basicVerifier (F := ZMod 2) (n := n))] =
    Pr[= true | simulateQ ((BLR.normalRandOracle (ZMod 2)).impl +
        fun x => (return f x : ProbComp (ZMod 2)))
      (BLR.verifier (F := ZMod 2) (n := n))] := by
  rw [blrBasicVerifier_acceptanceProbability_sum (F := ZMod 2) (n := n) f]
  rw [blrVerifier_acceptanceProbability_units (F := ZMod 2) (n := n) f]
  simp [zmod2_unit_coe]

/-- Over `ZMod 2`, completeness transfers from the scalar-sampling BLR verifier to
the additive basic verifier using the acceptance-probability equality above. -/
theorem BLR_basic_completeness_ZMod2 {n : ℕ}
    [Nonempty (Fin n)] [SampleableType (ZMod 2)]
    {f : (Fin n → ZMod 2) → ZMod 2}
    (hf : f ∈ BlrPcp.LinearSet (F := ZMod 2) (Idx := Fin n)) :
    Pr[= true | simulateQ ((randOracle (ZMod 2)).impl +
        fun x => (return f x : ProbComp (ZMod 2)))
      (BLR.basicVerifier (F := ZMod 2) (n := n))] = 1 := by
  rw [blrBasicVerifier_acceptanceProbability_eq_verifier_ZMod2]
  exact BLR_completeness (F := ZMod 2) (n := n) hf

/-- Over `ZMod 2`, soundness transfers from the scalar-sampling BLR verifier to
the additive basic verifier as an acceptance-probability upper bound. The
underlying soundness input is the finite-field theorem `BLR_soundness`. -/
theorem BLR_basic_soundness_ZMod2 {n : ℕ}
    [Nonempty (Fin n)] [SampleableType (ZMod 2)]
    (f : (Fin n → ZMod 2) → ZMod 2) :
    Pr[= true | simulateQ ((randOracle (ZMod 2)).impl +
        fun x => (return f x : ProbComp (ZMod 2)))
      (BLR.basicVerifier (F := ZMod 2) (n := n))] ≤
      1 - distanceToLin f := by
  rw [blrBasicVerifier_acceptanceProbability_eq_verifier_ZMod2]
  exact BLR_soundness (F := ZMod 2) (n := n) f
