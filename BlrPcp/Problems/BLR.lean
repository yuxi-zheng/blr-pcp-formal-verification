import BlrPcp.Oracle
import BlrPcp.Bridge

/-!
# BLR linearity test

The finite-field BLR verifier as an oracle computation.
-/

open OracleComp

namespace BLR

/-- Randomness used by the finite-field BLR verifier. -/
inductive Rand (F : Type) where
  | field
  | unit

/-- BLR randomness is either a field element or a nonzero scalar. -/
def randRange (F : Type) [Field F] : Rand F → Type
  | .field => F
  | .unit => Fˣ

abbrev randSpec (F : Type) [Field F] : OracleSpec (Rand F) :=
  OracleSpec.ofFn (randRange F)

abbrev spec (F : Type) [Field F] (n : ℕ) : OracleSpec (Rand F ⊕ (Fin n → F)) :=
  randSpec F + LPCP.proofSpec F n

/-- The BLR randomness implementation: field samples for vector coordinates,
and unit samples for the scalar coefficients. -/
abbrev rand (F : Type) [Field F] [SampleableType F] [SampleableType Fˣ] :
    OracleContext (Rand F) ProbComp where
  spec := randSpec F
  impl
    | .field => $ᵗ F
    | .unit => $ᵗ Fˣ

/-- Sample one field element. -/
def sampleField {F : Type} [Field F] {n : ℕ} : OracleComp (spec F n) F :=
  query (spec := spec F n) (.inl .field)

/-- Sample one nonzero scalar. -/
def sampleUnit {F : Type} [Field F] {n : ℕ} : OracleComp (spec F n) Fˣ :=
  query (spec := spec F n) (.inl .unit)

/-- Sample a vector in `F^n` using `n` calls to the field-valued randomness oracle. -/
def sampleVector (F : Type) [Field F] (n : ℕ) : OracleComp (spec F n) (Fin n → F) :=
  Fin.mOfFn n fun _ => sampleField (F := F)

/-- The finite-field BLR verifier. -/
def verifier {F : Type} [Field F] [DecidableEq F] {n : ℕ} :
    OracleComp (spec F n) Bool := do
  let x : Fin n → F ← sampleVector F n
  let y : Fin n → F ← sampleVector F n
  let a : Fˣ ← sampleUnit (F := F)
  let b : Fˣ ← sampleUnit (F := F)
  let fx : F ← query (spec := spec F n) (.inr x)
  let fy : F ← query (spec := spec F n) (.inr y)
  let fxy : F ← query (spec := spec F n) (.inr fun i => (a : F) * x i + (b : F) * y i)
  return decide ((a : F) * fx + (b : F) * fy = fxy)

lemma sampleVector_queryBoundAux (F : Type) [Field F] (m n : ℕ) :
    QueryBound (Fin.mOfFn m fun _ => sampleField (F := F) (n := n)) 0 m := by
  induction m with
  | zero =>
      simp [Fin.mOfFn, QueryBound]
  | succ m ih =>
      simp only [Fin.mOfFn]
      have hHead : QueryBound (sampleField (F := F) (n := n)) 0 1 := by
        simp [sampleField, QueryBound]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        queryBound_bind hHead fun _ => by
          simpa [QueryBound] using ih

lemma sampleVector_queryBound (F : Type) [Field F] (n : ℕ) :
    QueryBound (sampleVector F n) 0 n := by
  simpa [sampleVector] using sampleVector_queryBoundAux F n n

lemma sampleUnit_queryBound {F : Type} [Field F] {n : ℕ} :
    QueryBound (sampleUnit (F := F) (n := n)) 0 1 := by
  simp [sampleUnit, QueryBound]

end BLR

/-- `BLR.verifier` makes three queries to `f` and uses two random vectors and two scalars. -/
theorem BLR_query_complexity {F : Type} [Field F] [DecidableEq F] {n : ℕ} :
    QueryBound (BLR.verifier (F := F) (n := n)) 3 (2 * n + 2) := by
  have hProof : ∀ (x y : Fin n → F) (a b : Fˣ),
      QueryBound
        (do
          let fx : F ←
            (liftM (query (spec := BLR.spec F n) (.inr x)) :
              OracleComp (BLR.spec F n) F)
          let fy : F ←
            (liftM (query (spec := BLR.spec F n) (.inr y)) :
              OracleComp (BLR.spec F n) F)
          let fxy : F ←
            (liftM
              (query (spec := BLR.spec F n) (.inr fun i => (a : F) * x i + (b : F) * y i)) :
              OracleComp (BLR.spec F n) F)
          return decide ((a : F) * fx + (b : F) * fy = fxy)) 3 0 := by
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
    [Field F] [DecidableEq F] [Fintype F] [SampleableType F] [SampleableType Fˣ]
    (m n : ℕ) (impl : QueryImpl (LPCP.proofSpec F n) ProbComp)
    (x : Fin m → F) :
    Pr[= x |
      simulateQ ((BLR.rand F).impl + impl)
        (Fin.mOfFn m fun _ => BLR.sampleField (F := F) (n := n))] =
      (Fintype.card (Fin m → F) : ENNReal)⁻¹ := by
  induction m with
  | zero =>
      have hx : x = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      subst hx
      simp [Fin.mOfFn]
  | succ m ih =>
      simp only [Fin.mOfFn, BLR.sampleField, simulateQ_bind, simulateQ_query,
        simulateQ_pure, OracleQuery.cont_query, id_map, OracleQuery.input_query, BLR.rand]
      rw [probOutput_bind_eq_tsum, tsum_fintype]
      rw [Finset.sum_eq_single (x 0)]
      · change Pr[= x 0 | ($ᵗ F : ProbComp F)] *
            Pr[= x |
              (Fin.cons (x 0)) <$>
                simulateQ ((BLR.rand F).impl + impl)
                  (Fin.mOfFn m fun _ => BLR.sampleField (F := F) (n := n))] = _
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
                simulateQ ((BLR.rand F).impl + impl)
                  (Fin.mOfFn m fun _ => BLR.sampleField (F := F) (n := n))] = 0
        rw [probOutput_finCons_map_ne _ x ha]
        simp
      · intro h
        simp at h

@[simp]
lemma probOutput_simulateQ_BLR_sampleVector {F : Type}
    [Field F] [DecidableEq F] [Fintype F] [SampleableType F] [SampleableType Fˣ] {n : ℕ}
    (impl : QueryImpl (LPCP.proofSpec F n) ProbComp) (x : Fin n → F) :
    Pr[= x | simulateQ ((BLR.rand F).impl + impl) (BLR.sampleVector F n)] =
      (Fintype.card (Fin n → F) : ENNReal)⁻¹ := by
  simpa [BLR.sampleVector] using
    probOutput_simulateQ_BLR_sampleVectorAux (F := F) n n impl x

lemma probOutput_true_map_simulateQ_BLR_sampleVector {F : Type}
    [Field F] [DecidableEq F] [Fintype F] [SampleableType F] [SampleableType Fˣ] {n : ℕ}
    (impl : QueryImpl (LPCP.proofSpec F n) ProbComp)
    (g : (Fin n → F) → Bool) :
    Pr[= true | g <$> simulateQ ((BLR.rand F).impl + impl) (BLR.sampleVector F n)] =
      ∑ y : Fin n → F,
        (Fintype.card (Fin n → F) : ENNReal)⁻¹ * if g y = true then 1 else 0 := by
  rw [probOutput_map_eq_sum_fintype_ite]
  apply Finset.sum_congr rfl
  intro y _
  rw [probOutput_simulateQ_BLR_sampleVector (impl := impl) y]
  by_cases hy : g y = true <;> simp [hy]

@[simp]
lemma probOutput_simulateQ_BLR_sampleUnit {F : Type}
    [Field F] [Fintype Fˣ] [SampleableType F] [SampleableType Fˣ] {n : ℕ}
    (impl : QueryImpl (LPCP.proofSpec F n) ProbComp) (a : Fˣ) :
    Pr[= a | simulateQ ((BLR.rand F).impl + impl) (BLR.sampleUnit (F := F) (n := n))] =
      (Fintype.card Fˣ : ENNReal)⁻¹ := by
  simp [BLR.sampleUnit, BLR.rand, probOutput_uniformSample]

lemma probOutput_true_map_simulateQ_BLR_sampleUnit {F : Type}
    [Field F] [Fintype Fˣ] [DecidableEq Fˣ] [SampleableType F] [SampleableType Fˣ] {n : ℕ}
    (impl : QueryImpl (LPCP.proofSpec F n) ProbComp) (g : Fˣ → Bool) :
    Pr[= true | g <$> simulateQ ((BLR.rand F).impl + impl) (BLR.sampleUnit (F := F) (n := n))] =
      ∑ a : Fˣ, (Fintype.card Fˣ : ENNReal)⁻¹ * if g a = true then 1 else 0 := by
  rw [probOutput_map_eq_sum_fintype_ite]
  apply Finset.sum_congr rfl
  intro a _
  rw [probOutput_simulateQ_BLR_sampleUnit (impl := impl) a]
  by_cases ha : g a = true <;> simp [ha]

private lemma ite_classical_eq {α : Type} [Zero α] [One α] {p : Prop} [Decidable p] :
    @ite α p (Classical.propDecidable p) 1 0 = if p then 1 else 0 := by
  by_cases hp : p <;> simp [hp]

private lemma sum_units_eq_sum_nonzero {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (G : F → ENNReal) :
    (∑ a : Fˣ, G a) = ∑ a ∈ BlrPcp.nonzeroScalars (F := F), G a := by
  calc
    (∑ a : Fˣ, G a) =
        ∑ a : {a : F // a ≠ 0}, G a := by
          exact Fintype.sum_equiv unitsEquivNeZero _ _ fun _ => rfl
    _ = ∑ a ∈ BlrPcp.nonzeroScalars (F := F), G a := by
          simpa [BlrPcp.nonzeroScalars] using
            (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
              (f := G) (p := fun a : F => a ≠ 0))

private lemma card_units_eq_card_nonzeroScalars {F : Type}
    [Field F] [Fintype F] [DecidableEq F] :
    (Fintype.card Fˣ : ENNReal) = ((BlrPcp.nonzeroScalars (F := F)).card : ENNReal) := by
  have h : Fintype.card Fˣ = (BlrPcp.nonzeroScalars (F := F)).card := by
    rw [Fintype.card_congr unitsEquivNeZero]
    exact Fintype.card_of_subtype (p := fun a : F => a ≠ 0)
      (BlrPcp.nonzeroScalars (F := F)) (by
        intro a
        simp [BlrPcp.nonzeroScalars])
  exact_mod_cast h

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
          c * ∑ a ∈ BlrPcp.nonzeroScalars (F := F),
            ((BlrPcp.nonzeroScalars (F := F)).card : ENNReal)⁻¹ *
              ∑ b ∈ BlrPcp.nonzeroScalars (F := F),
                ((BlrPcp.nonzeroScalars (F := F)).card : ENNReal)⁻¹ * I a b x y := by
  rw [card_units_eq_card_nonzeroScalars (F := F)]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  rw [sum_units_eq_sum_nonzero (F := F)
    (G := fun a =>
      ((BlrPcp.nonzeroScalars (F := F)).card : ENNReal)⁻¹ *
        ∑ b : Fˣ,
          ((BlrPcp.nonzeroScalars (F := F)).card : ENNReal)⁻¹ * I a b x y)]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [sum_units_eq_sum_nonzero (F := F)
    (G := fun b =>
      ((BlrPcp.nonzeroScalars (F := F)).card : ENNReal)⁻¹ * I a b x y)]

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

private lemma ofReal_BLR_acceptance_sum {F : Type} {n : ℕ}
    [Field F] [DecidableEq F] [Fintype F] [Nonempty (Fin n)]
    (f : (Fin n → F) → F)
    [∀ a b x y, Decidable (BlrPcp.BLRAcceptsAt (F := F) (Idx := Fin n) f a b x y)] :
    ENNReal.ofReal
      (∑ a ∈ BlrPcp.nonzeroScalars (F := F),
        ∑ b ∈ BlrPcp.nonzeroScalars (F := F),
          ∑ x : Fin n → F, ∑ y : Fin n → F,
            if BlrPcp.BLRAcceptsAt (F := F) (Idx := Fin n) f a b x y
            then (1 : Real) else 0) =
      ∑ a ∈ BlrPcp.nonzeroScalars (F := F),
        ∑ b ∈ BlrPcp.nonzeroScalars (F := F),
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

private lemma acceptanceProbabilityBLR_eq_sum {F : Type} {n : ℕ}
    [Field F] [DecidableEq F] [Fintype F] [Nonempty (Fin n)]
    (f : (Fin n → F) → F)
    [∀ a b x y, Decidable (BlrPcp.BLRAcceptsAt (F := F) (Idx := Fin n) f a b x y)] :
    acceptanceProbabilityBLR f =
      ((BlrPcp.nonzeroScalars (F := F)).card : ENNReal)⁻¹ *
        ((BlrPcp.nonzeroScalars (F := F)).card : ENNReal)⁻¹ *
          (Fintype.card (Fin n → F) : ENNReal)⁻¹ *
            (Fintype.card (Fin n → F) : ENNReal)⁻¹ *
              ∑ a ∈ BlrPcp.nonzeroScalars (F := F),
                ∑ b ∈ BlrPcp.nonzeroScalars (F := F),
                  ∑ x : Fin n → F, ∑ y : Fin n → F,
                    if BlrPcp.BLRAcceptsAt (F := F) (Idx := Fin n) f a b x y
                    then (1 : ENNReal) else 0 := by
  have hnz_nonempty : (BlrPcp.nonzeroScalars (F := F)).Nonempty := by
    exact ⟨1, by simp [BlrPcp.nonzeroScalars]⟩
  have hnz_pos : 0 < ((BlrPcp.nonzeroScalars (F := F)).card : Real) := by
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
                ENNReal.ofReal (((BlrPcp.nonzeroScalars (F := F)).card : Real)⁻¹) *
                  ENNReal.ofReal (((BlrPcp.nonzeroScalars (F := F)).card : Real)⁻¹) *
                    ENNReal.ofReal ((Fintype.card (Fin n → F) : Real)⁻¹) *
                      ENNReal.ofReal ((Fintype.card (Fin n → F) : Real)⁻¹) * z)
              hsum
        · positivity
      · positivity
    · positivity
  · positivity

private lemma blrVerifier_acceptanceProbability_units {F : Type} {n : ℕ}
    [Field F] [DecidableEq F] [Fintype F] [Nonempty (Fin n)]
    [SampleableType F] [SampleableType Fˣ]
    (f : (Fin n → F) → F) :
    Pr[= true | simulateQ ((BLR.rand F).impl + fun x => (return f x : ProbComp F))
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

/-- The oracle BLR verifier has the analytical finite-field BLR acceptance probability. -/
theorem blrVerifier_acceptanceProbability {F : Type} {n : ℕ}
    [Field F] [DecidableEq F] [Fintype F] [Nonempty (Fin n)]
    [SampleableType F] [SampleableType Fˣ]
    (f : (Fin n → F) → F) :
    Pr[= true | simulateQ ((BLR.rand F).impl + fun x => (return f x : ProbComp F))
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

/-- The BLR test has the same rejection probability on `f` as the analytical test. -/
theorem blrSoundnessCompEqAnalytical {F : Type} {n : ℕ}
    [Field F] [DecidableEq F] [Fintype F] [Nonempty (Fin n)]
    [SampleableType F] [SampleableType Fˣ]
    (f : (Fin n → F) → F) :
    Pr[= false | simulateQ ((BLR.rand F).impl + fun x => (return f x : ProbComp F))
      (BLR.verifier (F := F) (n := n))] =
      rejectionProbabilityBLR f := by
  rw [probOutput_false_eq_sub]
  simp [blrVerifier_acceptanceProbability (F := F) (n := n) f, rejectionProbabilityBLR]

/-- Soundness of `BLR.verifier` for finite fields. -/
theorem BLR_soundness {F : Type} {n : ℕ}
    [Field F] [DecidableEq F] [Fintype F] [Nonempty (Fin n)]
    [SampleableType F] [SampleableType Fˣ]
    (f : (Fin n → F) → F) :
    distanceToLin f ≤
      Pr[= false | simulateQ ((BLR.rand F).impl + fun x => (return f x : ProbComp F))
        (BLR.verifier (F := F) (n := n))] := by
  rw [blrSoundnessCompEqAnalytical f]
  exact blrSoundnessAnalytical f

/-- Completeness of `BLR.verifier`: linear functions are accepted with probability one. -/
theorem BLR_completeness {F : Type} {n : ℕ}
    [Field F] [DecidableEq F] [Fintype F] [Nonempty (Fin n)]
    [SampleableType F] [SampleableType Fˣ]
    {f : (Fin n → F) → F}
    (hf : f ∈ BlrPcp.LinearSet (F := F) (Idx := Fin n)) :
    Pr[= true | simulateQ ((BLR.rand F).impl + fun x => (return f x : ProbComp F))
      (BLR.verifier (F := F) (n := n))] = 1 := by
  rw [blrVerifier_acceptanceProbability]
  simp [acceptanceProbabilityBLR, BlrPcp.blr_completeness (F := F) (Idx := Fin n) hf]
