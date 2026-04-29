import BlrPcp.Basic
import BlrPcp.Oracle

/-!
# BLR linearity test

The BLR test, defined as an oracle computation.
-/

open OracleComp

namespace BLR
abbrev unitRandSpec (F : Type) [Field F] : OracleSpec Unit :=
  Unit →ₒ Fˣ

abbrev unitRand (F : Type) [Field F] [SampleableType Fˣ] :
    OracleContext Unit ProbComp where
  spec := unitRandSpec F
  impl := fun _ => $ᵗ Fˣ

abbrev randomSpec (F : Type) [Field F] : OracleSpec (Unit ⊕ Unit) :=
  randSpec F + unitRandSpec F

abbrev random (F : Type) [Field F] [SampleableType F] [SampleableType Fˣ] :
    OracleContext (Unit ⊕ Unit) ProbComp :=
  rand F + unitRand F

abbrev spec (F : Type) [Field F] (n : ℕ) :
    OracleSpec ((Unit ⊕ Unit) ⊕ (Fin n → F)) :=
  randomSpec F + ((Fin n → F) →ₒ F)

def sampleVector {F : Type} [Field F] {n : ℕ} :
    OracleComp (spec F n) (Fin n → F) :=
  Fin.mOfFn n fun _ =>
    (liftM (query (spec := spec F n) (.inl (.inl ()))) : OracleComp (spec F n) F)

def verifier {F : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
    [SampleableType F] [SampleableType Fˣ] {n : ℕ} :
    OracleComp (spec F n) Bool := do
  let x ← sampleVector (F := F) (n := n)
  let y ← sampleVector (F := F) (n := n)
  let a : Fˣ ←
    (liftM (query (spec := spec F n) (.inl (.inr ()))) : OracleComp (spec F n) Fˣ)
  let b : Fˣ ←
    (liftM (query (spec := spec F n) (.inl (.inr ()))) : OracleComp (spec F n) Fˣ)
  let z : Fin n → F := fun i => a * x i + b * y i
  let fx : F ←
    (liftM (query (spec := spec F n) (.inr x)) : OracleComp (spec F n) F)
  let fy : F ←
    (liftM (query (spec := spec F n) (.inr y)) : OracleComp (spec F n) F)
  let fz : F ←
    (liftM (query (spec := spec F n) (.inr z)) : OracleComp (spec F n) F)
  return (a * fx + b * fy) == fz

noncomputable def distanceToLinear {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (f : (Fin n → F) → F) : ENNReal :=
  ENNReal.ofReal <| if h : n = 0 then 0 else
    letI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩
    BlrPcp.distanceToLinear (F := F) (Idx := Fin n) f

end BLR

theorem BLR_soundness {F : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
    [SampleableType F] [SampleableType Fˣ] {n : ℕ} (f : (Fin n → F) → F) :
  Pr[= false | simulateQ ((BLR.random F).impl + (fun v => (return f v : ProbComp F)))
    BLR.verifier]
    ≥ BLR.distanceToLinear f := by
  sorry

lemma BLR.sampleVector_queryBoundAux {F : Type} [Field F] (m n : ℕ) :
    QueryBound
      (Fin.mOfFn m fun _ =>
        (liftM (query (spec := BLR.spec F n) (.inl (.inl ()))) :
          OracleComp (BLR.spec F n) F)) 0 m := by
  induction m with
  | zero =>
      simp [Fin.mOfFn, QueryBound]
  | succ m ih =>
      simp only [Fin.mOfFn]
      have hHead :
          QueryBound
            ((liftM (query (spec := BLR.spec F n) (.inl (.inl ()))) :
              OracleComp (BLR.spec F n) F)) 0 1 := by
        simp [QueryBound]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        queryBound_bind hHead fun _ => by
          simpa [QueryBound] using ih

lemma BLR.sampleVector_queryBound {F : Type} [Field F] {n : ℕ} :
    QueryBound (BLR.sampleVector (F := F) (n := n)) 0 n := by
  simpa [BLR.sampleVector] using BLR.sampleVector_queryBoundAux (F := F) n n

/-- `BLR.verifier` makes at most 3 queries to `f` and uses `2n + 2`
random field/unit samples. -/
theorem BLR_query_complexity {F : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
    [SampleableType F] [SampleableType Fˣ] {n : ℕ} :
    QueryBound (BLR.verifier (F := F) (n := n)) 3 (2 * n + 2) := by
  have hProof : ∀ (x y : Fin n → F) (a b : Fˣ),
      QueryBound
        (do
          let z : Fin n → F := fun i => a * x i + b * y i
          let fx : F ←
            (liftM (query (spec := BLR.spec F n) (.inr x)) :
              OracleComp (BLR.spec F n) F)
          let fy : F ←
            (liftM (query (spec := BLR.spec F n) (.inr y)) :
              OracleComp (BLR.spec F n) F)
          let fz : F ←
            (liftM (query (spec := BLR.spec F n) (.inr z)) :
              OracleComp (BLR.spec F n) F)
          return (a * fx + b * fy) == fz) 3 0 := by
    intro x y a b
    simp only [QueryBound]
    rw [OracleComp.isQueryBound_query_bind_iff]
    refine ⟨by simp, fun fx => ?_⟩
    rw [OracleComp.isQueryBound_query_bind_iff]
    refine ⟨by simp, fun fy => ?_⟩
    rw [OracleComp.isQueryBound_query_bind_iff]
    exact ⟨by simp, fun fz => trivial⟩
  have hUnit :
      QueryBound
        ((liftM (query (spec := BLR.spec F n) (.inl (.inr ()))) :
          OracleComp (BLR.spec F n) Fˣ)) 0 1 := by
    simp [QueryBound]
  simp only [BLR.verifier]
  simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    queryBound_bind BLR.sampleVector_queryBound fun x =>
      queryBound_bind BLR.sampleVector_queryBound fun y =>
        queryBound_bind hUnit fun a =>
          queryBound_bind hUnit fun b =>
            hProof x y a b
