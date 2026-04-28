import BlrPcp.Basic
import BlrPcp.Oracle

/-!
# BLR linearity test

The BLR test, defined as an oracle computation.
-/

open OracleComp

namespace BLR
abbrev spec (F : Type) (n : ℕ) :
    OracleSpec (ℕ ⊕ (Fin n → F)) :=
  (unifSpec + ((Fin n → F) →ₒ F))

def verifier {F : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
    [SampleableType F] [SampleableType Fˣ] {n : ℕ} :
    OracleComp (spec F n) Bool := do
  let x ← ($ᵗ (Fin n → F))
  let y ← ($ᵗ (Fin n → F))
  let a ← ($ᵗ Fˣ)
  let b ← ($ᵗ Fˣ)
  let z : Fin n → F := fun i => a * x i + b * y i
  let fx : F ← query (spec := spec F n) (.inr x)
  let fy : F ← query (spec := spec F n) (.inr y)
  let fz : F ← query (spec := spec F n) (.inr z)
  return (a * fx + b * fy) == fz

noncomputable def distanceToLinear {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (f : (Fin n → F) → F) : ENNReal :=
  ENNReal.ofReal <| if h : n = 0 then 0 else
    letI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩
    BlrPcp.distanceToLinear (F := F) (Idx := Fin n) f

lemma vector_card_clog_le (F : Type) [Fintype F] (n : ℕ) :
    Nat.clog 2 (Fintype.card (Fin n → F)) ≤
      n * Nat.clog 2 (Fintype.card F) := by
  rw [Fintype.card_pi_const]
  exact Nat.clog_le_of_le_pow <| by
    have hpow := Nat.pow_le_pow_left
      (show Fintype.card F ≤ 2 ^ Nat.clog 2 (Fintype.card F) from
        Nat.le_pow_clog (by decide) _) n
    rwa [← Nat.pow_mul, Nat.mul_comm] at hpow

lemma units_card_clog_le (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Nat.clog 2 (Fintype.card Fˣ) ≤ Nat.clog 2 (Fintype.card F) :=
  Nat.clog_mono_right 2 <|
    Fintype.card_le_of_injective (fun x : Fˣ => (x : F)) fun _ _ h => Units.ext h

end BLR

private lemma queryBound_mono {ι α : Type} {proofSpec : OracleSpec ι}
    {oa : OracleComp (unifSpec + proofSpec) α} {q r q' r' : ℕ}
    (h : QueryBound oa q r) (hq : q ≤ q') (hr : r ≤ r') :
    QueryBound oa q' r' := by
  revert q r q' r'
  induction oa using OracleComp.inductionOn with
  | pure _ =>
      intro q r q' r' h hq hr
      trivial
  | query_bind t oa ih =>
      intro q r q' r' h hq hr
      rw [QueryBound, OracleComp.isQueryBound_query_bind_iff] at h ⊢
      cases t with
      | inl n =>
          refine ⟨Nat.le_trans h.1 hr, fun u => ?_⟩
          exact ih u (h.2 u) hq (Nat.sub_le_sub_right hr _)
      | inr _ =>
          refine ⟨Nat.lt_of_lt_of_le h.1 hq, fun u => ?_⟩
          exact ih u (h.2 u) (Nat.sub_le_sub_right hq _) hr

private lemma queryBound_bind {ι α β : Type} {proofSpec : OracleSpec ι}
    {oa : OracleComp (unifSpec + proofSpec) α}
    {ob : α → OracleComp (unifSpec + proofSpec) β} {q₁ r₁ q₂ r₂ : ℕ}
    (hoa : QueryBound oa q₁ r₁) (hob : ∀ x, QueryBound (ob x) q₂ r₂) :
    QueryBound (oa >>= ob) (q₁ + q₂) (r₁ + r₂) := by
  revert q₁ r₁
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro q₁ r₁ hoa
      simpa using queryBound_mono (hob x) (by omega) (by omega)
  | query_bind t oa ih =>
      intro q₁ r₁ hoa
      rw [QueryBound, OracleComp.isQueryBound_query_bind_iff] at hoa
      simp only [QueryBound, bind_assoc]
      rw [OracleComp.isQueryBound_query_bind_iff]
      cases t with
      | inl n =>
          refine ⟨by omega, fun u => ?_⟩
          exact queryBound_mono (ih u (hoa.2 u)) (by omega) (by omega)
      | inr _ =>
          refine ⟨by omega, fun u => ?_⟩
          exact queryBound_mono (ih u (hoa.2 u)) (by omega) (by omega)

theorem BLR_soundness {F : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
    [SampleableType F] [SampleableType Fˣ] {n : ℕ} (f : (Fin n → F) → F) :
  Pr[= false | simulateQ (rand.impl + (fun v => (return f v : ProbComp F))) BLR.verifier]
    ≥ BLR.distanceToLinear f := by
  sorry

/-- `BLR.verifier` makes at most 3 queries to `f` and uses at most
the randomness used by two vector samples and two nonzero scalar samples. -/
theorem BLR_query_complexity {F : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
    [SampleableType F] [SampleableType Fˣ] {n rv ru : ℕ}
    (hVec : QueryBound
      (liftM ($ᵗ (Fin n → F)) : OracleComp (BLR.spec F n) (Fin n → F)) 0 rv)
    (hUnit : QueryBound
      (liftM ($ᵗ Fˣ) : OracleComp (BLR.spec F n) Fˣ) 0 ru) :
    QueryBound (BLR.verifier (F := F) (n := n)) 3
      (2 * rv + 2 * ru) := by
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
  simp only [BLR.verifier]
  simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    queryBound_bind hVec fun x =>
      queryBound_bind hVec fun y =>
        queryBound_bind hUnit fun a =>
          queryBound_bind hUnit fun b =>
            hProof x y a b
