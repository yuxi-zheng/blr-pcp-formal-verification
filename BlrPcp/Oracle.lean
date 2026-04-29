import Architect
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.OracleComp
import VCVio.OracleComp.OracleContext
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Oracle computations

This file defines the BLR test, PCPs and LPCPs in terms of oracle computations.

## Main declarations

- `PCP`, `LPCP`: PCP and linear PCP language classes with query and randomness bounds.
-/

open OracleComp
open scoped Matrix

abbrev randSpec (F : Type) : OracleSpec Unit :=
  Unit →ₒ F

/-- An oracle that samples a random element from `F`. -/
abbrev rand (F : Type) [SampleableType F] : OracleContext Unit ProbComp where
  spec := randSpec F
  impl := fun _ => $ᵗ F

/-- `RunsInTime oa n` means `oa` halts in at most `n` steps. -/
abbrev RunsInTime {ι α : Type} {spec : OracleSpec ι}
    (_oa : OracleComp spec α) (_n : ℕ) : Prop :=
  true -- TODO: look into https://api.cslib.io/docs/Cslib/Algorithms/Lean/TimeM.html
       -- or even https://github.com/Shreyas4991/Algolean

/-- `QueryBound oa q r` means `oa` makes at most `q` proof queries
and at most `r` randomness queries. -/
abbrev QueryBound {ρ ι α : Type} {randSpec : OracleSpec ρ} {proofSpec : OracleSpec ι}
    (oa : OracleComp (randSpec + proofSpec) α) (q r : ℕ) : Prop :=
  OracleComp.IsQueryBound oa (r, q)
    (fun
      | .inl _, (r, _) => 0 < r
      | .inr _, (_, q) => 0 < q)
    (fun
      | .inl _, (r, q) => (r - 1, q)
      | .inr _, (r, q) => (r, q - 1))

lemma queryBound_mono {ρ ι α : Type} {randSpec : OracleSpec ρ} {proofSpec : OracleSpec ι}
    {oa : OracleComp (randSpec + proofSpec) α} {q r q' r' : ℕ}
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
      | inl _ =>
          refine ⟨Nat.lt_of_lt_of_le h.1 hr, fun u => ?_⟩
          exact ih u (h.2 u) hq (Nat.sub_le_sub_right hr _)
      | inr _ =>
          refine ⟨Nat.lt_of_lt_of_le h.1 hq, fun u => ?_⟩
          exact ih u (h.2 u) (Nat.sub_le_sub_right hq _) hr

lemma queryBound_bind {ρ ι α β : Type} {randSpec : OracleSpec ρ}
    {proofSpec : OracleSpec ι}
    {oa : OracleComp (randSpec + proofSpec) α}
    {ob : α → OracleComp (randSpec + proofSpec) β} {q₁ r₁ q₂ r₂ : ℕ}
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
      | inl _ =>
          refine ⟨by omega, fun u => ?_⟩
          exact queryBound_mono (ih u (hoa.2 u)) (by omega) (by omega)
      | inr _ =>
          refine ⟨by omega, fun u => ?_⟩
          exact queryBound_mono (ih u (hoa.2 u)) (by omega) (by omega)

namespace PCP

/-- A proof is represented as a function `π : [ℓ] → F`.
`π(q)` is the answer to query `q`. -/
abbrev proofSpec (F : Type) (ℓ : ℕ) : OracleSpec (Fin ℓ) :=
  Fin ℓ →ₒ F

abbrev proof {F : Type} {ℓ : ℕ}
    (π : Fin ℓ → F) : OracleContext (Fin ℓ) ProbComp where
  spec := proofSpec F ℓ
  impl := fun q => return π q

abbrev spec (F : Type) (ℓ : ℕ) : OracleSpec (Unit ⊕ Fin ℓ) :=
  randSpec F + proofSpec F ℓ

end PCP

abbrev PCPVerifier (α : Type) (size : α → ℕ) (F : Type) (ℓ : ℕ → ℕ) : Type :=
  (x : α) → OracleComp (PCP.spec F (ℓ (size x))) Bool

/-- The complexity class PCP. Note that we use a randomness oracle that samples elements from `F`
and not `{0,1}`. To recover the bit randomness compleixty, we need to multiply `r` by `log |F|`.-/
def PCP {α : Type} (size : α → ℕ) (ε_c ε_s : ENNReal) (F : Type)
    [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]
    (ℓ q r : ℕ → ℕ) : Set (Set α) :=
  { L | ∃ (V : PCPVerifier α size F ℓ) (t : Polynomial ℕ), ∀ x,
    RunsInTime (V x) (t.eval (size x)) ∧
    QueryBound (V x) (q (size x)) (r (size x)) ∧
    (x ∈ L → ∃ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ ((rand F).impl + (PCP.proof π).impl) (V x)] ≥ 1 - ε_c) ∧
    (x ∉ L → ∀ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ ((rand F).impl + (PCP.proof π).impl) (V x)] ≤ ε_s) }

namespace LPCP

/-- A linear-query proof: a query is a vector `u`,
and the answer is the inner product `⟨π, u⟩`. -/
abbrev proofSpec (F : Type) (ℓ : ℕ) : OracleSpec (Fin ℓ → F) :=
  (Fin ℓ → F) →ₒ F

abbrev proof {F : Type} [Field F] {ℓ : ℕ}
    (π : Fin ℓ → F) : OracleContext (Fin ℓ → F) ProbComp where
  spec := proofSpec F ℓ
  impl := fun u => return π ⬝ᵥ u

abbrev spec (F : Type) (ℓ : ℕ) : OracleSpec (Unit ⊕ (Fin ℓ → F)) :=
  randSpec F + proofSpec F ℓ

end LPCP

abbrev LPCPVerifier (α : Type) (size : α → ℕ) (F : Type) [Field F] (ℓ : ℕ → ℕ) : Type :=
  (x : α) → OracleComp (LPCP.spec F (ℓ (size x))) Bool

/-- The complexity class PCP. Note that we use a randomness oracle that samples elements from `F`
and not `{0,1}`. To recover the bit randomness compleixty, we need to multiply `r` by `log |F|`.-/
def LPCP {α : Type} (size : α → ℕ) (ε_c ε_s : ENNReal) (F : Type)
    [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]
    (ℓ q r : ℕ → ℕ) : Set (Set α) :=
  { L | ∃ (V : LPCPVerifier α size F ℓ) (t : Polynomial ℕ), ∀ x,
    RunsInTime (V x) (t.eval (size x)) ∧
    QueryBound (V x) (q (size x)) (r (size x)) ∧
    (x ∈ L → ∃ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ ((rand F).impl + (LPCP.proof π).impl) (V x)] ≥ 1 - ε_c) ∧
    (x ∉ L → ∀ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ ((rand F).impl + (LPCP.proof π).impl) (V x)] ≤ ε_s) }
