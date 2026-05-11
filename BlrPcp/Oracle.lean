import Architect
import BlrPcp.Basic
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.OracleComp
import VCVio.OracleComp.OracleContext
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Oracle computations

This file defines the BLR test, PCPs and LPCPs in terms of oracle computations.

## Main declarations

- `randOracleSpec`, `randOracle`: the specification and implementation of a randomness oracle
  that samples a uniform element from a type `F`.
- `proofOracleSpec_fin`, `proofOracleSpec_fin_vector`: proof-oracle specs for PCP (queries are
  indices `Fin ℓ`) and LPCP (queries are vectors `Fin ℓ → F`), both answering in `F`.
- `PCP.proofOracle`, `LPCP.proofOracle`: implementations of the proof oracles given a proof `π`.
- `PCP.fullSpec`, `LPCP.fullSpec`: combined randomness + proof oracle specs.
- `RunsInTime`, `QueryBound`: time and (randomness, proof) query bounds for verifier computations.
- `PCPVerifier`, `LPCPVerifier`: the type of PCP and LPCP verifiers.
- `PCP`, `LPCP`: PCP and LPCP complexity classes with query and randomness bounds.

## Design choices
- For each instance of PCP (LINEQ, TENSORQ, ..), we purposely pass an oracle which generates exactly 1 element. Each
  instance will use that random oracle to construct their own "whichever" random generator that suit them, e.g. vector
  of size n, n * 2, n^2 + n, ...

  Of course we can just define everything in simple terms and , as everything is either F or Z/2 now ..
-/

open OracleComp
open scoped Matrix
open BlrPcp (Vec ScalarFn linearFn IsLinear LinearSet distance)

/-- Specification of oracles that sample a random element from `F`. -/
abbrev randOracleSpec_unit_fin (F : Type) : OracleSpec Unit :=
  Unit →ₒ F

/-- We only work in finite fields. -/
abbrev randOracleSpec (F : Type) := randOracleSpec_unit_fin F

/-- An oracle that samples a random element from `F`. -/
abbrev randOracle (F : Type) [SampleableType F] : OracleContext Unit ProbComp where
  spec := randOracleSpec F
  impl := fun _ => $ᵗ F

namespace OracleUtil

def sampleVectorAux {ι F : Type} {spec : OracleSpec ι} (query1 : OracleComp spec F) :
    (m : ℕ) → OracleComp spec (Vector F m)
  | 0     => pure #v[]
  | m + 1 => Vector.push <$> sampleVectorAux query1 m <*> query1

/-- Sample `m` independent draws from `query1`, returning the result as `Fin m → F`. -/
def sampleVector {ι F : Type} {spec : OracleSpec ι} (query1 : OracleComp spec F) (m : ℕ) :
    OracleComp spec (Vec F (Fin m)) :=
  (·.get) <$> sampleVectorAux query1 m

end OracleUtil

abbrev proofOracleSpec_fin (F : Type) (ℓ : ℕ) : OracleSpec (Fin ℓ) :=
  Fin ℓ →ₒ F

abbrev proofOracleSpec_fin_vector (F : Type) (ℓ : ℕ) : OracleSpec (Fin ℓ → F) :=
  (Fin ℓ → F) →ₒ F

/- Used in LPCP, basic BLR, ... where they both proof-query an F-vector and get back an element. -/
abbrev fullSpec_fin_vector (F : Type) (ℓ : ℕ) : OracleSpec (Unit ⊕ (Fin ℓ → F)) :=
  randOracleSpec F + proofOracleSpec_fin_vector F ℓ

/-- `RunsInTime oa n` means `oa` halts in at most `n` steps. -/
abbrev RunsInTime {ι α : Type} {spec : OracleSpec ι}
    (_oa : OracleComp spec α) (_n : ℕ) : Prop :=
  true -- TODO: look into https://api.cslib.io/docs/Cslib/Algorithms/Lean/TimeM.html
       -- or even https://github.com/Shreyas4991/Algolean

/-- `QueryBound oa r q` means `oa` makes at most `r` randomness queries
and at most `q` proof queries. -/
abbrev QueryBound {ρ ι α : Type} {randOracleSpec : OracleSpec ρ} {proofSpec : OracleSpec ι}
    (oa : OracleComp (randOracleSpec + proofSpec) α) (r q : ℕ) : Prop :=
  OracleComp.IsQueryBound oa (r, q)
    (fun
      | .inl _, (r, _) => 0 < r
      | .inr _, (_, q) => 0 < q)
    (fun
      | .inl _, (r, q) => (r - 1, q)
      | .inr _, (r, q) => (r, q - 1))

lemma queryBound_mono {ρ ι α : Type} {randOracleSpec : OracleSpec ρ} {proofSpec : OracleSpec ι}
    {oa : OracleComp (randOracleSpec + proofSpec) α} {q r q' r' : ℕ}
    (h : QueryBound oa r q) (hq : q ≤ q') (hr : r ≤ r') :
    QueryBound oa r' q' := by
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

lemma queryBound_bind {ρ ι α β : Type} {randOracleSpec : OracleSpec ρ}
    {proofSpec : OracleSpec ι}
    {oa : OracleComp (randOracleSpec + proofSpec) α}
    {ob : α → OracleComp (randOracleSpec + proofSpec) β} {q₁ r₁ q₂ r₂ : ℕ}
    (hoa : QueryBound oa r₁ q₁) (hob : ∀ x, QueryBound (ob x) r₂ q₂) :
    QueryBound (oa >>= ob) (r₁ + r₂) (q₁ + q₂) := by
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

/-- A proof is represented as a function `π : [ℓ] → F`, i.e. a vector of size ℓ in field F.
`π(q)` is the answer to query `q`. -/
abbrev proofOracle {F : Type} {ℓ : ℕ}
    (π : Fin ℓ → F) : OracleContext (Fin ℓ) ProbComp where
  spec := proofOracleSpec_fin F ℓ
  impl := fun q => return π q

/-- Specification of a PCP instance, which includes a random Oracle and a proof Oracle. -/
abbrev fullSpec (F : Type) (ℓ : ℕ) : OracleSpec (Unit ⊕ Fin ℓ) :=
  randOracleSpec F + proofOracleSpec_fin F ℓ

end PCP

abbrev PCPVerifier (α : Type) (size : α → ℕ) (F : Type) (ℓ : ℕ → ℕ) : Type :=
  (x : α) → OracleComp (PCP.fullSpec F (ℓ (size x))) Bool

/-- The complexity class PCP. Note that we use a randomness oracle that samples elements from `F`
and not `{0,1}`. To recover the bit randomness compleixty, we need to multiply `r` by `log |F|`.-/
def PCP {α : Type} (size : α → ℕ) (ε_c ε_s : ENNReal) (F : Type)
    [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]
    (ℓ q r : ℕ → ℕ) : Set (Set α) :=
  { L | ∃ (V : PCPVerifier α size F ℓ) (t : Polynomial ℕ), ∀ x,
    RunsInTime (V x) (t.eval (size x)) ∧
    QueryBound (V x) (r (size x)) (q (size x)) ∧
    (x ∈ L → ∃ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ ((randOracle F).impl + (PCP.proofOracle π).impl) (V x)] ≥ 1 - ε_c) ∧
    (x ∉ L → ∀ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ ((randOracle F).impl + (PCP.proofOracle π).impl) (V x)] ≤ ε_s) }

namespace LPCP

/-- A linear-query proof: a query is a vector `u`,
and the answer is the inner product `⟨π, u⟩`. -/
abbrev proofOracle {F : Type} [Field F] {ℓ : ℕ}
    (π : Fin ℓ → F) : OracleContext (Fin ℓ → F) ProbComp where
  spec := proofOracleSpec_fin_vector F ℓ
  impl := fun u => return π ⬝ᵥ u

abbrev fullSpec (F : Type) (ℓ : ℕ) : OracleSpec (Unit ⊕ (Fin ℓ → F)) := fullSpec_fin_vector F ℓ

end LPCP

abbrev LPCPVerifier (α : Type) (size : α → ℕ) (F : Type) [Field F] (ℓ : ℕ → ℕ) : Type :=
  (x : α) → OracleComp (LPCP.fullSpec F (ℓ (size x))) Bool

/-- The complexity class LPCP. Note that we use a randomness oracle that samples elements from `F`
and not `{0,1}`. To recover the bit randomness compleixty, we need to multiply `r` by `log |F|`.-/
def LPCP {α : Type} (size : α → ℕ) (ε_c ε_s : ENNReal) (F : Type)
    [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]
    (ℓ q r : ℕ → ℕ) : Set (Set α) :=
  { L | ∃ (V : LPCPVerifier α size F ℓ) (t : Polynomial ℕ), ∀ x,
    RunsInTime (V x) (t.eval (size x)) ∧
    QueryBound (V x) (r (size x)) (q (size x)) ∧
    (x ∈ L → ∃ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ ((randOracle F).impl + (LPCP.proofOracle π).impl) (V x)] ≥ 1 - ε_c) ∧
    (x ∉ L → ∀ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ ((randOracle F).impl + (LPCP.proofOracle π).impl) (V x)] ≤ ε_s) }
