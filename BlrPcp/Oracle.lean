import Architect
import BlrPcp.FnFiniteFIelds.Linear
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.OracleComp
import VCVio.OracleComp.OracleContext
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Oracle computations

This file defines PCPs and LPCPs in terms of oracle computations, as well as some genetic utils.

For BLR, the randomness oracle gives either an element of field F or a scalar, and thus uses a different definition from
the ones defined here.

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

namespace OracleUtil

def sampleVectorAux {ι F : Type} {spec : OracleSpec ι} (query1 : OracleComp spec F) :
    (m : ℕ) → OracleComp spec (Vector F m)
  | 0     => pure #v[]
  | m + 1 => Vector.push <$> sampleVectorAux query1 m <*> query1

/-- Sample `m` independent draws from `query1`, returning the result as `Fin m → F`. -/
def sampleVector {ι F : Type} {spec : OracleSpec ι} (query1 : OracleComp spec F) (m : ℕ) :
    OracleComp spec (Vec F (Fin m)) :=
  (·.get) <$> sampleVectorAux query1 m

/-- Sample one field element from the standard (Unit-indexed) randomness oracle. -/
def sampleField {ι F : Type} {spec : OracleSpec ι} :
    OracleComp (randOracleSpec F + spec) F :=
  liftM (query (spec := randOracleSpec F + spec) (.inl ()))

lemma sampleField_queryBound {ι F : Type} {spec : OracleSpec ι} :
    QueryBound (sampleField (F := F) (spec := spec)) 1 0 := by
  simp [sampleField, QueryBound]

/-- Sample `m` independent random field elements using the randomness oracle of
`fullSpec_fin_vector F N`. -/
def sampleRandomVector (F : Type) [SampleableType F] (m N : ℕ) :
    OracleComp (fullSpec_fin_vector F N) (Fin m → F) :=
  sampleVector ((liftM (query (spec := fullSpec_fin_vector F N) (.inl ())) :
    OracleComp (fullSpec_fin_vector F N) F)) m

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]

omit [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma sampleVectorAux_queryBound' {ρ ι F : Type} {randSpec : OracleSpec ρ}
    {proofSpec : OracleSpec ι}
    {query1 : OracleComp (randSpec + proofSpec) F}
    (hq : QueryBound query1 1 0) : ∀ m,
    QueryBound (sampleVectorAux query1 m) m 0 := by
  intro m
  induction m with
  | zero => simp [sampleVectorAux, QueryBound]
  | succ m ih =>
      simp only [sampleVectorAux, seq_eq_bind_map]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        queryBound_bind ih fun _ => by simpa [QueryBound] using hq

omit [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma sampleVectorAux_queryBound (m n : ℕ) :
    QueryBound (sampleVectorAux ((liftM (query (spec := LPCP.fullSpec F n) (.inl ())) :
      OracleComp (LPCP.fullSpec F n) F)) m) m 0 :=
  sampleVectorAux_queryBound' (by simp [QueryBound]) m

omit [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma sampleVector_queryBound' {ρ ι F : Type} {randSpec : OracleSpec ρ}
    {proofSpec : OracleSpec ι}
    {query1 : OracleComp (randSpec + proofSpec) F}
    (hq : QueryBound query1 1 0) (m : ℕ) :
    QueryBound (sampleVector query1 m) m 0 := by
  simp only [sampleVector, map_eq_bind_pure_comp]
  exact queryBound_mono
    (queryBound_bind (q₂ := 0) (r₂ := 0) (sampleVectorAux_queryBound' hq m)
      fun _ => by simp [QueryBound])
    (by omega) (by omega)

omit [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma sampleVector_queryBound (m n : ℕ) :
    QueryBound (sampleVector ((liftM (query (spec := LPCP.fullSpec F n) (.inl ())) :
      OracleComp (LPCP.fullSpec F n) F)) m) m 0 :=
  sampleVector_queryBound' (by simp [QueryBound]) m

omit [Field F] [Fintype F] [Inhabited F] in
lemma simulateQ_sampleVector' {ρ ι F : Type} {randSpec : OracleSpec ρ}
    {proofSpec : OracleSpec ι} [DecidableEq F] [Fintype F] [SampleableType F]
    (impl : QueryImpl (randSpec + proofSpec) ProbComp)
    {query1 : OracleComp (randSpec + proofSpec) F}
    (h : simulateQ impl query1 = $ᵗ F) (m : ℕ) :
    simulateQ impl (sampleVector query1 m) = $ᵗ (Fin m → F) := by
  simp only [sampleVector]
  suffices h' : ∀ m, simulateQ impl (sampleVectorAux query1 m) = $ᵗ Vector F m by
    simp only [simulateQ_map, h' m]; rfl
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [sampleVectorAux, simulateQ_seq, simulateQ_map]
      rw [ih, h]
      rfl

omit [Field F] [Fintype F] [Inhabited F] in
lemma simulateQ_sampleVector (m n : ℕ)
    (impl : QueryImpl ((Fin n → F) →ₒ F) ProbComp) :
    simulateQ ((randOracle F).impl + impl)
        (sampleVector ((liftM (query (spec := LPCP.fullSpec F n) (.inl ())) :
          OracleComp (LPCP.fullSpec F n) F)) m) =
      ($ᵗ (Fin m → F) : ProbComp (Fin m → F)) := by
  simp only [sampleVector]
  suffices h : ∀ m, simulateQ ((randOracle F).impl + impl)
      (sampleVectorAux ((liftM (query (spec := LPCP.fullSpec F n) (.inl ())) :
        OracleComp (LPCP.fullSpec F n) F)) m) =
      ($ᵗ Vector F m : ProbComp (Vector F m)) by
    simp only [simulateQ_map, h m]; rfl
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [sampleVectorAux, simulateQ_seq, simulateQ_map, simulateQ_query,
        OracleQuery.cont_query, id_map, OracleQuery.input_query]
      change Vector.push <$> simulateQ ((randOracle F).impl + impl)
          (sampleVectorAux ((liftM (query (spec := LPCP.fullSpec F n) (.inl ())) :
            OracleComp (LPCP.fullSpec F n) F)) m) <*>
          ($ᵗ F) = (instSampleableTypeVector F (m + 1)).selectElem
      rw [ih]
      rfl

omit [Field F] [Fintype F] [Inhabited F] in
lemma simulateQ_sampleRandomVector (m N : ℕ)
    (impl : QueryImpl (proofOracleSpec_fin_vector F N) ProbComp) :
    simulateQ ((randOracle F).impl + impl) (sampleRandomVector F m N) =
    ($ᵗ (Fin m → F) : ProbComp (Fin m → F)) := by
  simp [sampleRandomVector, simulateQ_sampleVector m N impl]

omit [Field F] [Fintype F] [DecidableEq F] [Inhabited F] in
lemma sampleRandomVector_queryBound (m N : ℕ) :
    QueryBound (sampleRandomVector F m N) m 0 := by
  simp [sampleRandomVector, sampleVector_queryBound (F := F) m N]

end OracleUtil
