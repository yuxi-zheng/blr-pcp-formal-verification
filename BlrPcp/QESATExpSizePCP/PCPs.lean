import Architect
import BlrPcp.FnFiniteFIelds.Linear
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.OracleComp
import VCVio.OracleComp.OracleContext
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# PCPs

This file defines PCPs and LPCPs in terms of oracle computations, as well as some generic utils.

For BLR, the randomness oracle gives either an element of the field `F` or a scalar, and thus uses a different definition from
the ones defined here. However, the simpler BLR verifier (for `F = {0,1}`) is compatible with `randOracleSpec`, since it
doesn't need to sample from `Fˣ`.

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

/-- Specification (i.e. signature) of oracles that sample a random element from the finite field `F`.
Unit is a type admitting only one value `()`, meaning that the only possible query is `()`.
When a query is made, a field element from `F` ia returned. -/
abbrev randOracleSpec (F : Type) : OracleSpec Unit :=
  Unit →ₒ F

/-- An oracle that samples a random element from the finite field `F`.
It uses the specification `randOracleSpec` defined above,
and the implementation sampled an element u.a.r. with `$ᵗ F` -/
abbrev randOracle (F : Type) [SampleableType F] : OracleContext Unit ProbComp where
  spec := randOracleSpec F
  impl := fun _ => $ᵗ F

/-- Specification (i.e. signature) of proof oracles for ordinary PCPs.
`Fin ℓ` is the type of valid proof-table indices, meaning that a query chooses one position
in a proof of length `ℓ`. When a query is made, a field element from `F` is returned. -/
abbrev proofOracleSpec_fin (F : Type) (ℓ : ℕ) : OracleSpec (Fin ℓ) :=
  Fin ℓ →ₒ F

/-- Specification (i.e. signature) of proof oracles for linear PCPs/BLR.
`Fin ℓ → F` is the type of length-`ℓ` field vectors.
When a vector is queried, a field element from `F` is returned. -/
abbrev proofOracleSpec_fin_vector (F : Type) (ℓ : ℕ) : OracleSpec (Fin ℓ → F) :=
  (Fin ℓ → F) →ₒ F

/-- `RunsInTime oa n` means `oa` halts in at most `n` steps. -/
abbrev RunsInTime {ι α : Type} {spec : OracleSpec ι}
    (_oa : OracleComp spec α) (_n : ℕ) : Prop :=
  true -- TODO: look into https://api.cslib.io/docs/Cslib/Algorithms/Lean/TimeM.html
       -- or even https://github.com/Shreyas4991/Algolean

/-- `QueryBound oa r q` means that the oracle computation/algorithm `oa` makes at most
`r` randomness queries and at most `q` proof queries.
Here `oa` is a computation/algorithm which has access to a combined oracle specification `randOracleSpec + proofSpec`.
Queries to the left side, written `(.inl _)`, are counted as randomness queries; in the
PCP/LPCP applications this is usually `randOracleSpec F`, whose implementation samples field
elements from `F`. Queries to the right side, written `(.inr _)`, are counted as proof queries;
in the PCP/LPCP applications `proofSpec` is a proof-oracle specification, representing access to a proof
of length `ℓ`. -/
abbrev QueryBound {ρ ι α : Type} {randOracleSpec : OracleSpec ρ} {proofSpec : OracleSpec ι}
    (oa : OracleComp (randOracleSpec + proofSpec) α) (r q : ℕ) : Prop :=
  OracleComp.IsQueryBound oa (r, q)
    (fun
      | .inl _, (r, _) => 0 < r
      | .inr _, (_, q) => 0 < q)
    (fun
      | .inl _, (r, q) => (r - 1, q)
      | .inr _, (r, q) => (r, q - 1))

/-- Monotonicity of query bounds.
If `oa` makes at most `r` randomness queries and at most `q` proof queries, then it also
satisfies any larger randomness and proof budgets `r'` and `q'`. -/
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

/-- Query bounds for monadic sequencing.
The computation `oa >>= ob` first runs `oa`, then feeds its output `x` to the continuation
`ob x` and runs that second computation. If `oa` uses at most `(r₁, q₁)` randomness/proof
queries, and every continuation `ob x` uses at most `(r₂, q₂)`, then the whole sequenced
computation uses at most `(r₁ + r₂, q₁ + q₂)`. -/
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

/-- A proof is represented as a function `π : Fin ℓ → F`, i.e. a vector of size `ℓ` with entries in the finite field `F`.
This proof oracle uses the specification `proofOracleSpec_fin F ℓ` defined above: queries are indices `q : Fin ℓ`.
Its implementation answers deterministically with `π q`, the proof-table entry at position `q`. -/
abbrev proofOracle {F : Type} {ℓ : ℕ}
    (π : Fin ℓ → F) : OracleContext (Fin ℓ) ProbComp where
  spec := proofOracleSpec_fin F ℓ
  impl := fun q => return π q

/-- Combined oracle interface for PCP verifiers with access to randomness and to a proof table of length `ℓ`. -/
abbrev fullSpec (F : Type) (ℓ : ℕ) : OracleSpec (Unit ⊕ Fin ℓ) :=
  randOracleSpec F + proofOracleSpec_fin F ℓ

end PCP

/-- Type of ordinary PCP verifiers.
For an input type `α` with size function `size`, field `F`, and proof-length function `ℓ`,
a verifier maps each input `x : α` to an oracle computation with access to randomness and
to a proof table of length `ℓ (size x)`. The computation returns a `Bool`, interpreted as
accept/reject. -/
abbrev PCPVerifier (α : Type) (size : α → ℕ) (F : Type) (ℓ : ℕ → ℕ) : Type :=
  (x : α) → OracleComp (PCP.fullSpec F (ℓ (size x))) Bool

/-- The complexity class PCP. Note that we use a randomness oracle that samples elements from `F`
and not `{0,1}`. To recover the bit randomness complexity, we need to multiply `r` by `log |F|`.-/
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

/-- A proof is represented as a function `π : Fin ℓ → F`, i.e. a vector of size `ℓ` with entries in the finite field `F`.
This linear proof oracle uses the specification `proofOracleSpec_fin_vector F ℓ` defined above: queries are vectors `u : Fin ℓ → F`.
Its implementation answers deterministically with `π ⬝ᵥ u`, the inner product of the proof and the query vector `u`. -/
abbrev proofOracle {F : Type} [Field F] {ℓ : ℕ}
    (π : Fin ℓ → F) : OracleContext (Fin ℓ → F) ProbComp where
  spec := proofOracleSpec_fin_vector F ℓ
  impl := fun u => return π ⬝ᵥ u

/-- Combined oracle specification for LPCP verifiers.
The left side `randOracleSpec F` handles randomness queries: a query `(.inl ())` returns an
element of `F`. The right side `proofOracleSpec_fin_vector F ℓ` handles proof queries:
a query `(.inr u)`, where `u : Fin ℓ → F`, returns the value of the linear proof oracle at `u`.
This is the oracle interface used by LPCP verifiers with access to randomness and to a
linear-query proof of length `ℓ`. -/
abbrev fullSpec (F : Type) (ℓ : ℕ) : OracleSpec (Unit ⊕ (Fin ℓ → F)) :=
  randOracleSpec F + proofOracleSpec_fin_vector F ℓ

end LPCP

/-- Type of linear PCP verifiers.
For an input type `α` with size function `size`, field `F`, and proof-length function `ℓ`,
a verifier maps each input `x : α` to an oracle computation with access to randomness and
to a linear-query proof oracle of length `ℓ (size x)`. The computation returns a `Bool`,
interpreted as accept/reject. -/
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

/-- Sample one scalar from the standard (Unit-indexed) randomness oracle.
This is how the verifier uses the random oracle. -/
def sampleScalar {ι F : Type} {spec : OracleSpec ι} :
    OracleComp (randOracleSpec F + spec) F :=
  liftM (query (spec := randOracleSpec F + spec) (.inl ()))

/-- `sampleScalar` satisfies the query bound `(1, 0)`: it makes one query to the
randomness oracle and no queries to the proof/auxiliary oracle `spec`. -/
lemma sampleScalar_queryBound {ι F : Type} {spec : OracleSpec ι} :
    QueryBound (sampleScalar (F := F) (spec := spec)) 1 0 := by
  simp [sampleScalar, QueryBound]

/-- Auxiliary recursive sampler for fixed-length vectors.
Given a computation `query1` that samples one value of type `F`, `sampleVectorAux query1 m`
runs it `m` times and returns the results as a `Vector F m`. -/
private def sampleVectorAux {ι F : Type} {spec : OracleSpec ι} (query1 : OracleComp spec F) :
    (m : ℕ) → OracleComp spec (Vector F m)
  | 0     => pure #v[]
  | m + 1 => Vector.push <$> sampleVectorAux query1 m <*> query1

/-- Sample `m` independent draws from `query1`, returning the result as `Fin m → F`. -/
def sampleVector {ι F : Type} {spec : OracleSpec ι} (query1 : OracleComp spec F) (m : ℕ) :
    OracleComp spec (Vec F (Fin m)) :=
  (·.get) <$> sampleVectorAux query1 m

/-- Sample `m` independent random field elements using the randomness oracle of `LPCP.fullSpec F N`.
This is how the verifier uses the random oracle. -/
def sampleRandomVector (F : Type) (m N : ℕ) :
    OracleComp (LPCP.fullSpec F N) (Fin m → F) :=
  sampleVector ((liftM (query (spec := LPCP.fullSpec F N) (.inl ())) :
    OracleComp (LPCP.fullSpec F N) F)) m

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]

/- Generic query-bound lemma for `sampleVectorAux`.
If one execution of `query1` uses at most one randomness query and no proof queries, then
running it `m` times through `sampleVectorAux` uses at most `m` randomness queries and no
proof queries. -/
omit [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
private lemma sampleVectorAux_queryBound' {ρ ι F : Type} {randSpec : OracleSpec ρ}
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

/- Query-bound specialization of `sampleVectorAux_queryBound'` to the randomness oracle in
`LPCP.fullSpec F n`. Sampling an auxiliary vector of length `m` makes at most `m`
randomness queries and no proof queries. -/
omit [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
private lemma sampleVectorAux_queryBound (m n : ℕ) :
    QueryBound (sampleVectorAux ((liftM (query (spec := LPCP.fullSpec F n) (.inl ())) :
      OracleComp (LPCP.fullSpec F n) F)) m) m 0 :=
  sampleVectorAux_queryBound' (by simp [QueryBound]) m

/- Generic query-bound lemma for `sampleVector`.
If one execution of `query1` uses at most one randomness query and no proof queries, then
`sampleVector query1 m` uses at most `m` randomness queries and no proof queries. -/
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

/- Query-bound specialization of `sampleVector_queryBound'` to the randomness oracle in
`LPCP.fullSpec F n`. Sampling a vector of length `m` makes at most `m` randomness queries
and no proof queries. -/
omit [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma sampleVector_queryBound (m n : ℕ) :
    QueryBound (sampleVector ((liftM (query (spec := LPCP.fullSpec F n) (.inl ())) :
      OracleComp (LPCP.fullSpec F n) F)) m) m 0 :=
  sampleVector_queryBound' (by simp [QueryBound]) m

/- Generic simulation lemma for `sampleVector`.
If the implementation `impl` interprets one execution of `query1` as a uniform sample from
`F`, then simulating `sampleVector query1 m` produces the uniform distribution on
functions `Fin m → F`. -/
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

/- Simulation lemma for vector sampling in `LPCP.fullSpec`.
When the left randomness oracle is implemented by `randOracle F`, sampling `m` field
elements through `sampleVector` gives the uniform distribution on `Fin m → F`, independent
of the proof-oracle implementation `impl`. -/
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

/- Simulation lemma for `sampleRandomVector`.
Running `sampleRandomVector F m N` with the standard randomness implementation produces the
uniform distribution on `Fin m → F`, regardless of the vector proof-oracle implementation. -/
omit [Field F] [Fintype F] [Inhabited F] in
lemma simulateQ_sampleRandomVector (m N : ℕ)
    (impl : QueryImpl (proofOracleSpec_fin_vector F N) ProbComp) :
    simulateQ ((randOracle F).impl + impl) (sampleRandomVector F m N) =
    ($ᵗ (Fin m → F) : ProbComp (Fin m → F)) := by
  simp [sampleRandomVector, simulateQ_sampleVector m N impl]

/- Query-bound lemma for `sampleRandomVector`.
Sampling a random vector of length `m` from `LPCP.fullSpec F N` uses at most `m`
randomness queries and no proof queries. -/
omit [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma sampleRandomVector_queryBound (m N : ℕ) :
    QueryBound (sampleRandomVector F m N) m 0 := by
  simp [sampleRandomVector, sampleVector_queryBound (F := F) m N]

end OracleUtil
