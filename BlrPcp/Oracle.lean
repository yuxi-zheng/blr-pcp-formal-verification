import Architect
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.OracleComp
import VCVio.OracleComp.OracleContext
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Oracle computations

This file defines PCPs and LPCPs in terms of oracle computations.

## Main declarations

- `PCP`, `LPCP`: PCP and linear PCP language classes with query and randomness bounds.
-/

open OracleComp
open scoped Matrix

instance instEncodableZModOfNeZero (q : ℕ) [NeZero q] : Encodable (ZMod q) :=
  Encodable.ofEquiv (Fin q) (ZMod.finEquiv q).symm

abbrev RandOracleSpec : OracleSpec ℕ :=
  unifSpec

abbrev RandOracle : OracleContext ℕ ProbComp where
  spec := RandOracleSpec
  impl := fun n => $ᵗ Fin (n + 1)

/-- A proof is represented as a function `π : [ℓ] → F`.
`π(q)` is the answer to query `q`. -/
abbrev ProofOracleSpec (F : Type) (ℓ : ℕ) : OracleSpec (Fin ℓ) :=
  Fin ℓ →ₒ F

abbrev ProofOracle (proof : Fin ℓ → F) : OracleContext (Fin ℓ) ProbComp where
  spec := ProofOracleSpec F ℓ
  impl := fun q => pure (proof q)

abbrev PCPOracleSpec (F : Type) (ℓ : ℕ) : OracleSpec (ℕ ⊕ Fin ℓ) :=
  RandOracleSpec + ProofOracleSpec F ℓ

abbrev PCPVerifier (α : Type) (size : α → ℕ) (F : Type) (ℓ : ℕ → ℕ) : Type :=
  (x : α) → OracleComp (PCPOracleSpec F (ℓ (size x))) Bool

/-- TODO: Runtime bound of a computation `V(x)` -/
def RunsInTime {α : Type} {size : α → ℕ} {F : Type} {ℓ : ℕ → ℕ}
    (_ : PCPVerifier α size F ℓ) (_ : α) (_ : ℕ) : Prop :=
  true

/-- `PCPQueryBound oa q r` means `oa` makes at most `q` proof queries
and at most `r` randomness queries. -/
def PCPQueryBound {F α : Type} {ℓ : ℕ}
    (oa : OracleComp (PCPOracleSpec F ℓ) α) (q r : ℕ) : Prop :=
  IsQueryBound oa (q, r)
    (fun
      | .inl n, (_, r) => Nat.clog 2 (n + 1) ≤ r
      | .inr _, (q, _) => 0 < q)
    (fun
      | .inl n, (q, r) => (q, r - Nat.clog 2 (n + 1))
      | .inr _, (q, r) => (q - 1, r))

def PCP {α : Type} (size : α → ℕ) (ε_c ε_s : ENNReal) (F : Type)
    [Fintype F] [DecidableEq F] [Inhabited F]
    (ℓ q r : ℕ → ℕ) : Set (Set α) :=
  { L | ∃ (V : PCPVerifier α size F ℓ) (t : Polynomial ℕ), ∀ x,
    RunsInTime V x (t.eval (size x)) ∧
    PCPQueryBound (V x) (q (size x)) (r (size x)) ∧
    (x ∈ L → ∃ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ (RandOracle.impl + (ProofOracle π).impl) (V x)] ≥ 1 - ε_c) ∧
    (x ∉ L → ∀ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ (RandOracle.impl + (ProofOracle π).impl) (V x)] ≤ ε_s) }

/-- A linear-query proof oracle: a query is a vector `u`,
and the answer is the inner product `⟨π, u⟩`. -/
abbrev LinProofOracleSpec (F : Type) [Field F] (ℓ : ℕ) : OracleSpec (Fin ℓ → F) :=
  (Fin ℓ → F) →ₒ F

abbrev LinProofOracle {F : Type} [Field F] {ℓ : ℕ}
    (π : Fin ℓ → F) : OracleContext (Fin ℓ → F) ProbComp where
  spec := LinProofOracleSpec F ℓ
  impl := fun u => pure (π ⬝ᵥ u)

abbrev LPCPOracleSpec (F : Type) [Field F] (ℓ : ℕ) : OracleSpec (ℕ ⊕ (Fin ℓ → F)) :=
  RandOracleSpec + LinProofOracleSpec F ℓ

abbrev LPCPVerifier (α : Type) (size : α → ℕ) (F : Type) [Field F]
    (ℓ : ℕ → ℕ) : Type :=
  (x : α) → OracleComp (LPCPOracleSpec F (ℓ (size x))) Bool

/-- TODO: Avoid code duplication by defining runtime for generic OracleComp -/
def LRunsInTime {α : Type} {size : α → ℕ} {F : Type} {ℓ : ℕ → ℕ} [Field F]
    (_ : LPCPVerifier α size F ℓ) (_ : α) (_ : ℕ) : Prop :=
  true

-- TODO: Avoid code duplication
/-- `LPCPQueryBound oa q r` means `oa` makes at most `q` proof queries
and at most `r` randomness queries. -/
def LPCPQueryBound {F α : Type} {ℓ : ℕ} [Field F]
    (oa : OracleComp (LPCPOracleSpec F ℓ) α) (q r : ℕ) : Prop :=
  IsQueryBound oa (q, r)
    (fun
      | .inl n, (_, r) => Nat.clog 2 (n + 1) ≤ r
      | .inr _, (q, _) => 0 < q)
    (fun
      | .inl n, (q, r) => (q, r - Nat.clog 2 (n + 1))
      | .inr _, (q, r) => (q - 1, r))

def LPCP {α : Type} (size : α → ℕ) (ε_c ε_s : ENNReal) (F : Type)
    [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
    (ℓ q r : ℕ → ℕ) : Set (Set α) :=
  { L | ∃ (V : LPCPVerifier α size F ℓ) (t : Polynomial ℕ), ∀ x,
    LRunsInTime V x (t.eval (size x)) ∧
    LPCPQueryBound (V x) (q (size x)) (r (size x)) ∧
    (x ∈ L → ∃ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ (RandOracle.impl + (LinProofOracle π).impl) (V x)] ≥ 1 - ε_c) ∧
    (x ∉ L → ∀ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ (RandOracle.impl + (LinProofOracle π).impl) (V x)] ≤ ε_s) }
