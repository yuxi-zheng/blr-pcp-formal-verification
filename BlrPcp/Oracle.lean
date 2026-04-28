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

instance instEncodableZModOfNeZero (q : ℕ) [NeZero q] : Encodable (ZMod q) :=
  Encodable.ofEquiv (Fin q) (ZMod.finEquiv q).symm

/-- `RunsInTime oa n` means `oa` halts in at most `n` steps. -/
abbrev RunsInTime {ι α : Type} {spec : OracleSpec ι}
    (_oa : OracleComp spec α) (_n : ℕ) : Prop :=
  true -- TODO: look into https://api.cslib.io/docs/Cslib/Algorithms/Lean/TimeM.html
       -- or even https://github.com/Shreyas4991/Algolean

/-- `QueryBound oa q r` means `oa` makes at most `q` proof queries
and at most `r` bits of randomness. -/
abbrev QueryBound {ι α : Type} {proofSpec : OracleSpec ι}
    (oa : OracleComp (unifSpec + proofSpec) α) (q r : ℕ) : Prop :=
  OracleComp.IsQueryBound oa (r, q)
    (fun
      | .inl n, (r, _) => Nat.clog 2 (n + 1) ≤ r
      | .inr _, (_, q) => 0 < q)
    (fun
      | .inl n, (r, q) => (r - Nat.clog 2 (n + 1), q)
      | .inr _, (r, q) => (r, q - 1))

/-- A randomness oracle. -/
abbrev rand : OracleContext ℕ ProbComp where
  spec := unifSpec
  impl := fun n => $ᵗ Fin (n + 1)

namespace PCP
/-- A proof is represented as a function `π : [ℓ] → F`.
`π(q)` is the answer to query `q`. -/
abbrev proof {F : Type} {ℓ : ℕ}
    (π : Fin ℓ → F) : OracleContext (Fin ℓ) ProbComp where
  spec := Fin ℓ →ₒ F
  impl := fun q => return π q

abbrev spec (F : Type) (ℓ : ℕ) : OracleSpec (ℕ ⊕ Fin ℓ) :=
  unifSpec + (Fin ℓ →ₒ F)
end PCP

abbrev PCPVerifier (α : Type) (size : α → ℕ) (F : Type) (ℓ : ℕ → ℕ) : Type :=
  (x : α) → OracleComp (PCP.spec F (ℓ (size x))) Bool

def PCP {α : Type} (size : α → ℕ) (ε_c ε_s : ENNReal) (F : Type)
    [Fintype F] [DecidableEq F] [Inhabited F]
    (ℓ q r : ℕ → ℕ) : Set (Set α) :=
  { L | ∃ (V : PCPVerifier α size F ℓ) (t : Polynomial ℕ), ∀ x,
    RunsInTime (V x) (t.eval (size x)) ∧
    QueryBound (V x) (q (size x)) (r (size x)) ∧
    (x ∈ L → ∃ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ (rand.impl + (PCP.proof π).impl) (V x)] ≥ 1 - ε_c) ∧
    (x ∉ L → ∀ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ (rand.impl + (PCP.proof π).impl) (V x)] ≤ ε_s) }

namespace LPCP
/-- A linear-query proof: a query is a vector `u`,
and the answer is the inner product `⟨π, u⟩`. -/
abbrev proof {F : Type} [Field F] {ℓ : ℕ}
    (π : Fin ℓ → F) : OracleContext (Fin ℓ → F) ProbComp where
  spec := (Fin ℓ → F) →ₒ F
  impl := fun u => return π ⬝ᵥ u

abbrev spec (F : Type) (ℓ : ℕ) : OracleSpec (ℕ ⊕ (Fin ℓ → F)) :=
  unifSpec + ((Fin ℓ → F) →ₒ F)
end LPCP

abbrev LPCPVerifier (α : Type) (size : α → ℕ) (F : Type) [Field F] (ℓ : ℕ → ℕ) : Type :=
  (x : α) → OracleComp (LPCP.spec F (ℓ (size x))) Bool

def LPCP {α : Type} (size : α → ℕ) (ε_c ε_s : ENNReal) (F : Type)
    [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
    (ℓ q r : ℕ → ℕ) : Set (Set α) :=
  { L | ∃ (V : LPCPVerifier α size F ℓ) (t : Polynomial ℕ), ∀ x,
    RunsInTime (V x) (t.eval (size x)) ∧
    QueryBound (V x) (q (size x)) (r (size x)) ∧
    (x ∈ L → ∃ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ (rand.impl + (LPCP.proof π).impl) (V x)] ≥ 1 - ε_c) ∧
    (x ∉ L → ∀ π : Fin (ℓ (size x)) → F,
      Pr[= true | simulateQ (rand.impl + (LPCP.proof π).impl) (V x)] ≤ ε_s) }
