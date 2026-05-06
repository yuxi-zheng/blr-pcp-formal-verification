import BlrPcp.Oracle

/-!
# IO-backed randomness for executable tests

This file provides concrete `IO` implementations of the randomness and proof
oracles used by PCP verifiers.
-/

open OracleComp

namespace SysRand

/-- Uniformly sample a `Fin (n + 1)` using Lean's system-backed `IO.rand`. -/
def randFinInclusive (n : ℕ) : IO (Fin (n + 1)) :=
  Fin.ofNat (n + 1) <$> (IO.rand 0 n).toIO

/-- Concrete randomness oracle for `ZMod 2`. -/
def zmod2RandImpl : QueryImpl (randSpec (ZMod 2)) IO :=
  fun _ => do
    let b ← randFinInclusive 1
    pure (b.val : ZMod 2)

/-- Concrete deterministic proof oracle for a PCP table. -/
def proofImpl {ℓ : ℕ} (π : Fin ℓ → ZMod 2) :
    QueryImpl (PCP.proofSpec (ZMod 2) ℓ) IO :=
  fun i => pure (π i)

/-- Concrete combined implementation of verifier randomness and a PCP proof oracle. -/
def pcpImpl {ℓ : ℕ} (π : Fin ℓ → ZMod 2) :
    QueryImpl (PCP.spec (ZMod 2) ℓ) IO :=
  zmod2RandImpl + proofImpl π

/-- Run a PCP verifier once using fresh system randomness. -/
def runPCP {ℓ : ℕ} {α : Type} (π : Fin ℓ → ZMod 2)
    (oa : OracleComp (PCP.spec (ZMod 2) ℓ) α) : IO α :=
  simulateQ (pcpImpl π) oa

end SysRand
