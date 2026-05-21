import BlrPcp.QESATExpSizePCP.PCPs

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
def zmod2RandImpl : QueryImpl (randOracleSpec (ZMod 2)) IO :=
  fun _ => do
    let b ← randFinInclusive 1
    pure (b.val : ZMod 2)

private def randChunkWidth : ℕ := 30

private def randChunkMax : ℕ :=
  2 ^ randChunkWidth - 1

/-- A buffered randomness oracle for `ZMod 2`.

The formal oracle still returns one field element per randomness query. The
buffer only reduces the number of calls to system randomness made by the IO
implementation. -/
def bufferedZMod2RandImpl : IO (QueryImpl (randOracleSpec (ZMod 2)) IO) := do
  let state ← IO.mkRef ((0 : ℕ), (0 : ℕ))
  pure fun _ => do
    let (bits, remaining) ← state.get
    if remaining = 0 then
      let chunk ← randFinInclusive randChunkMax
      state.set (chunk.val / 2, randChunkWidth - 1)
      pure ((chunk.val % 2 : ℕ) : ZMod 2)
    else
      state.set (bits / 2, remaining - 1)
      pure ((bits % 2 : ℕ) : ZMod 2)

/-- Concrete deterministic proof oracle for a PCP table. -/
def proofImpl {ℓ : ℕ} (π : Fin ℓ → ZMod 2) :
    QueryImpl (proofOracleSpec_fin (ZMod 2) ℓ) IO :=
  fun i => pure (π i)

/-- Concrete combined implementation of verifier randomness and a PCP proof oracle. -/
def pcpImpl {ℓ : ℕ} (π : Fin ℓ → ZMod 2) :
    QueryImpl (PCP.fullSpec (ZMod 2) ℓ) IO :=
  zmod2RandImpl + proofImpl π

/-- Concrete combined implementation using buffered system randomness. -/
def bufferedPcpImpl {ℓ : ℕ} (π : Fin ℓ → ZMod 2) :
    IO (QueryImpl (PCP.fullSpec (ZMod 2) ℓ) IO) := do
  let randImpl ← bufferedZMod2RandImpl
  pure (randImpl + proofImpl π)

/-- Run a PCP verifier once using fresh system randomness. -/
def runPCP {ℓ : ℕ} {α : Type} (π : Fin ℓ → ZMod 2)
    (oa : OracleComp (PCP.fullSpec (ZMod 2) ℓ) α) : IO α :=
  simulateQ (pcpImpl π) oa

/-- Run a PCP verifier once using buffered system randomness. -/
def runPCPBuffered {ℓ : ℕ} {α : Type} (π : Fin ℓ → ZMod 2)
    (oa : OracleComp (PCP.fullSpec (ZMod 2) ℓ) α) : IO α := do
  let impl ← bufferedPcpImpl π
  simulateQ impl oa

end SysRand
