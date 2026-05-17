import BlrPcp.Problems.QESAT
import BlrPcp.Test.SysRand

/-!
# Component benchmarks for the concrete QESAT PCP verifier

This executable decomposes the final QESAT PCP verifier into the `OracleComp`
components it runs and times each component with the same concrete IO-backed
randomness/proof-oracle style used by the executable tests.

Run with:

```
lake exe qesat_component_bench
```
-/

open CPoly CMvPolynomial
open OracleComp
open scoped Matrix

namespace QESATComponentBench

abbrev F := ZMod 2

def shiftCount : ℕ :=
  LPCPToPCP.numShifts (fun _ => 4) 0

def proofDim (vars : ℕ) : ℕ :=
  vars + vars * vars

def firstVarEqOneN (vars : ℕ) : CMvPolynomial vars F :=
  if h : 0 < vars then
    CMvPolynomial.X (R := F) ⟨0, h⟩ + CMvPolynomial.C (n := vars) (R := F) 1
  else
    CMvPolynomial.C (n := vars) (R := F) 0

def repeatedSatInstanceN (vars count : ℕ) : List (CMvPolynomial vars F) :=
  List.replicate count (firstVarEqOneN vars)

def allOnes {vars : ℕ} : Fin vars → F :=
  fun _ => 1

def tensorSquareOnes {vars : ℕ} : Fin vars × Fin vars → F :=
  fun _ => 1

def lpcpHonestProof {vars : ℕ} : Fin (proofDim vars) → F :=
  TENSORQ.honestProof (F := F) (allOnes, tensorSquareOnes)

def pcpHonestProof {vars : ℕ} : Fin (2 ^ proofDim vars) → F :=
  (Vector.ofFn (LPCPToPCP.encodedProof lpcpHonestProof)).get

def paddedHonestProof {vars : ℕ} (x : List (CMvPolynomial vars F)) :
    Fin (2 ^ QESAT.size x) → F :=
  fun j =>
    if h : j.val < 2 ^ proofDim vars then
      pcpHonestProof ⟨j.val, h⟩
    else
      0

def lpcpProofImpl {ℓ : ℕ} (π : Fin ℓ → F) :
    QueryImpl (proofOracleSpec_fin_vector F ℓ) IO :=
  fun u => pure (π ⬝ᵥ u)

def lpcpImpl {ℓ : ℕ} (π : Fin ℓ → F) :
    IO (QueryImpl (LPCP.fullSpec F ℓ) IO) := do
  let randImpl ← SysRand.bufferedZMod2RandImpl
  pure (randImpl + lpcpProofImpl π)

def runLPCPBuffered {ℓ : ℕ} {α : Type} (π : Fin ℓ → F)
    (oa : OracleComp (LPCP.fullSpec F ℓ) α) : IO α := do
  let impl ← lpcpImpl π
  simulateQ impl oa

def padImplBench {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) :
    QueryImpl (PCP.fullSpec F n₀) (OracleComp (PCP.fullSpec F n₁))
  | .inl () => query (spec := PCP.fullSpec F n₁) (.inl ())
  | .inr i => query (spec := PCP.fullSpec F n₁) (.inr (Fin.castLE h i))

def zeroShifts (n t : ℕ) : Fin t → Fin n → F :=
  fun _ _ => 0

def firstVarMatrix (rows vars : ℕ) : Matrix (Fin rows) (Fin (proofDim vars)) F :=
  fun _ j => if j.val = 0 then 1 else 0

def firstVarTarget (rows : ℕ) : Fin rows → F :=
  fun _ => 1

def lineqComp (vars rows : ℕ) :
    OracleComp (LPCP.fullSpec F (proofDim vars)) Bool :=
  LINEQ.verifier (F := F)
    (firstVarMatrix rows vars, firstVarTarget rows)

def tensorSelfComp (vars : ℕ) :
    OracleComp (LPCP.fullSpec F (proofDim vars)) Bool := do
  let s ← OracleUtil.sampleRandomVector F vars (proofDim vars)
  let t ← OracleUtil.sampleRandomVector F vars (proofDim vars)
  let yA : F ← query (spec := LPCP.fullSpec F (proofDim vars)) (.inr (TENSORQ.queryA s))
  let yA' : F ← query (spec := LPCP.fullSpec F (proofDim vars)) (.inr (TENSORQ.queryA t))
  let yB : F ← query (spec := LPCP.fullSpec F (proofDim vars)) (.inr (TENSORQ.queryB s t))
  pure (yB = yA * yA')

def qesatLpcpComp (vars rows : ℕ) :
    OracleComp (LPCP.fullSpec F (proofDim vars)) Bool :=
  QESAT.verifier (n := vars) (repeatedSatInstanceN vars rows)

def decodedLineqComp (vars rows : ℕ) :
    OracleComp (PCP.fullSpec F (2 ^ proofDim vars)) Bool :=
  simulateQ (LPCPToPCP.decodedImpl (zeroShifts (proofDim vars) shiftCount))
    (lineqComp vars rows)

def decodedTensorComp (vars : ℕ) :
    OracleComp (PCP.fullSpec F (2 ^ proofDim vars)) Bool :=
  simulateQ (LPCPToPCP.decodedImpl (zeroShifts (proofDim vars) shiftCount))
    (tensorSelfComp vars)

def decodedQESATLpcpComp (vars rows : ℕ) :
    OracleComp (PCP.fullSpec F (2 ^ proofDim vars)) Bool :=
  simulateQ (LPCPToPCP.decodedImpl (zeroShifts (proofDim vars) shiftCount))
    (qesatLpcpComp vars rows)

def decodedQESATLpcpSampledShiftsComp (vars rows : ℕ) :
    OracleComp (PCP.fullSpec F (2 ^ proofDim vars)) Bool := do
  let shifts ← LPCPToPCP.sampleShifts (proofDim vars) shiftCount
  simulateQ (LPCPToPCP.decodedImpl shifts) (qesatLpcpComp vars rows)

def blrComp (vars : ℕ) :
    OracleComp (PCP.fullSpec F (2 ^ proofDim vars)) Bool :=
  simulateQ (LPCPToPCP.truthTableImpl (proofDim vars))
    (BLR.basicVerifier (F := F) (n := proofDim vars))

def sampleShiftsComp (vars : ℕ) :
    OracleComp (PCP.fullSpec F (2 ^ proofDim vars))
      (Fin shiftCount → Fin (proofDim vars) → F) :=
  LPCPToPCP.sampleShifts (proofDim vars) shiftCount

private def sampledShiftIndexSum {n : ℕ} :
    (t : ℕ) → (Fin t → Fin n → F) → (Fin n → F) → ℕ
  | 0, _shifts, _a => 0
  | t + 1, shifts, a =>
      (LPCPToPCP.truthTableIndex n (fun j => a j + shifts 0 j)).val +
        (LPCPToPCP.truthTableIndex n (shifts 0)).val +
        sampledShiftIndexSum t (fun i => shifts i.succ) a

private def sampledShiftAccessSum {n : ℕ} :
    (t : ℕ) → (Fin t → Fin n → F) → ℕ
  | 0, _shifts => 0
  | t + 1, shifts =>
      (∑ j : Fin n, if shifts 0 j = 1 then 1 else 0) +
        sampledShiftAccessSum t (fun i => shifts i.succ)

def sampledShiftIndexComp (vars : ℕ) :
    OracleComp (PCP.fullSpec F (2 ^ proofDim vars)) ℕ := do
  let shifts ← LPCPToPCP.sampleShifts (proofDim vars) shiftCount
  pure (sampledShiftIndexSum shiftCount shifts (fun _ => 1))

def sampledShiftAccessComp (vars : ℕ) :
    OracleComp (PCP.fullSpec F (2 ^ proofDim vars)) ℕ := do
  let shifts ← LPCPToPCP.sampleShifts (proofDim vars) shiftCount
  pure (sampledShiftAccessSum shiftCount shifts)

def decodedSingleQueryComp (vars : ℕ) :
    OracleComp (PCP.fullSpec F (2 ^ proofDim vars)) F :=
  LPCPToPCP.decodedLinearQuery
    (zeroShifts (proofDim vars) shiftCount)
    (fun _ => 1)

def decodedSingleQueryCompT (vars t : ℕ) :
    OracleComp (PCP.fullSpec F (2 ^ proofDim vars)) F :=
  LPCPToPCP.decodedLinearQuery
    (zeroShifts (proofDim vars) t)
    (fun _ => 1)

def decodedSingleQuerySampledShiftsComp (vars : ℕ) :
    OracleComp (PCP.fullSpec F (2 ^ proofDim vars)) F := do
  let shifts ← LPCPToPCP.sampleShifts (proofDim vars) shiftCount
  LPCPToPCP.decodedLinearQuery shifts (fun _ => 1)

def decodedSingleQuerySampledShiftsCompT (vars t : ℕ) :
    OracleComp (PCP.fullSpec F (2 ^ proofDim vars)) F := do
  let shifts ← LPCPToPCP.sampleShifts (proofDim vars) t
  LPCPToPCP.decodedLinearQuery shifts (fun _ => 1)

def decodedCorrectionStepComp (vars : ℕ) :
    OracleComp (PCP.fullSpec F (2 ^ proofDim vars)) F := do
  let y₁ : F ← query (spec := PCP.fullSpec F (2 ^ proofDim vars))
    (.inr (LPCPToPCP.truthTableIndex (proofDim vars) (fun _ => (1 : F))))
  let y₀ : F ← query (spec := PCP.fullSpec F (2 ^ proofDim vars))
    (.inr (LPCPToPCP.truthTableIndex (proofDim vars) (fun _ => (0 : F))))
  pure (y₁ - y₀)

def fixedIndexCorrectionLoopCompT (vars t : ℕ) :
    OracleComp (PCP.fullSpec F (2 ^ proofDim vars)) F := do
  let ys : Fin t → F ← Fin.mOfFn t fun _ => do
    let y₁ : F ← query (spec := PCP.fullSpec F (2 ^ proofDim vars))
      (.inr (Fin.ofNat (2 ^ proofDim vars) 0))
    let y₀ : F ← query (spec := PCP.fullSpec F (2 ^ proofDim vars))
      (.inr (Fin.ofNat (2 ^ proofDim vars) 0))
    pure (y₁ - y₀)
  pure (LPCPToPCP.pluralityZMod2 ys)

def randomBitComp (vars : ℕ) :
    OracleComp (PCP.fullSpec F (2 ^ proofDim vars)) F := do
  let b : F ← query (spec := PCP.fullSpec F (2 ^ proofDim vars)) (.inl ())
  pure b

def encodedProofQueryComp (vars : ℕ) :
    OracleComp (PCP.fullSpec F (2 ^ proofDim vars)) F := do
  let y : F ← query (spec := PCP.fullSpec F (2 ^ proofDim vars))
    (.inr (Fin.ofNat (2 ^ proofDim vars) 0))
  pure y

def paddedProofQueryComp {vars : ℕ} (x : List (CMvPolynomial vars F)) :
    OracleComp (PCP.fullSpec F (2 ^ QESAT.size x)) F := do
  let y : F ← query (spec := PCP.fullSpec F (2 ^ QESAT.size x))
    (.inr (Fin.ofNat (2 ^ QESAT.size x) 0))
  pure y

def pcpRoundComp (vars rows : ℕ) :
    OracleComp (PCP.fullSpec F (2 ^ proofDim vars)) Bool :=
  (LPCPToPCP.verifier (α := List (CMvPolynomial vars F))
    QESAT.size (fun _ => proofDim vars) (fun _ => 4)
    (QESAT.verifier (n := vars))) (repeatedSatInstanceN vars rows)

def paddedRoundComp {vars : ℕ} (x : List (CMvPolynomial vars F)) :
    OracleComp (PCP.fullSpec F (2 ^ QESAT.size x)) Bool :=
  if hlen : 2 ^ proofDim vars ≤ 2 ^ QESAT.size x then
    simulateQ (padImplBench hlen)
      ((LPCPToPCP.verifier (α := List (CMvPolynomial vars F))
        QESAT.size (fun _ => proofDim vars) (fun _ => 4)
        (QESAT.verifier (n := vars))) x)
  else
    pure true

def finalRepeatedComp {vars : ℕ} (x : List (CMvPolynomial vars F)) :
    OracleComp (PCP.fullSpec F (2 ^ QESAT.size x)) Bool := do
  let xs ← OracleComp.replicate 6 (paddedRoundComp x)
  pure (xs.all id)

structure BenchRow where
  component : String
  vars : ℕ
  rows : ℕ
  dimension : ℕ
  trials : ℕ
  accepts : ℕ
  elapsedMs : ℕ

def BenchRow.avgUs (row : BenchRow) : ℕ :=
  if row.trials = 0 then 0 else row.elapsedMs * 1000 / row.trials

def BenchRow.tsvHeader : String :=
  "component\tvars\trows\tproof_dim\ttrials\taccepts\telapsed_ms\tavg_us"

def BenchRow.toTsv (row : BenchRow) : String :=
  s!"{row.component}\t{row.vars}\t{row.rows}\t{row.dimension}\t{row.trials}\t" ++
    s!"{row.accepts}\t{row.elapsedMs}\t{row.avgUs}"

def timeBoolTrials (trials : ℕ) (trial : IO Bool) : IO (ℕ × ℕ) := do
  let start ← IO.monoMsNow
  let mut accepts := 0
  for _ in List.range trials do
    if ← trial then
      accepts := accepts + 1
  let stop ← IO.monoMsNow
  pure (accepts, stop - start)

def timeUnitTrials (trials : ℕ) (trial : IO Unit) : IO ℕ := do
  let start ← IO.monoMsNow
  for _ in List.range trials do
    trial
  let stop ← IO.monoMsNow
  pure (stop - start)

def boolRow (component : String) (vars rows trials : ℕ) (trial : IO Bool) :
    IO BenchRow := do
  let (accepts, elapsed) ← timeBoolTrials trials trial
  let dim := proofDim vars
  pure (BenchRow.mk component vars rows dim trials accepts elapsed)

def unitRow (component : String) (vars rows trials : ℕ) (trial : IO Unit) :
    IO BenchRow := do
  let elapsed ← timeUnitTrials trials trial
  let dim := proofDim vars
  pure (BenchRow.mk component vars rows dim trials 0 elapsed)

def runPcpComp {N : ℕ} {α : Type} (π : Fin N → F)
    (oa : OracleComp (PCP.fullSpec F N) α) : IO α :=
  SysRand.runPCPBuffered π oa

structure TrialPlan where
  atomic : ℕ
  base : ℕ
  round : ℕ
  final : ℕ
  heavy : ℕ

def trialPlan (vars rows : ℕ) : TrialPlan :=
  if vars ≤ 1 && rows = 1 then
    { atomic := 200, base := 20, round := 1, final := 0, heavy := 0 }
  else if vars ≤ 2 && rows ≤ 10 then
    { atomic := 100, base := 10, round := 1, final := 0, heavy := 0 }
  else if vars ≤ 3 && rows = 1 then
    { atomic := 50, base := 5, round := 1, final := 0, heavy := 0 }
  else if vars ≤ 4 && rows = 1 then
    { atomic := 25, base := 2, round := 1, final := 0, heavy := 0 }
  else if rows ≤ 100 then
    { atomic := 25, base := 2, round := 1, final := 0, heavy := 0 }
  else
    { atomic := 10, base := 1, round := 1, final := 0, heavy := 0 }

def emitRow (row : BenchRow) : IO Unit := do
  IO.println row.toTsv
  let stdout ← IO.getStdout
  stdout.flush

def emitBoolRow (component : String) (vars rows trials : ℕ) (trial : IO Bool) :
    IO Unit := do
  if trials = 0 then
    pure ()
  else
    emitRow (← boolRow component vars rows trials trial)

def emitUnitRow (component : String) (vars rows trials : ℕ) (trial : IO Unit) :
    IO Unit := do
  if trials = 0 then
    pure ()
  else
    emitRow (← unitRow component vars rows trials trial)

def runRowsFor (vars rows : ℕ) : IO Unit := do
  let x := repeatedSatInstanceN vars rows
  let plan := trialPlan vars rows
  emitUnitRow "pure.truthTableIndex" vars rows plan.atomic do
    let _ := LPCPToPCP.truthTableIndex (proofDim vars) (fun _ => (1 : F))
    pure ()
  emitUnitRow "pure.truthTableVector" vars rows plan.atomic do
    let _ := LPCPToPCP.truthTableVector (proofDim vars)
      (Fin.ofNat (2 ^ proofDim vars) 0)
    pure ()
  emitUnitRow "pure.encodedProofEval" vars rows plan.atomic do
    let _ := pcpHonestProof (vars := vars) (Fin.ofNat (2 ^ proofDim vars) 0)
    pure ()
  emitUnitRow "pure.linearProofDot" vars rows plan.atomic do
    let _ := lpcpHonestProof (vars := vars) ⬝ᵥ (fun _ => (1 : F))
    pure ()
  emitUnitRow "pure.paddingLengthPow" vars rows plan.atomic do
    let _ := 2 ^ QESAT.size x
    pure ()
  emitUnitRow "pure.paddingBoundCheck" vars rows plan.atomic do
    let _ := decide (2 ^ proofDim vars ≤ 2 ^ QESAT.size x)
    pure ()
  emitBoolRow "atomic.randomBitQuery" vars rows plan.atomic do
    let y ← runPcpComp (pcpHonestProof (vars := vars)) (randomBitComp vars)
    pure (y = 0 ∨ y = 1)
  emitBoolRow "atomic.encodedProofQuery" vars rows plan.atomic do
    let y ← runPcpComp (pcpHonestProof (vars := vars)) (encodedProofQueryComp vars)
    pure (y = 0 ∨ y = 1)
  emitBoolRow "atomic.paddedProofQuery" vars rows plan.atomic do
    let y ← runPcpComp (paddedHonestProof x) (paddedProofQueryComp x)
    pure (y = 0 ∨ y = 1)
  emitBoolRow "PCP.decodedCorrectionStep" vars rows plan.base do
    let y ← runPcpComp (pcpHonestProof (vars := vars)) (decodedCorrectionStepComp vars)
    pure (y = 0 ∨ y = 1)
  emitBoolRow "PCP.decodedSingleQuery.t1" vars rows plan.round do
    let y ← runPcpComp (pcpHonestProof (vars := vars)) (decodedSingleQueryCompT vars 1)
    pure (y = 0 ∨ y = 1)
  emitBoolRow "PCP.decodedSingleQuery.t8" vars rows plan.round do
    let y ← runPcpComp (pcpHonestProof (vars := vars)) (decodedSingleQueryCompT vars 8)
    pure (y = 0 ∨ y = 1)
  emitBoolRow "LPCP.rawLineq" vars rows plan.base do
    runLPCPBuffered (lpcpHonestProof (vars := vars)) (lineqComp vars rows)
  emitBoolRow "LPCP.rawTensor" vars rows plan.base do
    runLPCPBuffered (lpcpHonestProof (vars := vars)) (tensorSelfComp vars)
  emitBoolRow "LPCP.rawQESAT" vars rows plan.base do
    runLPCPBuffered (lpcpHonestProof (vars := vars)) (qesatLpcpComp vars rows)
  emitBoolRow "PCP.BLRPrecheck" vars rows plan.base do
    runPcpComp (pcpHonestProof (vars := vars)) (blrComp vars)
  emitUnitRow "PCP.sampleShifts" vars rows plan.base do
    let _ ← runPcpComp (pcpHonestProof (vars := vars)) (sampleShiftsComp vars)
    pure ()
  emitBoolRow "PCP.decodedSingleQuery" vars rows plan.heavy do
    let y ← runPcpComp (pcpHonestProof (vars := vars)) (decodedSingleQueryComp vars)
    pure (y = 0 ∨ y = 1)
  emitBoolRow "PCP.decodedLineq" vars rows plan.heavy do
    runPcpComp (pcpHonestProof (vars := vars)) (decodedLineqComp vars rows)
  emitBoolRow "PCP.decodedTensor" vars rows plan.heavy do
    runPcpComp (pcpHonestProof (vars := vars)) (decodedTensorComp vars)
  emitBoolRow "PCP.decodedQESAT" vars rows plan.heavy do
    runPcpComp (pcpHonestProof (vars := vars)) (decodedQESATLpcpComp vars rows)
  emitBoolRow "PCP.preRound" vars rows plan.heavy do
    runPcpComp (pcpHonestProof (vars := vars)) (pcpRoundComp vars rows)
  emitBoolRow "PCP.paddedPreRound" vars rows plan.heavy do
    runPcpComp (paddedHonestProof x) (paddedRoundComp x)
  emitBoolRow "PCP.finalRepeatedPadded" vars rows plan.final do
    runPcpComp (paddedHonestProof x) (finalRepeatedComp x)
  emitUnitRow "pure.degreeCheck" vars rows plan.base do
    let _ := decide (∀ p ∈ x, p.totalDegree ≤ 2)
    pure ()

def defaultCases : List (ℕ × ℕ) :=
  [(1, 1), (2, 1), (3, 1), (4, 1), (2, 10), (2, 100), (2, 500)]

def wideCases : List (ℕ × ℕ) :=
  defaultCases ++ [(5, 1), (2, 1000)]

def runTsv (cases : List (ℕ × ℕ)) : IO Unit := do
  IO.println BenchRow.tsvHeader
  for (vars, rows) in cases do
    runRowsFor vars rows

def runOneComponent (component : String) (vars rows trials : ℕ) : IO UInt32 := do
  let x := repeatedSatInstanceN vars rows
  IO.println BenchRow.tsvHeader
  match component with
  | "blr" =>
      emitBoolRow "PCP.BLRPrecheck" vars rows trials do
        runPcpComp (pcpHonestProof (vars := vars)) (blrComp vars)
      pure 0
  | "decoded-step" =>
      emitBoolRow "PCP.decodedCorrectionStep" vars rows trials do
        let y ← runPcpComp (pcpHonestProof (vars := vars)) (decodedCorrectionStepComp vars)
        pure (y = 0 ∨ y = 1)
      pure 0
  | "decoded-t1" =>
      emitBoolRow "PCP.decodedSingleQuery.t1" vars rows trials do
        let y ← runPcpComp (pcpHonestProof (vars := vars)) (decodedSingleQueryCompT vars 1)
        pure (y = 0 ∨ y = 1)
      pure 0
  | "decoded-t8" =>
      emitBoolRow "PCP.decodedSingleQuery.t8" vars rows trials do
        let y ← runPcpComp (pcpHonestProof (vars := vars)) (decodedSingleQueryCompT vars 8)
        pure (y = 0 ∨ y = 1)
      pure 0
  | "decoded-single" =>
      emitBoolRow "PCP.decodedSingleQuery" vars rows trials do
        let y ← runPcpComp (pcpHonestProof (vars := vars)) (decodedSingleQueryComp vars)
        pure (y = 0 ∨ y = 1)
      pure 0
  | "decoded-single-sampled" =>
      emitBoolRow "PCP.decodedSingleQuery.sampledShifts" vars rows trials do
        let y ← runPcpComp (pcpHonestProof (vars := vars))
          (decodedSingleQuerySampledShiftsComp vars)
        pure (y = 0 ∨ y = 1)
      pure 0
  | "sampled-shift-index" =>
      emitUnitRow "PCP.sampledShiftIndex" vars rows trials do
        let _ ← runPcpComp (pcpHonestProof (vars := vars)) (sampledShiftIndexComp vars)
        pure ()
      pure 0
  | "sampled-shift-access" =>
      emitUnitRow "PCP.sampledShiftAccess" vars rows trials do
        let _ ← runPcpComp (pcpHonestProof (vars := vars)) (sampledShiftAccessComp vars)
        pure ()
      pure 0
  | "decoded-lineq" =>
      emitBoolRow "PCP.decodedLineq" vars rows trials do
        runPcpComp (pcpHonestProof (vars := vars)) (decodedLineqComp vars rows)
      pure 0
  | "decoded-tensor" =>
      emitBoolRow "PCP.decodedTensor" vars rows trials do
        runPcpComp (pcpHonestProof (vars := vars)) (decodedTensorComp vars)
      pure 0
  | "decoded-qesat" =>
      emitBoolRow "PCP.decodedQESAT" vars rows trials do
        runPcpComp (pcpHonestProof (vars := vars)) (decodedQESATLpcpComp vars rows)
      pure 0
  | "decoded-qesat-sampled" =>
      emitBoolRow "PCP.decodedQESAT.sampledShifts" vars rows trials do
        runPcpComp (pcpHonestProof (vars := vars))
          (decodedQESATLpcpSampledShiftsComp vars rows)
      pure 0
  | "pre-round" =>
      emitBoolRow "PCP.preRound" vars rows trials do
        runPcpComp (pcpHonestProof (vars := vars)) (pcpRoundComp vars rows)
      pure 0
  | "padded-pre-round" =>
      emitBoolRow "PCP.paddedPreRound" vars rows trials do
        runPcpComp (paddedHonestProof x) (paddedRoundComp x)
      pure 0
  | "final" =>
      emitBoolRow "PCP.finalRepeatedPadded" vars rows trials do
        runPcpComp (paddedHonestProof x) (finalRepeatedComp x)
      pure 0
  | _ =>
      IO.eprintln "unknown component"
      pure 1

def runDecodedT (t vars rows trials : ℕ) : IO UInt32 := do
  IO.println BenchRow.tsvHeader
  emitBoolRow s!"PCP.decodedSingleQuery.t{t}" vars rows trials do
    let y ← runPcpComp (pcpHonestProof (vars := vars)) (decodedSingleQueryCompT vars t)
    pure (y = 0 ∨ y = 1)
  pure 0

def runDecodedSampledT (t vars rows trials : ℕ) : IO UInt32 := do
  IO.println BenchRow.tsvHeader
  emitBoolRow s!"PCP.decodedSingleQuery.sampled.t{t}" vars rows trials do
    let y ← runPcpComp (pcpHonestProof (vars := vars))
      (decodedSingleQuerySampledShiftsCompT vars t)
    pure (y = 0 ∨ y = 1)
  pure 0

def runPluralityT (t vars rows trials : ℕ) : IO UInt32 := do
  IO.println BenchRow.tsvHeader
  emitUnitRow s!"pure.plurality.t{t}" vars rows trials do
    let _ := LPCPToPCP.pluralityZMod2 (t := t) (fun _ => (1 : F))
    pure ()
  pure 0

def runMOfFnT (t vars rows trials : ℕ) : IO UInt32 := do
  IO.println BenchRow.tsvHeader
  emitUnitRow s!"pure.mOfFn.t{t}" vars rows trials do
    let _ys ← Fin.mOfFn t fun _ => pure (1 : F)
    pure ()
  pure 0

def runMOfFnPluralityT (t vars rows trials : ℕ) : IO UInt32 := do
  IO.println BenchRow.tsvHeader
  emitUnitRow s!"pure.mOfFnPlurality.t{t}" vars rows trials do
    let ys ← Fin.mOfFn t fun _ => pure (1 : F)
    let _ := LPCPToPCP.pluralityZMod2 ys
    pure ()
  pure 0

def runFixedIndexCorrectionLoopT (t vars rows trials : ℕ) : IO UInt32 := do
  IO.println BenchRow.tsvHeader
  emitBoolRow s!"PCP.fixedIndexCorrectionLoop.t{t}" vars rows trials do
    let y ← runPcpComp (pcpHonestProof (vars := vars)) (fixedIndexCorrectionLoopCompT vars t)
    pure (y = 0 ∨ y = 1)
  pure 0

end QESATComponentBench

def parseNat? (s : String) : Option ℕ :=
  s.toNat?

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      QESATComponentBench.runTsv QESATComponentBench.defaultCases
      pure 0
  | ["wide"] =>
      QESATComponentBench.runTsv QESATComponentBench.wideCases
      pure 0
  | ["case", vars, rows] =>
      match parseNat? vars, parseNat? rows with
      | some vars, some rows =>
          QESATComponentBench.runTsv [(vars, rows)]
          pure 0
      | _, _ =>
          IO.eprintln "usage: lake exe qesat_component_bench [wide|case vars rows|component name vars rows trials]"
          pure 1
  | ["component", component, vars, rows, trials] =>
      match parseNat? vars, parseNat? rows, parseNat? trials with
      | some vars, some rows, some trials =>
          QESATComponentBench.runOneComponent component vars rows trials
      | _, _, _ =>
          IO.eprintln "usage: lake exe qesat_component_bench [wide|case vars rows|component name vars rows trials|decoded-t shifts vars rows trials|plurality-t shifts vars rows trials|mofn-t shifts vars rows trials|mofn-plurality-t shifts vars rows trials|fixed-loop-t shifts vars rows trials]"
          pure 1
  | ["decoded-t", shifts, vars, rows, trials] =>
      match parseNat? shifts, parseNat? vars, parseNat? rows, parseNat? trials with
      | some shifts, some vars, some rows, some trials =>
          QESATComponentBench.runDecodedT shifts vars rows trials
      | _, _, _, _ =>
          IO.eprintln "usage: lake exe qesat_component_bench [wide|case vars rows|component name vars rows trials|decoded-t shifts vars rows trials|plurality-t shifts vars rows trials|mofn-t shifts vars rows trials|mofn-plurality-t shifts vars rows trials|fixed-loop-t shifts vars rows trials]"
          pure 1
  | ["decoded-sampled-t", shifts, vars, rows, trials] =>
      match parseNat? shifts, parseNat? vars, parseNat? rows, parseNat? trials with
      | some shifts, some vars, some rows, some trials =>
          QESATComponentBench.runDecodedSampledT shifts vars rows trials
      | _, _, _, _ =>
          IO.eprintln "usage: lake exe qesat_component_bench [wide|case vars rows|component name vars rows trials|decoded-t shifts vars rows trials|decoded-sampled-t shifts vars rows trials|plurality-t shifts vars rows trials|mofn-t shifts vars rows trials|mofn-plurality-t shifts vars rows trials|fixed-loop-t shifts vars rows trials]"
          pure 1
  | ["plurality-t", shifts, vars, rows, trials] =>
      match parseNat? shifts, parseNat? vars, parseNat? rows, parseNat? trials with
      | some shifts, some vars, some rows, some trials =>
          QESATComponentBench.runPluralityT shifts vars rows trials
      | _, _, _, _ =>
          IO.eprintln "usage: lake exe qesat_component_bench [wide|case vars rows|component name vars rows trials|decoded-t shifts vars rows trials|plurality-t shifts vars rows trials|mofn-t shifts vars rows trials|mofn-plurality-t shifts vars rows trials|fixed-loop-t shifts vars rows trials]"
          pure 1
  | ["mofn-t", shifts, vars, rows, trials] =>
      match parseNat? shifts, parseNat? vars, parseNat? rows, parseNat? trials with
      | some shifts, some vars, some rows, some trials =>
          QESATComponentBench.runMOfFnT shifts vars rows trials
      | _, _, _, _ =>
          IO.eprintln "usage: lake exe qesat_component_bench [wide|case vars rows|component name vars rows trials|decoded-t shifts vars rows trials|plurality-t shifts vars rows trials|mofn-t shifts vars rows trials|mofn-plurality-t shifts vars rows trials|fixed-loop-t shifts vars rows trials]"
          pure 1
  | ["mofn-plurality-t", shifts, vars, rows, trials] =>
      match parseNat? shifts, parseNat? vars, parseNat? rows, parseNat? trials with
      | some shifts, some vars, some rows, some trials =>
          QESATComponentBench.runMOfFnPluralityT shifts vars rows trials
      | _, _, _, _ =>
          IO.eprintln "usage: lake exe qesat_component_bench [wide|case vars rows|component name vars rows trials|decoded-t shifts vars rows trials|plurality-t shifts vars rows trials|mofn-t shifts vars rows trials|mofn-plurality-t shifts vars rows trials|fixed-loop-t shifts vars rows trials]"
          pure 1
  | ["fixed-loop-t", shifts, vars, rows, trials] =>
      match parseNat? shifts, parseNat? vars, parseNat? rows, parseNat? trials with
      | some shifts, some vars, some rows, some trials =>
          QESATComponentBench.runFixedIndexCorrectionLoopT shifts vars rows trials
      | _, _, _, _ =>
          IO.eprintln "usage: lake exe qesat_component_bench [wide|case vars rows|component name vars rows trials|decoded-t shifts vars rows trials|plurality-t shifts vars rows trials|mofn-t shifts vars rows trials|mofn-plurality-t shifts vars rows trials|fixed-loop-t shifts vars rows trials]"
          pure 1
  | _ =>
      IO.eprintln "usage: lake exe qesat_component_bench [wide|case vars rows|component name vars rows trials|decoded-t shifts vars rows trials|plurality-t shifts vars rows trials|mofn-t shifts vars rows trials|mofn-plurality-t shifts vars rows trials|fixed-loop-t shifts vars rows trials]"
      pure 1
