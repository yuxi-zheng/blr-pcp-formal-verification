import BlrPcp.Problems.QESAT
import BlrPcp.Test.SysRand

/-!
# Executable QESAT PCP verifier checks

Run with:

```
lake exe qesat_test
```

The default mode is a bounded smoke test. Use `lake exe qesat_test bench`
for a larger local timing run.
-/

open CPoly CMvPolynomial
open OracleComp
open scoped ENNReal
open scoped Matrix

namespace QESATTest

abbrev F := ZMod 2

def firstVarEqOne (vars : ℕ) : CMvPolynomial (vars + 1) F :=
  CMvPolynomial.X (R := F) ⟨0, Nat.succ_pos vars⟩ +
    CMvPolynomial.C (n := vars + 1) (R := F) 1

def satInstance (vars : ℕ) : List (CMvPolynomial (vars + 1) F) :=
  [firstVarEqOne vars]

def unsatInstance (vars : ℕ) : List (CMvPolynomial (vars + 1) F) :=
  [CMvPolynomial.C (n := vars + 1) (R := F) 1]

def repeatedSatInstance (vars count : ℕ) : List (CMvPolynomial (vars + 1) F) :=
  List.replicate count (firstVarEqOne vars)

def allOnes {vars : ℕ} : Fin vars → F :=
  fun _ => 1

def vectorOfIndex {n : ℕ} (i : Fin (2 ^ n)) : Fin n → F :=
  fun j => (Nat.getBit j.val i.val : F)

def linearTable {n : ℕ} (π : Fin n → F) : Fin (2 ^ n) → F :=
  fun i => π ⬝ᵥ vectorOfIndex i

def honestLPCPProof {vars : ℕ} (a : Fin vars → F) :
    Fin (vars + vars * vars) → F :=
  TENSORQ.honestProof (F := F) (a, fun q : Fin vars × Fin vars => a q.1 * a q.2)

def paddedProof {small large : ℕ} (π : Fin small → F) : Fin large → F :=
  fun j => if hj : j.val < small then π ⟨j.val, hj⟩ else 0

def honestPCPProof {vars : ℕ} (x : List (CMvPolynomial vars F)) (a : Fin vars → F) :
    Fin (2 ^ QESAT.size x) → F :=
  paddedProof (linearTable (honestLPCPProof a))

def zeroProof {vars : ℕ} (x : List (CMvPolynomial vars F)) :
    Fin (2 ^ QESAT.size x) → F :=
  fun _ => 0

def runVerifier {vars : ℕ} (x : List (CMvPolynomial vars F))
    (π : Fin (2 ^ QESAT.size x) → F) : IO Bool :=
  SysRand.runPCP π (QESAT.pcpVerifier (vars := vars) x)

structure TrialSummary where
  label : String
  trials : ℕ
  accepts : ℕ
  elapsedMs : ℕ

def rateString (accepts trials : ℕ) : String :=
  if trials = 0 then
    "n/a"
  else
    let scaled := accepts * 10000 / trials
    let whole := scaled / 100
    let frac := scaled % 100
    let fracText := if frac < 10 then "0" ++ toString frac else toString frac
    s!"{accepts}/{trials} ({whole}.{fracText}%)"

def TrialSummary.render (s : TrialSummary) : String :=
  let avgMs := if s.trials = 0 then 0 else s.elapsedMs / s.trials
  s!"{s.label}: accepts={rateString s.accepts s.trials}, elapsed={s.elapsedMs}ms, avg={avgMs}ms"

def timeIt {α : Type} (x : IO α) : IO (α × ℕ) := do
  let start ← IO.monoMsNow
  let y ← x
  let stop ← IO.monoMsNow
  pure (y, stop - start)

def repeatTrials (trials : ℕ) (trial : IO Bool) : IO ℕ := do
  let mut accepts := 0
  for _ in List.range trials do
    if ← trial then
      accepts := accepts + 1
  pure accepts

def runTrials (label : String) (trials : ℕ) (trial : IO Bool) : IO TrialSummary := do
  let (accepts, elapsed) ← timeIt (repeatTrials trials trial)
  pure { label, trials, accepts, elapsedMs := elapsed }

def requireAllAccepted (s : TrialSummary) : IO Unit := do
  if s.accepts = s.trials then
    pure ()
  else
    throw (IO.userError s!"completeness check failed: {s.render}")

def requireAcceptanceAtMostHalf (s : TrialSummary) : IO Unit := do
  if s.accepts * 2 ≤ s.trials then
    pure ()
  else
    throw (IO.userError s!"empirical soundness check failed: {s.render}")

def runCompletenessCase (vars trials : ℕ) : IO Unit := do
  let x := satInstance vars
  let π := honestPCPProof x (allOnes (vars := vars + 1))
  let summary ← runTrials s!"complete vars={vars + 1}" trials (runVerifier x π)
  IO.println summary.render
  requireAllAccepted summary

def runSoundnessCase (vars trials : ℕ) : IO Unit := do
  let x := unsatInstance vars
  let π := zeroProof x
  let summary ← runTrials s!"soundness vars={vars + 1}" trials (runVerifier x π)
  IO.println summary.render
  requireAcceptanceAtMostHalf summary

def runVariableRuntimeCase (vars trials : ℕ) : IO Unit := do
  let x := satInstance vars
  let π := honestPCPProof x (allOnes (vars := vars + 1))
  let summary ← runTrials s!"runtime-vars vars={vars + 1}, polys={x.length}" trials
    (runVerifier x π)
  IO.println summary.render

def runLengthRuntimeCase (vars count trials : ℕ) : IO Unit := do
  let x := repeatedSatInstance vars count
  let π := honestPCPProof x (allOnes (vars := vars + 1))
  let summary ← runTrials s!"runtime-length vars={vars + 1}, polys={count}" trials
    (runVerifier x π)
  IO.println summary.render

def runSmoke : IO Unit := do
  IO.println "QESAT PCP concrete verifier smoke tests"
  IO.println "Completeness checks"
  for vars in [0, 1, 2] do
    runCompletenessCase vars 1
  IO.println "Empirical soundness check"
  runSoundnessCase 0 100
  IO.println "Runtime by variable count"
  for vars in [0, 1, 2] do
    runVariableRuntimeCase vars 1
  IO.println "Runtime by polynomial count"
  for count in [1, 10, 100] do
    runLengthRuntimeCase 0 count 1

def runBench : IO Unit := do
  IO.println "QESAT PCP concrete verifier benchmark"
  IO.println "Completeness checks"
  for vars in [0, 1, 2] do
    runCompletenessCase vars 5
  IO.println "Empirical soundness checks"
  runSoundnessCase 0 500
  runSoundnessCase 1 100
  runSoundnessCase 2 20
  IO.println "Runtime by variable count"
  for vars in [0, 1, 2] do
    runVariableRuntimeCase vars 5
  IO.println "Runtime by polynomial count"
  for count in [1, 10, 100, 500] do
    runLengthRuntimeCase 0 count 3

example {vars : ℕ} (x : List (CMvPolynomial vars F)) :
    (x ∈ QESAT F vars → ∃ π : Fin (2 ^ QESAT.size x) → F,
      Pr[= true | simulateQ ((rand F).impl + (PCP.proof π).impl)
        (QESAT.pcpVerifier (vars := vars) x)] ≥ 1 - (0 : ℝ≥0∞)) :=
  (QESAT.pcpVerifier_correct (vars := vars) x).2.2.1

example {vars : ℕ} (x : List (CMvPolynomial vars F)) :
    (x ∉ QESAT F vars → ∀ π : Fin (2 ^ QESAT.size x) → F,
      Pr[= true | simulateQ ((rand F).impl + (PCP.proof π).impl)
        (QESAT.pcpVerifier (vars := vars) x)] ≤ (1 / 2 : ℝ≥0∞)) :=
  (QESAT.pcpVerifier_correct (vars := vars) x).2.2.2

def runAll : IO Unit := do
  runSmoke

end QESATTest

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      QESATTest.runSmoke
      pure 0
  | ["smoke"] =>
      QESATTest.runSmoke
      pure 0
  | ["bench"] =>
      QESATTest.runBench
      pure 0
  | _ =>
      IO.eprintln "usage: lake exe qesat_test [smoke|bench]"
      pure 1
