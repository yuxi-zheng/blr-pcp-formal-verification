import BlrPcp.Problems.QESAT
import BlrPcp.Test.SysRand

/-!
# Executable QESAT PCP verifier checks

Run with:

```
lake exe qesat_test
```

The default mode is a bounded smoke test. Use `lake exe qesat_test bench`
for a larger local timing run, or `.lake/build/bin/qesat_test csv` for
machine-readable benchmark rows after building the executable.
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

def linearTableNat : (n : ℕ) → (Fin n → F) → ℕ → F
  | 0, _, _ => 0
  | n + 1, π, i =>
      let tail := linearTableNat n (fun j => π (Fin.castSucc j)) i
      if Nat.getBit n i = 0 then tail else tail + π (Fin.last n)

def linearTable {n : ℕ} (π : Fin n → F) : Fin (2 ^ n) → F :=
  fun i => linearTableNat n π i.val

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

/-- Slow reference runner for the proof-oriented `OracleComp` verifier. -/
def runOracleVerifier {vars : ℕ} (x : List (CMvPolynomial vars F))
    (π : Fin (2 ^ QESAT.size x) → F) : IO Bool :=
  SysRand.runPCP π (QESAT.pcpVerifier (vars := vars) x)

def runOracleTrivialVerifier {vars : ℕ} (x : List (CMvPolynomial vars F)) : IO Bool :=
  SysRand.runPCP (Fin.elim0 : Fin 0 → F) (QESAT.trivialPcpVerifier (vars := vars) x)

abbrev FastProof := Nat → Bool

def boolToF : Bool → F
  | false => 0
  | true => 1

def fToBool (x : F) : Bool :=
  decide (x ≠ 0)

def bxor (a b : Bool) : Bool :=
  a != b

def bitAt (i x : ℕ) : Bool :=
  Nat.getBit i x != 0

def bitMask (i : ℕ) : ℕ :=
  2 ^ i

def randBool : IO Bool := do
  let b ← SysRand.randFinInclusive 1
  pure (b.val == 1)

def sampleIndexAux : ℕ → ℕ → ℕ → IO ℕ
  | 0, _, acc => pure acc
  | fuel + 1, shift, acc => do
      let width := min 30 (fuel + 1)
      let upper := 2 ^ width - 1
      let chunk ← SysRand.randFinInclusive upper
      sampleIndexAux (fuel + 1 - width) (shift + width)
        (Nat.lor acc (Nat.shiftLeft chunk.val shift))

def sampleIndex (width : ℕ) : IO ℕ :=
  sampleIndexAux width 0 0

def linearEvalIndexAux (coeff : ℕ → Bool) (idx : ℕ) : ℕ → Bool → Bool
  | 0, acc => acc
  | k + 1, acc =>
      let acc' := if bitAt k idx then bxor acc (coeff k) else acc
      linearEvalIndexAux coeff idx k acc'

def linearEvalIndex (width : ℕ) (coeff : ℕ → Bool) (idx : ℕ) : Bool :=
  linearEvalIndexAux coeff idx width false

def assignmentCoeff {vars : ℕ} (a : Fin vars → F) (coord : ℕ) : Bool :=
  if h : coord < vars then
    fToBool (a ⟨coord, h⟩)
  else
    let q := coord - vars
    let i := q / vars
    let j := q % vars
    if hi : i < vars then
      if hj : j < vars then
        fToBool (a ⟨i, hi⟩ * a ⟨j, hj⟩)
      else
        false
    else
      false

def honestProofNat {vars : ℕ} (a : Fin vars → F) : FastProof :=
  fun idx => linearEvalIndex (vars + vars * vars) (assignmentCoeff a) idx

def zeroProofNat : FastProof :=
  fun _ => false

def monomialTotalDegreeFast {vars : ℕ} (m : CMvMonomial vars) : ℕ :=
  (List.finRange vars).foldl (fun acc i => acc + m.get i) 0

def monomialCoord? {vars : ℕ} (m : CMvMonomial vars) : Option ℕ :=
  let nz := (List.finRange vars).filter fun i => m.get i != 0
  match nz with
  | [] => none
  | [i] =>
      let e := m.get i
      if (e == 1) || (e == 2) then
        some (vars + i.val * vars + i.val)
      else
        none
  | [i, j] =>
      if (m.get i == 1) && (m.get j == 1) then
        some (vars + i.val * vars + j.val)
      else
        none
  | _ => none

def polynomialDegreeOkFast {vars : ℕ} (p : CMvPolynomial vars F) : Bool :=
  (Lawful.monomials p).all fun m => monomialTotalDegreeFast m ≤ 2

def polynomialRowIndex {vars : ℕ} (p : CMvPolynomial vars F) : ℕ :=
  (Lawful.monomials p).foldl
    (fun acc m =>
      if CMvPolynomial.coeff m p = 0 then
        acc
      else
        match monomialCoord? m with
        | none => acc
        | some coord => Nat.xor acc (bitMask coord))
    0

def polynomialTarget {vars : ℕ} (p : CMvPolynomial vars F) : Bool :=
  fToBool (CMvPolynomial.coeff 0 p)

structure FastInstance where
  vars : ℕ
  size : ℕ
  proofDim : ℕ
  rows : List ℕ
  targets : List Bool
  degreeOk : Bool

def compileFastInstance {vars : ℕ} (x : List (CMvPolynomial vars F)) : FastInstance where
  vars := vars
  size := QESAT.size x
  proofDim := vars + vars * vars
  rows := x.map polynomialRowIndex
  targets := x.map polynomialTarget
  degreeOk := x.all polynomialDegreeOkFast

def xorSelectedRows : List ℕ → ℕ → ℕ → ℕ → ℕ
  | [], _, acc, _ => acc
  | row :: rows, r, acc, i =>
      xorSelectedRows rows r (if bitAt i r then Nat.xor acc row else acc) (i + 1)

def selectedTarget : List Bool → ℕ → Bool → ℕ → Bool
  | [], _, acc, _ => acc
  | target :: targets, r, acc, i =>
      selectedTarget targets r (if bitAt i r then bxor acc target else acc) (i + 1)

def evalRowOnAssignment (vars row assignment : ℕ) : Bool :=
  linearEvalIndex (vars + vars * vars)
    (fun coord =>
      if coord < vars then
        bitAt coord assignment
      else
        let q := coord - vars
        bitAt (q / vars) assignment && bitAt (q % vars) assignment)
    row

def allRowsSatisfied (ci : FastInstance) (assignment : ℕ) : Bool :=
  (ci.rows.zip ci.targets).all fun (row, target) =>
    evalRowOnAssignment ci.vars row assignment == target

def searchAssignment (ci : FastInstance) : ℕ → Bool
  | 0 => false
  | fuel + 1 => allRowsSatisfied ci fuel || searchAssignment ci fuel

def trivialAcceptsFast (ci : FastInstance) : Bool :=
  ci.degreeOk && searchAssignment ci (2 ^ ci.vars)

def selfCorrectSampleFast (proof : FastProof) (width u : ℕ) : IO Bool := do
  let z ← sampleIndex width
  pure (bxor (proof z) (proof (Nat.xor u z)))

def selfCorrectRestFast (proof : FastProof) (width u : ℕ) :
    ℕ → Bool → IO Bool
  | 0, _ => pure true
  | fuel + 1, expected => do
      let y ← selfCorrectSampleFast proof width u
      if y == expected then
        selfCorrectRestFast proof width u fuel expected
      else
        pure false

def selfCorrectFast (proof : FastProof) (width rep u : ℕ) : IO (Option Bool) :=
  match rep with
  | 0 => pure none
  | fuel + 1 => do
      let y ← selfCorrectSampleFast proof width u
      let ok ← selfCorrectRestFast proof width u fuel y
      pure (if ok then some y else none)

def blrFast (proof : FastProof) (width : ℕ) : IO Bool := do
  let x ← sampleIndex width
  let y ← sampleIndex width
  pure (bxor (proof x) (proof y) == proof (Nat.xor x y))

def lineqFast (ci : FastInstance) (proof : FastProof) (rep : ℕ) : IO Bool := do
  let r ← sampleIndex ci.rows.length
  let u := xorSelectedRows ci.rows r 0 0
  let target := selectedTarget ci.targets r false 0
  match ← selfCorrectFast proof ci.proofDim rep u with
  | none => pure false
  | some y => pure (y == target)

def queryBIndex (vars s t : ℕ) : ℕ := Id.run do
  let mut acc := 0
  for i in List.range vars do
    if bitAt i s then
      for j in List.range vars do
        if bitAt j t then
          acc := Nat.lor acc (bitMask (vars + i * vars + j))
  pure acc

def tensorFast (ci : FastInstance) (proof : FastProof) (rep : ℕ) : IO Bool := do
  let s ← sampleIndex ci.vars
  let t ← sampleIndex ci.vars
  let yA? ← selfCorrectFast proof ci.proofDim rep s
  let yA'? ← selfCorrectFast proof ci.proofDim rep t
  let yB? ← selfCorrectFast proof ci.proofDim rep (queryBIndex ci.vars s t)
  match yA?, yA'?, yB? with
  | some yA, some yA', some yB => pure (yB == (yA && yA'))
  | _, _, _ => pure false

def pcpRoundFast (ci : FastInstance) (proof : FastProof) : IO Bool := do
  if !ci.degreeOk then
    pure false
  else if !(← blrFast proof ci.proofDim) then
    pure false
  else if !(← lineqFast ci proof 9) then
    pure false
  else
    tensorFast ci proof 9

def repeatPcpFast (ci : FastInstance) (proof : FastProof) : ℕ → IO Bool
  | 0 => pure true
  | fuel + 1 => do
      if ← pcpRoundFast ci proof then
        repeatPcpFast ci proof fuel
      else
        pure false

def runFastVerifier {vars : ℕ} (x : List (CMvPolynomial vars F))
    (proof : FastProof) : IO Bool := do
  let ci := compileFastInstance x
  if ci.proofDim ≤ ci.size then
    repeatPcpFast ci proof 6
  else
    pure true

def runFastTrivialVerifier {vars : ℕ} (x : List (CMvPolynomial vars F)) : IO Bool :=
  pure (trivialAcceptsFast (compileFastInstance x))

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
  let π := honestProofNat (allOnes (vars := vars + 1))
  let summary ← runTrials s!"complete vars={vars + 1}" trials (runFastVerifier x π)
  IO.println summary.render
  requireAllAccepted summary

def runSoundnessCase (vars trials : ℕ) : IO Unit := do
  let x := unsatInstance vars
  let π := zeroProofNat
  let summary ← runTrials s!"soundness vars={vars + 1}" trials (runFastVerifier x π)
  IO.println summary.render
  requireAcceptanceAtMostHalf summary

def runVariableRuntimeCase (vars trials : ℕ) : IO Unit := do
  let x := satInstance vars
  let π := honestProofNat (allOnes (vars := vars + 1))
  let summary ← runTrials s!"runtime-vars vars={vars + 1}, polys={x.length}" trials
    (runFastVerifier x π)
  IO.println summary.render

def runLengthRuntimeCase (vars count trials : ℕ) : IO Unit := do
  let x := repeatedSatInstance vars count
  let π := honestProofNat (allOnes (vars := vars + 1))
  let summary ← runTrials s!"runtime-length vars={vars + 1}, polys={count}" trials
    (runFastVerifier x π)
  IO.println summary.render

structure BenchmarkRow where
  verifier : String
  vars : ℕ
  polys : ℕ
  trials : ℕ
  accepts : ℕ
  elapsedMs : ℕ

def BenchmarkRow.avgMs (row : BenchmarkRow) : ℕ :=
  if row.trials = 0 then 0 else row.elapsedMs / row.trials

def BenchmarkRow.csvHeader : String :=
  "verifier,vars,polys,trials,accepts,elapsed_ms,avg_ms"

def BenchmarkRow.toCsv (row : BenchmarkRow) : String :=
  s!"{row.verifier},{row.vars},{row.polys},{row.trials},{row.accepts}," ++
    s!"{row.elapsedMs},{row.avgMs}"

def runBenchmarkRow (verifier : String) (vars polys trials : ℕ) (trial : IO Bool) :
    IO BenchmarkRow := do
  let (accepts, elapsed) ← timeIt (repeatTrials trials trial)
  pure { verifier, vars, polys, trials, accepts, elapsedMs := elapsed }

def runPcpBenchmarkRow (vars trials : ℕ) : IO BenchmarkRow := do
  let x := satInstance vars
  let π := honestProofNat (allOnes (vars := vars + 1))
  runBenchmarkRow "pcp" (vars + 1) x.length trials (runFastVerifier x π)

def runPcpZeroBenchmarkRow (vars trials : ℕ) : IO BenchmarkRow := do
  let x := satInstance vars
  runBenchmarkRow "pcp-zero" (vars + 1) x.length trials (runFastVerifier x zeroProofNat)

def runTrivialBenchmarkRow (vars trials : ℕ) : IO BenchmarkRow := do
  -- Use an unsatisfiable instance so the brute-force verifier must scan every assignment.
  let x := unsatInstance vars
  runBenchmarkRow "trivial" (vars + 1) x.length trials (runFastTrivialVerifier x)

def runCsv (pcpMaxVars trivialMaxVars trials : ℕ) : IO Unit := do
  IO.println BenchmarkRow.csvHeader
  for vars in List.range pcpMaxVars do
    IO.println (← runPcpBenchmarkRow vars trials).toCsv
  for vars in List.range trivialMaxVars do
    IO.println (← runTrivialBenchmarkRow vars trials).toCsv

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
  | ["csv"] =>
      QESATTest.runCsv 24 20 3
      pure 0
  | ["csv", maxVars] =>
      let n := maxVars.toNat?.getD 3
      QESATTest.runCsv n n 3
      pure 0
  | ["csv", maxVars, trials] =>
      let n := maxVars.toNat?.getD 3
      QESATTest.runCsv n n (trials.toNat?.getD 3)
      pure 0
  | ["csv", pcpMaxVars, trials, trivialMaxVars] =>
      QESATTest.runCsv (pcpMaxVars.toNat?.getD 3) (trivialMaxVars.toNat?.getD 16)
        (trials.toNat?.getD 3)
      pure 0
  | ["csv-zero", maxVars, trials] =>
      IO.println QESATTest.BenchmarkRow.csvHeader
      for vars in List.range (maxVars.toNat?.getD 3) do
        IO.println (← QESATTest.runPcpZeroBenchmarkRow vars (trials.toNat?.getD 1)).toCsv
      pure 0
  | _ =>
      IO.eprintln
        ("usage: lake exe qesat_test " ++
          "[smoke|bench|csv [maxVars] [trials] [trivialMaxVars]|csv-zero maxVars trials]")
      pure 1
