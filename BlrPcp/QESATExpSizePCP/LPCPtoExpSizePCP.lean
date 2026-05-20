import Architect
import BlrPcp.QESATExpSizePCP.PCPs
import BlrPcp.QESATExpSizePCP.FnOracleAccessBLR
import CompPoly.Multivariate.CMvPolynomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Archimedean
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import VCVio.OracleComp.Constructions.Replicate

open OracleComp
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LPCPToPCP

/-- Index the truth table of a function `F₂^n → F₂` by `Fin (2^n)`. -/
def truthTableIndex (n : ℕ) : (Fin n → ZMod 2) → Fin (2 ^ n) :=
  finFunctionFinEquiv

/-- Interpret a PCP truth table as the function `F₂^n → F₂` tested by BLR. -/
noncomputable def tableFunction {n : ℕ} (πhat : Fin (2 ^ n) → ZMod 2) :
    (Fin n → ZMod 2) → ZMod 2 :=
  fun v => πhat (truthTableIndex n v)

/-- Decode a truth-table index back to the corresponding vector in `F₂^n`. -/
def truthTableVector (n : ℕ) : Fin (2 ^ n) → (Fin n → ZMod 2) :=
  (finFunctionFinEquiv (m := 2) (n := n)).symm

lemma truthTableVector_truthTableIndex (n : ℕ) (v : Fin n → ZMod 2) :
    truthTableVector n (truthTableIndex n v) = v := by
  simp [truthTableVector, truthTableIndex]

/-- Encode the linear LPCP proof as the PCP truth table `a ↦ ⟪π, a⟫`. -/
def encodedProof {n : ℕ} (π : Fin n → ZMod 2) : Fin (2 ^ n) → ZMod 2 :=
  fun i => π ⬝ᵥ truthTableVector n i

lemma encodedProof_truthTableIndex {n : ℕ} (π : Fin n → ZMod 2)
    (v : Fin n → ZMod 2) :
    encodedProof π (truthTableIndex n v) = π ⬝ᵥ v := by
  simp [encodedProof, truthTableVector_truthTableIndex]

/-- `⌊log₂ (100 q)⌋ + 1`, a computable `Θ(log q)` surrogate for `⌈ln (100q)⌉`. -/
def logFactor (q : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.log 2 (100 * q n) + 1

/-- Number of random shifts used to decode a linear query by plurality. -/
def numShifts (q : ℕ → ℕ) (n : ℕ) : ℕ :=
  8 * logFactor q n

lemma numShifts_pos (q : ℕ → ℕ) (n : ℕ) : 0 < numShifts q n := by
  simp [numShifts, logFactor]

/-- Plurality over `ZMod 2`, with ties broken toward `0`. -/
def pluralityZMod2 {t : ℕ} (ys : Fin t → ZMod 2) : ZMod 2 :=
  if Fintype.card { i : Fin t // ys i = 1 } * 2 > t then 1 else 0

lemma pluralityZMod2_const {t : ℕ} (ht : 0 < t) (b : ZMod 2) :
    pluralityZMod2 (fun _ : Fin t => b) = b := by
  fin_cases b
  · simp [pluralityZMod2]
  · simp [pluralityZMod2, ht]

abbrev sampleField {F : Type} {N : ℕ} : OracleComp (PCP.fullSpec F N) F :=
  OracleUtil.sampleField (spec := proofOracleSpec_fin F N)

def sampleVector (F : Type) (m : ℕ) {N : ℕ} :
    OracleComp (PCP.fullSpec F N) (Fin m → F) :=
  OracleUtil.sampleVector (sampleField (F := F) (N := N)) m

def sampleShifts (n t : ℕ) :
    OracleComp (PCP.fullSpec (ZMod 2) (2 ^ n)) (Fin t → Fin n → ZMod 2) :=
  Fin.mOfFn t fun _ => sampleVector (ZMod 2) n

private lemma queryBound_map {ρ ι α β : Type} {randSpec : OracleSpec ρ}
    {proofSpec : OracleSpec ι} {oa : OracleComp (randSpec + proofSpec) α}
    {q r : ℕ} (f : α → β) (hoa : QueryBound oa r q) :
    QueryBound (f <$> oa) r q := by
  simpa [QueryBound] using
    (OracleComp.isQueryBound_map_iff oa f (r, q)
      (fun
        | .inl _, (r, _) => 0 < r
        | .inr _, (_, q) => 0 < q)
      (fun
        | .inl _, (r, q) => (r - 1, q)
        | .inr _, (r, q) => (r, q - 1))).2 hoa

private lemma queryBound_mOfFn {ρ ι α : Type} {randSpec : OracleSpec ρ}
    {proofSpec : OracleSpec ι} {m r q : ℕ}
    (oa : Fin m → OracleComp (randSpec + proofSpec) α)
    (hoa : ∀ i, QueryBound (oa i) r q) :
    QueryBound (Fin.mOfFn m oa) (m * r) (m * q) := by
  induction m with
  | zero =>
      simp [Fin.mOfFn, QueryBound]
  | succ m ih =>
      simp only [Fin.mOfFn]
      simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        queryBound_bind (hoa 0) fun x =>
          by
            simpa [QueryBound] using ih (fun i => oa i.succ) fun i => hoa i.succ

lemma sampleVector_queryBound (F : Type) (m : ℕ) {N : ℕ} :
    QueryBound (sampleVector F m (N := N)) m 0 :=
  OracleUtil.sampleVector_queryBound' OracleUtil.sampleField_queryBound m

lemma sampleShifts_queryBound (n t : ℕ) :
    QueryBound (sampleShifts n t) (t * n) 0 := by
  simpa [sampleShifts] using
    queryBound_mOfFn
      (fun _ : Fin t => sampleVector (ZMod 2) n (N := 2 ^ n))
      (fun _ => sampleVector_queryBound (ZMod 2) n (N := 2 ^ n))

private lemma simulateQ_sampleField {F : Type}
    [Nonempty F] [Fintype F] [SampleableType F]
    {N : ℕ} (impl : QueryImpl (proofOracleSpec_fin F N) ProbComp) :
    simulateQ ((randOracle F).impl + impl) (sampleField (F := F) (N := N)) = $ᵗ F := by
  simp [OracleUtil.sampleField, randOracle]

@[simp]
lemma probOutput_simulateQ_sampleVector {F : Type}
    [Nonempty F] [DecidableEq F] [Fintype F] [SampleableType F]
    {m N : ℕ} (impl : QueryImpl (proofOracleSpec_fin F N) ProbComp)
    (x : Fin m → F) :
    Pr[= x | simulateQ ((randOracle F).impl + impl) (sampleVector F m (N := N))] =
      (Fintype.card (Fin m → F) : ℝ≥0∞)⁻¹ := by
  haveI : Inhabited F := Classical.inhabited_of_nonempty ‹_›
  rw [show sampleVector F m (N := N) =
        OracleUtil.sampleVector (sampleField (F := F) (N := N)) m from rfl]
  rw [OracleUtil.simulateQ_sampleVector' _ (simulateQ_sampleField impl) m]
  exact probOutput_uniformSample (α := Fin m → F) x

lemma probEvent_simulateQ_sampleVector_eq_sum {F : Type}
    [Nonempty F] [DecidableEq F] [Fintype F] [SampleableType F]
    {m N : ℕ} (impl : QueryImpl (proofOracleSpec_fin F N) ProbComp)
    (p : (Fin m → F) → Prop) [DecidablePred p] :
    Pr[p | simulateQ ((randOracle F).impl + impl) (sampleVector F m (N := N))] =
      ∑ y : Fin m → F,
        (Fintype.card (Fin m → F) : ℝ≥0∞)⁻¹ * if p y then 1 else 0 := by
  rw [probEvent_eq_tsum_ite, tsum_fintype]
  apply Finset.sum_congr rfl
  intro y _
  rw [probOutput_simulateQ_sampleVector (impl := impl) y]
  by_cases hy : p y <;> simp [hy]

/-- The mean of the sum of Boolean random variables sampled independently by `Fin.mOfFn`. -/
noncomputable def bernoulliSumMean {N : ℕ} (X : Fin N → ProbComp Bool) : ℝ :=
  ∑ i : Fin N, (Pr[= true | X i]).toReal

private lemma pmf_bool_sum (p : PMF Bool) : p true + p false = 1 := by
  simpa [Fintype.sum_bool] using (PMF.tsum_coe p)

private noncomputable def piBoolPMF {N : ℕ} (p : Fin N → PMF Bool) :
    PMF (Fin N → Bool) :=
  PMF.ofFintype (fun xs => ∏ i : Fin N, p i (xs i)) (by
    classical
    calc
      ∑ xs : Fin N → Bool, ∏ i : Fin N, p i (xs i)
          = ∏ i : Fin N, ∑ b ∈ (Finset.univ : Finset Bool), p i b := by
            simpa [Fintype.piFinset_univ] using
              (Finset.sum_prod_piFinset (ι := Fin N) (s := Finset.univ)
                (g := fun i b => p i b))
      _ = 1 := by simp [pmf_bool_sum])

private lemma pmf_map_some_apply_some {α : Type} (p : PMF α) (x : α) :
    (some <$> p) (some x) = p x := by
  rw [PMF.monad_map_eq_map, PMF.map_apply]
  rw [tsum_eq_single x]
  · simp
  · intro b hb
    have hxb : x ≠ b := fun h => hb h.symm
    simp [hxb]

private lemma probOutput_eq_toPMF {α : Type} (mx : ProbComp α) (x : α) :
    Pr[= x | mx] = (HasEvalPMF.toPMF mx) x := by
  rw [probOutput_def, HasEvalPMF.evalDist_of_hasEvalPMF_def]
  rw [SPMF.apply_eq_toPMF_some, SPMF.toPMF_liftM]
  exact pmf_map_some_apply_some (HasEvalPMF.toPMF mx) x

private lemma probEvent_eq_toPMF_toMeasure {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] (mx : ProbComp α) (p : α → Prop)
    (hp : MeasurableSet {x | p x}) :
    Pr[p | mx] = (HasEvalPMF.toPMF mx).toMeasure {x | p x} := by
  rw [probEvent_eq_tsum_indicator]
  rw [PMF.toMeasure_apply _ hp]
  apply tsum_congr
  intro x
  exact congrArg ({x | p x}.indicator · x) (funext fun y => probOutput_eq_toPMF mx y)

private lemma pmf_map_fin_cons_apply {n : ℕ} (p : PMF (Fin n → Bool)) (b : Bool)
    (xs : Fin (n + 1) → Bool) :
    (PMF.map (fun y : Fin n → Bool => Fin.cons b y) p) xs =
      if xs 0 = b then p (fun i => xs i.succ) else 0 := by
  classical
  rw [PMF.map_apply]
  by_cases h0 : xs 0 = b
  · rw [if_pos h0]
    rw [tsum_eq_single (fun i : Fin n => xs i.succ)]
    · have hcons : xs = Fin.cons b (fun i : Fin n => xs i.succ) := by
        ext i
        cases i using Fin.cases <;> simp [h0]
      rw [hcons]
      simp
    · intro y hy
      rw [if_neg]
      intro hxy
      apply hy
      ext i
      simp [hxy]
  · rw [if_neg h0]
    rw [ENNReal.tsum_eq_zero]
    intro y
    rw [if_neg]
    intro hxy
    exact h0 (by simp [hxy])

private lemma toPMF_mOfFn_bool {N : ℕ} (X : Fin N → ProbComp Bool) :
    HasEvalPMF.toPMF (Fin.mOfFn N X) = piBoolPMF (fun i => HasEvalPMF.toPMF (X i)) := by
  induction N with
  | zero =>
      ext xs
      simp [Fin.mOfFn, piBoolPMF]
      ext i
      exact Fin.elim0 i
  | succ n ih =>
      ext xs
      simp [Fin.mOfFn, piBoolPMF]
      simp_rw [ih (fun i : Fin n => X i.succ)]
      rw [PMF.monad_map_eq_map, pmf_map_fin_cons_apply]
      rw [PMF.monad_map_eq_map, pmf_map_fin_cons_apply]
      rw [Fin.prod_univ_succ]
      cases hxs0 : xs 0 <;> simp [piBoolPMF]

private lemma piBoolPMF_toMeasure {N : ℕ} (p : Fin N → PMF Bool) :
    (piBoolPMF p).toMeasure = Measure.pi (fun i => (p i).toMeasure) := by
  classical
  apply Measure.ext_of_singleton
  intro xs
  rw [(piBoolPMF p).toMeasure_apply_singleton xs (measurableSet_singleton xs)]
  rw [Measure.pi_singleton]
  simp [piBoolPMF]

private lemma coordinate_mean {N : ℕ} (X : Fin N → ProbComp Bool) (i : Fin N) :
    ∫ xs : Fin N → Bool, (if xs i then (1 : ℝ) else 0)
      ∂(Measure.pi fun i => (HasEvalPMF.toPMF (X i)).toMeasure) =
    (Pr[= true | X i]).toReal := by
  have hcomp := MeasureTheory.integral_comp_eval
    (μ := fun i : Fin N => (HasEvalPMF.toPMF (X i)).toMeasure)
    (i := i) (f := fun b : Bool => if b then (1 : ℝ) else 0)
    (by exact (measurable_of_finite _).aestronglyMeasurable)
  rw [hcomp]
  rw [PMF.integral_eq_sum]
  rw [probOutput_eq_toPMF]
  simp

/-- Chernoff bound for independent Boolean random variables. -/
theorem chernoff_bound {N : ℕ} (hN : 0 < N) (X : Fin N → ProbComp Bool)
    {Δ : ℝ} (hΔ : 0 < Δ) :
    Pr[fun xs => bernoulliSumMean X + Δ ≤
      (∑ i : Fin N, if xs i then (1 : ℝ) else 0) |
      Fin.mOfFn N X] ≤
      ENNReal.ofReal (Real.exp (-(2 * Δ ^ 2 / N))) := by
  classical
  let p : Fin N → PMF Bool := fun i => HasEvalPMF.toPMF (X i)
  let μ : Measure (Fin N → Bool) := Measure.pi fun i => (p i).toMeasure
  let Y : Fin N → (Fin N → Bool) → ℝ :=
    fun i xs => (if xs i then (1 : ℝ) else 0) -
      ∫ xs, (if xs i then (1 : ℝ) else 0) ∂μ
  have hmean : ∀ i : Fin N,
      ∫ xs : Fin N → Bool, (if xs i then (1 : ℝ) else 0) ∂μ =
        (Pr[= true | X i]).toReal := by
    intro i
    dsimp [μ, p]
    exact coordinate_mean X i
  have h_indep_coord : iIndepFun (fun i (xs : Fin N → Bool) => xs i) μ := by
    dsimp [μ, p]
    exact ProbabilityTheory.iIndepFun_pi
      (μ := fun i => (HasEvalPMF.toPMF (X i)).toMeasure)
      (X := fun _ (b : Bool) => b) (fun _ => measurable_id.aemeasurable)
  have h_indep : iIndepFun Y μ := by
    refine h_indep_coord.comp (fun i b => (if b then (1 : ℝ) else 0) -
      ∫ xs : Fin N → Bool, (if xs i then (1 : ℝ) else 0) ∂μ) ?_
    intro i
    exact measurable_of_finite _
  have h_subG : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      HasSubgaussianMGF (Y i) ((1 : NNReal) / 4) μ := by
    intro i hi
    have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (μ := μ)
      (X := fun xs : Fin N → Bool => if xs i then (1 : ℝ) else 0)
      (a := 0) (b := 1) (by exact (measurable_of_finite _).aemeasurable) ?_
    · have hc : ((2 : NNReal) ^ 2)⁻¹ = (4 : NNReal)⁻¹ := by norm_num
      simpa [Y, hc] using h
    · filter_upwards with xs
      by_cases hxi : xs i <;> simp [hxi]
  have hHoeff := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (μ := μ) (X := Y) (c := fun _ : Fin N => ((1 : NNReal) / 4)) h_indep
    (s := Finset.univ) h_subG (show 0 ≤ Δ from hΔ.le)
  have hset : {xs : Fin N → Bool | Δ ≤ ∑ i ∈ (Finset.univ : Finset (Fin N)), Y i xs} =
      {xs | bernoulliSumMean X + Δ ≤ ∑ i : Fin N, if xs i then (1 : ℝ) else 0} := by
    ext xs
    simp [Y, bernoulliSumMean, hmean, Finset.sum_sub_distrib]
    constructor <;> intro h <;> linarith
  have hden : Real.exp (-Δ ^ 2 / (2 * ↑(∑ i : Fin N, ((1 : NNReal) / 4)))) =
      Real.exp (-(2 * Δ ^ 2 / N)) := by
    congr 1
    have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
    have hsum : ((↑(∑ i : Fin N, ((1 : NNReal) / 4)) : ℝ)) = N / 4 := by
      simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    rw [hsum]
    field_simp [hNreal]
    ring
  have hreal : (Pr[fun xs => bernoulliSumMean X + Δ ≤
      (∑ i : Fin N, if xs i then (1 : ℝ) else 0) | Fin.mOfFn N X]).toReal ≤
      Real.exp (-(2 * Δ ^ 2 / N)) := by
    have hprob : Pr[fun xs => bernoulliSumMean X + Δ ≤
        (∑ i : Fin N, if xs i then (1 : ℝ) else 0) | Fin.mOfFn N X] =
        μ {xs | bernoulliSumMean X + Δ ≤ ∑ i : Fin N, if xs i then (1 : ℝ) else 0} := by
      rw [probEvent_eq_toPMF_toMeasure]
      · rw [toPMF_mOfFn_bool, piBoolPMF_toMeasure]
      · measurability
    rw [hprob, ← measureReal_def]
    rw [← hset]
    exact hHoeff.trans_eq hden
  exact (ENNReal.le_ofReal_iff_toReal_le probEvent_ne_top (Real.exp_pos _).le).2 hreal

lemma chernoff_half_of_mean_le_quarter {t : ℕ} (ht : 0 < t)
    (X : Fin t → ProbComp Bool)
    (hmean : bernoulliSumMean X ≤ (t : ℝ) / 4) :
    Pr[fun xs => (t : ℝ) / 2 ≤ ∑ i : Fin t, if xs i then (1 : ℝ) else 0 |
      Fin.mOfFn t X] ≤ ENNReal.ofReal (Real.exp (-(t : ℝ) / 8)) := by
  have hΔ : 0 < (t : ℝ) / 4 := by positivity
  have hchern := chernoff_bound (N := t) ht X (Δ := (t : ℝ) / 4) hΔ
  refine (probEvent_mono (mx := Fin.mOfFn t X)
    (q := fun xs => bernoulliSumMean X + (t : ℝ) / 4 ≤
      ∑ i : Fin t, if xs i then (1 : ℝ) else 0) ?_).trans ?_
  · intro xs _ hxs
    nlinarith
  · refine hchern.trans_eq ?_
    congr 1
    congr 1
    have htne : (t : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt ht
    field_simp [htne]
    ring

private lemma one_quarter_ne_top : (1 / 4 : ℝ≥0∞) ≠ ∞ := by
  exact ENNReal.div_ne_top (by simp) (by norm_num)

lemma bernoulliSumMean_le_quarter {t : ℕ} (X : Fin t → ProbComp Bool)
    (hX : ∀ i : Fin t, Pr[= true | X i] ≤ (1 / 4 : ℝ≥0∞)) :
    bernoulliSumMean X ≤ (t : ℝ) / 4 := by
  calc
    bernoulliSumMean X = ∑ i : Fin t, (Pr[= true | X i]).toReal := rfl
    _ ≤ ∑ _i : Fin t, (1 / 4 : ℝ) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hi := ENNReal.toReal_mono one_quarter_ne_top (hX i)
      simpa using hi
    _ = (t : ℝ) / 4 := by
      simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- Run an LPCP-style vector query against a PCP truth table. -/
def truthTableImpl (n : ℕ) :
    QueryImpl (LPCP.fullSpec (ZMod 2) n) (OracleComp (PCP.fullSpec (ZMod 2) (2 ^ n)))
  | .inl () => query (spec := PCP.fullSpec (ZMod 2) (2 ^ n)) (.inl ())
  | .inr a => query (spec := PCP.fullSpec (ZMod 2) (2 ^ n)) (.inr (truthTableIndex n a))

lemma queryBound_simulateQ_truthTableImpl {n : ℕ} {α : Type}
    {oa : OracleComp (LPCP.fullSpec (ZMod 2) n) α} {r q : ℕ}
    (hoa : QueryBound oa r q) :
    QueryBound (simulateQ (truthTableImpl n) oa) r q := by
  revert q r
  induction oa using OracleComp.inductionOn with
  | pure _ =>
      intro q r hoa
      simp
  | query_bind t mx ih =>
      intro q r hoa
      rw [QueryBound, OracleComp.isQueryBound_query_bind_iff] at hoa
      cases t with
      | inl u =>
          rcases u
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
            OracleQuery.input_query, truthTableImpl]
          rw [QueryBound, OracleComp.isQueryBound_query_bind_iff]
          exact ⟨hoa.1, fun y => ih y (hoa.2 y)⟩
      | inr _ =>
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
            OracleQuery.input_query, truthTableImpl]
          rw [QueryBound, OracleComp.isQueryBound_query_bind_iff]
          exact ⟨hoa.1, fun y => ih y (hoa.2 y)⟩

lemma simulateQ_truthTableImpl_encodedProof_eq {n : ℕ}
    (π : Fin n → ZMod 2) {α : Type}
    (oa : OracleComp (LPCP.fullSpec (ZMod 2) n) α) :
    simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle (encodedProof π)).impl)
      (simulateQ (truthTableImpl n) oa) =
      simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) oa := by
  induction oa using OracleComp.inductionOn with
  | pure _ =>
      simp
  | query_bind oracle mx ih =>
      cases oracle with
      | inl u =>
          rcases u
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
            OracleQuery.input_query, truthTableImpl]
          refine bind_congr fun y => ?_
          exact ih y
      | inr a =>
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
            OracleQuery.input_query, truthTableImpl]
          simp [encodedProof_truthTableIndex]
          let ans : ZMod 2 := π ⬝ᵥ a
          exact ih ans

lemma simulateQ_truthTableImpl_table_eq {n : ℕ}
    (πhat : Fin (2 ^ n) → ZMod 2) {α : Type}
    (oa : OracleComp (LPCP.fullSpec (ZMod 2) n) α) :
    simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
      (simulateQ (truthTableImpl n) oa) =
    simulateQ ((randOracle (ZMod 2)).impl +
      fun v => (return tableFunction πhat v : ProbComp (ZMod 2))) oa := by
  induction oa using OracleComp.inductionOn with
  | pure _ =>
      simp
  | query_bind oracle mx ih =>
      cases oracle with
      | inl u =>
          rcases u
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
            OracleQuery.input_query, truthTableImpl]
          refine bind_congr fun y => ?_
          exact ih y
      | inr a =>
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
            OracleQuery.input_query, truthTableImpl]
          simp [tableFunction]
          let ans : ZMod 2 := tableFunction πhat a
          exact ih ans

lemma blrPrecheck_encodedProof_accepts {n : ℕ} (π : Fin n → ZMod 2) :
    Pr[= true |
      simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle (encodedProof π)).impl)
        (simulateQ (truthTableImpl n) (BLR.basicVerifier (F := ZMod 2) (n := n)))] = 1 := by
  rw [simulateQ_truthTableImpl_encodedProof_eq π
    (BLR.basicVerifier (F := ZMod 2) (n := n))]
  by_cases hn : n = 0
  · subst n
    simp [BLR.basicVerifier, BLR.basicSampleVector, Fin.mOfFn, LPCP.proofOracle]
  · haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    have hlin :
        (fun u : Fin n → ZMod 2 => π ⬝ᵥ u) ∈
          BlrPcp.LinearSet (F := ZMod 2) (Idx := Fin n) := by
      simp [BlrPcp.LinearSet, BlrPcp.IsLinear, BlrPcp.linearFn, BlrPcp.dotProduct]
      exact ⟨π, fun _ => by simp [dotProduct]⟩
    simpa [LPCP.proofOracle] using
      (BLR_basic_completeness_ZMod2 (n := n) (f := fun u : Fin n → ZMod 2 => π ⬝ᵥ u) hlin)

/-- Answer one LPCP linear query using the sampled shifts and plurality decoding. -/
def decodedLinearQuery {n t : ℕ}
    (shifts : Fin t → Fin n → ZMod 2) (a : Fin n → ZMod 2) :
    OracleComp (PCP.fullSpec (ZMod 2) (2 ^ n)) (ZMod 2) := do
  let ys : Fin t → ZMod 2 ← Fin.mOfFn t fun i => do
    let y₁ : ZMod 2 ← query (spec := PCP.fullSpec (ZMod 2) (2 ^ n))
      (.inr (truthTableIndex n fun j => a j + shifts i j))
    let y₀ : ZMod 2 ← query (spec := PCP.fullSpec (ZMod 2) (2 ^ n))
      (.inr (truthTableIndex n (shifts i)))
    pure (y₁ - y₀)
  pure (pluralityZMod2 ys)

def correctedAnswer {n t : ℕ} (πhat : Fin (2 ^ n) → ZMod 2)
    (shifts : Fin t → Fin n → ZMod 2) (a : Fin n → ZMod 2) : ZMod 2 :=
  pluralityZMod2 fun i : Fin t =>
    πhat (truthTableIndex n fun j => a j + shifts i j) -
      πhat (truthTableIndex n (shifts i))

def localCorrectionBad {n : ℕ} (πhat : Fin (2 ^ n) → ZMod 2)
    (π : Fin n → ZMod 2) (a r : Fin n → ZMod 2) : Bool :=
  decide
    (πhat (truthTableIndex n fun j => a j + r j) -
      πhat (truthTableIndex n r) ≠ π ⬝ᵥ a)

private lemma decodedLinearQuery_step_queryBound {n t : ℕ}
    (shifts : Fin t → Fin n → ZMod 2) (a : Fin n → ZMod 2) (i : Fin t) :
    QueryBound
      ((do
        let y₁ : ZMod 2 ← query (spec := PCP.fullSpec (ZMod 2) (2 ^ n))
          (.inr (truthTableIndex n fun j => a j + shifts i j))
        let y₀ : ZMod 2 ← query (spec := PCP.fullSpec (ZMod 2) (2 ^ n))
          (.inr (truthTableIndex n (shifts i)))
        pure (y₁ - y₀)) :
        OracleComp (PCP.fullSpec (ZMod 2) (2 ^ n)) (ZMod 2)) 0 2 := by
  simp only [QueryBound]
  rw [OracleComp.isQueryBound_query_bind_iff]
  refine ⟨by simp, fun _ => ?_⟩
  rw [OracleComp.isQueryBound_query_bind_iff]
  exact ⟨by simp, fun _ => trivial⟩

lemma decodedLinearQuery_queryBound {n t : ℕ}
    (shifts : Fin t → Fin n → ZMod 2) (a : Fin n → ZMod 2) :
    QueryBound (decodedLinearQuery shifts a) 0 (2 * t) := by
  have hys : QueryBound
      (Fin.mOfFn t fun i => ((do
        let y₁ : ZMod 2 ← query (spec := PCP.fullSpec (ZMod 2) (2 ^ n))
          (.inr (truthTableIndex n fun j => a j + shifts i j))
        let y₀ : ZMod 2 ← query (spec := PCP.fullSpec (ZMod 2) (2 ^ n))
          (.inr (truthTableIndex n (shifts i)))
        pure (y₁ - y₀)) :
        OracleComp (PCP.fullSpec (ZMod 2) (2 ^ n)) (ZMod 2))) 0 (2 * t) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (queryBound_mOfFn
        (fun i : Fin t => ((do
          let y₁ : ZMod 2 ← query (spec := PCP.fullSpec (ZMod 2) (2 ^ n))
            (.inr (truthTableIndex n fun j => a j + shifts i j))
          let y₀ : ZMod 2 ← query (spec := PCP.fullSpec (ZMod 2) (2 ^ n))
            (.inr (truthTableIndex n (shifts i)))
          pure (y₁ - y₀)) :
          OracleComp (PCP.fullSpec (ZMod 2) (2 ^ n)) (ZMod 2)))
        (fun i => decodedLinearQuery_step_queryBound shifts a i))
  simpa [decodedLinearQuery] using hys

private lemma mOfFn_pure_const {M : Type → Type} [Monad M] [LawfulMonad M]
    {α : Type} (k : ℕ) (a : α) :
    (Fin.mOfFn k fun _ => (pure a : M α)) =
      pure (fun _ : Fin k => a) := by
  induction k with
  | zero =>
      have hfun : Fin.elim0 = (fun _ : Fin 0 => a) := by
        funext i
        exact Fin.elim0 i
      simp [Fin.mOfFn, hfun]
  | succ k ih =>
      have hfun : Fin.cons a (fun _ : Fin k => a) = (fun _ : Fin (k + 1) => a) := by
        funext i
        cases i using Fin.cases <;> simp
      simp [Fin.mOfFn, ih, hfun]

private lemma mOfFn_pure {M : Type → Type} [Monad M] [LawfulMonad M]
    {α : Type} {k : ℕ} (f : Fin k → α) :
    (Fin.mOfFn k fun i => (pure (f i) : M α)) = pure f := by
  induction k with
  | zero =>
      have hfun : Fin.elim0 = f := by
        funext i
        exact Fin.elim0 i
      simp [Fin.mOfFn, hfun]
  | succ k ih =>
      have htail :
          (Fin.mOfFn k fun i => (pure (f i.succ) : M α)) =
            pure (fun i : Fin k => f i.succ) := ih (fun i => f i.succ)
      have hfun : Fin.cons (f 0) (fun i : Fin k => f i.succ) = f := by
        funext i
        cases i using Fin.cases <;> simp
      simp [Fin.mOfFn, htail, hfun]

private lemma simulateQ_mOfFn_prob {ι α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec ProbComp) (m : ℕ)
    (oa : Fin m → OracleComp spec α) :
    simulateQ impl (Fin.mOfFn m oa) =
      Fin.mOfFn m fun i => simulateQ impl (oa i) := by
  induction m with
  | zero =>
      simp [Fin.mOfFn]
  | succ m ih =>
      simp [Fin.mOfFn, simulateQ_bind, ih]

private lemma map_mOfFn_const {α β : Type} (m : ℕ) (oa : ProbComp α) (f : α → β) :
    (fun xs : Fin m → α => fun i => f (xs i)) <$> (Fin.mOfFn m fun _ => oa) =
      Fin.mOfFn m fun _ => f <$> oa := by
  induction m with
  | zero =>
      have hfun : (fun xs : Fin 0 → α => fun i : Fin 0 => f (xs i)) =
          fun _ => (Fin.elim0 : Fin 0 → β) := by
        funext xs i
        exact Fin.elim0 i
      simp [Fin.mOfFn, hfun]
  | succ m ih =>
      simp only [Fin.mOfFn, map_eq_bind_pure_comp, bind_assoc, pure_bind]
      refine bind_congr fun a => ?_
      simp only [Function.comp_apply, pure_bind]
      change (do
          let xs : Fin m → α ← Fin.mOfFn m fun _ => oa
          pure (fun i : Fin (m + 1) => f ((Fin.cons a xs : Fin (m + 1) → α) i))) =
        (do
          let rest ← Fin.mOfFn m fun _ => f <$> oa
          pure (Fin.cons (f a) rest))
      rw [← ih]
      simp only [map_eq_bind_pure_comp, bind_assoc]
      refine bind_congr fun xs => ?_
      simp only [Function.comp_apply, pure_bind]
      congr 1
      funext i
      cases i using Fin.cases <;> simp

private lemma dotProduct_add_sub_shift {n : ℕ}
    (π a r : Fin n → ZMod 2) :
    π ⬝ᵥ (fun j => a j + r j) - π ⬝ᵥ r = π ⬝ᵥ a := by
  change π ⬝ᵥ (a + r) - π ⬝ᵥ r = π ⬝ᵥ a
  rw [dotProduct_add]
  ring

lemma simulateQ_decodedLinearQuery_encodedProof_eq {n t : ℕ}
    (ht : 0 < t) (π : Fin n → ZMod 2)
    (shifts : Fin t → Fin n → ZMod 2) (a : Fin n → ZMod 2) :
    simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle (encodedProof π)).impl)
      (decodedLinearQuery shifts a) =
      pure (π ⬝ᵥ a) := by
  rw [decodedLinearQuery, simulateQ_bind, simulateQ_mOfFn_prob]
  simp [simulateQ_bind, simulateQ_query,
    OracleQuery.cont_query, OracleQuery.input_query, PCP.proofOracle,
    encodedProof_truthTableIndex, dotProduct_add_sub_shift, mOfFn_pure_const,
    pluralityZMod2_const ht]

lemma simulateQ_decodedLinearQuery_table_eq {n t : ℕ}
    (πhat : Fin (2 ^ n) → ZMod 2)
    (shifts : Fin t → Fin n → ZMod 2) (a : Fin n → ZMod 2) :
    simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
      (decodedLinearQuery shifts a) =
      pure (correctedAnswer πhat shifts a) := by
  rw [decodedLinearQuery, correctedAnswer, simulateQ_bind, simulateQ_mOfFn_prob]
  simp [simulateQ_bind, simulateQ_query,
    OracleQuery.cont_query, OracleQuery.input_query, PCP.proofOracle, mOfFn_pure]

/-- Simulate LPCP oracle queries using a PCP truth table and fixed random shifts. -/
def decodedImpl {n t : ℕ}
    (shifts : Fin t → Fin n → ZMod 2) :
    QueryImpl (LPCP.fullSpec (ZMod 2) n) (OracleComp (PCP.fullSpec (ZMod 2) (2 ^ n)))
  | .inl () => query (spec := PCP.fullSpec (ZMod 2) (2 ^ n)) (.inl ())
  | .inr a => decodedLinearQuery shifts a

def correctedImpl {n t : ℕ} (πhat : Fin (2 ^ n) → ZMod 2)
    (shifts : Fin t → Fin n → ZMod 2) :
    QueryImpl (LPCP.fullSpec (ZMod 2) n) ProbComp
  | .inl () => (randOracle (ZMod 2)).impl ()
  | .inr a => pure (correctedAnswer πhat shifts a)

lemma simulateQ_decodedImpl_encodedProof_eq {n t : ℕ} (ht : 0 < t)
    (π : Fin n → ZMod 2) (shifts : Fin t → Fin n → ZMod 2)
    {α : Type} {oa : OracleComp (LPCP.fullSpec (ZMod 2) n) α} {r q : ℕ}
    (hoa : QueryBound oa r q) :
    simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle (encodedProof π)).impl)
      (simulateQ (decodedImpl shifts) oa) =
      simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) oa := by
  revert r q
  induction oa using OracleComp.inductionOn with
  | pure _ =>
      intro r q hoa
      simp
  | query_bind oracle mx ih =>
      intro r q hoa
      rw [QueryBound, OracleComp.isQueryBound_query_bind_iff] at hoa
      cases oracle with
      | inl u =>
          rcases u
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
            OracleQuery.input_query, decodedImpl]
          refine bind_congr fun y => ?_
          exact ih y (hoa.2 y)
      | inr a =>
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
            OracleQuery.input_query, decodedImpl]
          rw [simulateQ_decodedLinearQuery_encodedProof_eq ht π shifts a]
          let ans : ZMod 2 := π ⬝ᵥ a
          exact ih ans (hoa.2 ans)

lemma simulateQ_decodedImpl_table_eq {n t : ℕ}
    (πhat : Fin (2 ^ n) → ZMod 2) (shifts : Fin t → Fin n → ZMod 2)
    {α : Type} (oa : OracleComp (LPCP.fullSpec (ZMod 2) n) α) :
    simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
      (simulateQ (decodedImpl shifts) oa) =
      simulateQ (correctedImpl πhat shifts) oa := by
  induction oa using OracleComp.inductionOn with
  | pure _ =>
      simp
  | query_bind oracle mx ih =>
      cases oracle with
      | inl u =>
          rcases u
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
            OracleQuery.input_query, decodedImpl, correctedImpl]
          refine bind_congr fun y => ?_
          exact ih y
      | inr a =>
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
            OracleQuery.input_query, decodedImpl, correctedImpl]
          rw [simulateQ_decodedLinearQuery_table_eq]
          let ans : ZMod 2 := correctedAnswer πhat shifts a
          exact ih ans

lemma queryBound_simulateQ_decodedImpl {n t : ℕ}
    (shifts : Fin t → Fin n → ZMod 2) {α : Type}
    {oa : OracleComp (LPCP.fullSpec (ZMod 2) n) α} {r q : ℕ}
    (hoa : QueryBound oa r q) :
    QueryBound (simulateQ (decodedImpl shifts) oa) r (2 * t * q) := by
  revert r q
  induction oa using OracleComp.inductionOn with
  | pure _ =>
      intro r q hoa
      simp
  | query_bind oracle mx ih =>
      intro r q hoa
      rw [QueryBound, OracleComp.isQueryBound_query_bind_iff] at hoa
      cases oracle with
      | inl u =>
          rcases u
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
            OracleQuery.input_query, decodedImpl]
          rw [QueryBound, OracleComp.isQueryBound_query_bind_iff]
          refine ⟨hoa.1, fun y => ?_⟩
          exact queryBound_mono (ih y (hoa.2 y)) (by omega) (by omega)
      | inr a =>
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
            OracleQuery.input_query, decodedImpl]
          have htail : ∀ y : ZMod 2,
              QueryBound (simulateQ (decodedImpl shifts) (mx y)) r (2 * t * (q - 1)) := by
            intro y
            exact ih y (hoa.2 y)
          have hbind :
              QueryBound
                (decodedLinearQuery shifts a >>=
                  fun y => simulateQ (decodedImpl shifts) (mx y))
                (0 + r) ((2 * t) + (2 * t * (q - 1))) :=
            queryBound_bind (decodedLinearQuery_queryBound shifts a) htail
          have hqueries : (2 * t) + (2 * t * (q - 1)) = 2 * t * q := by
            rw [Nat.add_comm, ← Nat.mul_succ]
            have hq : (q - 1).succ = q := by omega
            rw [hq]
          exact queryBound_mono hbind (by rw [hqueries]) (by omega)

/-- The PCP verifier obtained from an LPCP verifier over `ZMod 2`. -/
def verifier {α : Type} (size : α → ℕ) (ℓ q : ℕ → ℕ)
    (V : LPCPVerifier α size (ZMod 2) ℓ) :
    PCPVerifier α size (ZMod 2) (fun n => 2 ^ (ℓ n)) :=
  fun x => do
    let ok ← simulateQ (truthTableImpl (ℓ (size x)))
      (BLR.basicVerifier (F := ZMod 2) (n := ℓ (size x)))
    if ok then
      let shifts : Fin (numShifts q (size x)) → Fin (ℓ (size x)) → ZMod 2 ←
        sampleShifts (ℓ (size x)) (numShifts q (size x))
      simulateQ (decodedImpl shifts) (V x)
    else
      pure false

private lemma probOutput_bind_if_true_eq (oa ob : ProbComp Bool)
    (hoa : Pr[= true | oa] = 1) :
    Pr[= true | do
      let ok ← oa
      if ok then ob else pure false] = Pr[= true | ob] := by
  rw [probOutput_bind_eq_tsum, tsum_bool]
  simp [hoa]

private lemma probOutput_bind_if_true_le (oa ob : ProbComp Bool) :
    Pr[= true | do
      let ok ← oa
      if ok then ob else pure false] ≤ Pr[= true | oa] := by
  rw [probOutput_bind_eq_tsum, tsum_bool]
  simp

private lemma probOutput_bind_if_true_le_right (oa ob : ProbComp Bool) :
    Pr[= true | do
      let ok ← oa
      if ok then ob else pure false] ≤ Pr[= true | ob] := by
  rw [probOutput_bind_eq_tsum, tsum_bool]
  simp

private lemma probOutput_bind_le_bad_add {σ : Type} (ms : ProbComp σ) (bad : σ → Prop)
    (A B : σ → ProbComp Bool)
    (hgood : ∀ s ∈ support ms, ¬ bad s → Pr[= true | A s] ≤ Pr[= true | B s]) :
    Pr[= true | ms >>= A] ≤ Pr[bad | ms] + Pr[= true | ms >>= B] := by
  classical
  rw [probOutput_bind_eq_tsum, probEvent_eq_tsum_ite, probOutput_bind_eq_tsum]
  calc
    (∑' s : σ, Pr[= s | ms] * Pr[= true | A s])
        ≤ ∑' s : σ, Pr[= s | ms] * ((if bad s then 1 else 0) + Pr[= true | B s]) := by
          refine ENNReal.tsum_le_tsum fun s => ?_
          by_cases hs : s ∈ support ms
          · by_cases hb : bad s
            · simp only [hb, ↓reduceIte]
              exact mul_le_mul' le_rfl (probOutput_le_one.trans le_self_add)
            · simp only [hb, ↓reduceIte, zero_add]
              exact mul_le_mul' le_rfl (hgood s hs hb)
          · simp [probOutput_eq_zero_of_not_mem_support hs]
    _ = ∑' s : σ, (Pr[= s | ms] * (if bad s then 1 else 0) +
          Pr[= s | ms] * Pr[= true | B s]) := by
          apply tsum_congr
          intro s
          rw [mul_add]
    _ = (∑' s : σ, Pr[= s | ms] * (if bad s then 1 else 0)) +
          ∑' s : σ, Pr[= s | ms] * Pr[= true | B s] := by
          rw [ENNReal.tsum_add]
    _ = (∑' s : σ, (if bad s then Pr[= s | ms] else 0)) +
          ∑' s : σ, Pr[= s | ms] * Pr[= true | B s] := by
          congr 1
          apply tsum_congr
          intro s
          by_cases hb : bad s <;> simp [hb]

lemma verifier_encodedProof_probOutput_true_eq {α : Type}
    (size : α → ℕ) (ℓ q : ℕ → ℕ)
    (V : LPCPVerifier α size (ZMod 2) ℓ) (x : α)
    (π : Fin (ℓ (size x)) → ZMod 2)
    {r : ℕ} (hQuery : QueryBound (V x) r (q (size x))) :
    Pr[= true |
      simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle (encodedProof π)).impl)
        ((verifier size ℓ q V) x)] =
    Pr[= true |
      simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) (V x)] := by
  let n := ℓ (size x)
  let t := numShifts q (size x)
  have ht : 0 < t := by
    simpa [t] using numShifts_pos q (size x)
  have hBLR :
      Pr[= true |
        simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle (encodedProof π)).impl)
          (simulateQ (truthTableImpl n) (BLR.basicVerifier (F := ZMod 2) (n := n)))] = 1 := by
    simpa [n] using blrPrecheck_encodedProof_accepts (n := n) π
  rw [verifier]
  simp only [simulateQ_bind, simulateQ_ite, simulateQ_pure]
  rw [probOutput_bind_if_true_eq _ _ hBLR]
  simp_rw [simulateQ_decodedImpl_encodedProof_eq (ht := ht) (π := π)
    (hoa := hQuery)]
  rw [probOutput_bind_const]
  simp

lemma verifier_completeness {α : Type} (size : α → ℕ) (ε_c : ℝ≥0∞)
    (ℓ q r : ℕ → ℕ) (V : LPCPVerifier α size (ZMod 2) ℓ) (x : α)
    (hQuery : QueryBound (V x) (r (size x)) (q (size x)))
    (hComplete :
      ∃ π : Fin (ℓ (size x)) → ZMod 2,
        Pr[= true |
          simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) (V x)]
          ≥ 1 - ε_c) :
    ∃ πbar : Fin (2 ^ ℓ (size x)) → ZMod 2,
      Pr[= true |
        simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πbar).impl)
          ((verifier size ℓ q V) x)] ≥ 1 - ε_c := by
  rcases hComplete with ⟨π, hπ⟩
  refine ⟨encodedProof π, ?_⟩
  rw [verifier_encodedProof_probOutput_true_eq size ℓ q V x π hQuery]
  exact hπ

lemma verifier_accept_le_blrPrecheck_accept {α : Type}
    (size : α → ℕ) (ℓ q : ℕ → ℕ)
    (V : LPCPVerifier α size (ZMod 2) ℓ) (x : α)
    (πhat : Fin (2 ^ ℓ (size x)) → ZMod 2) :
    Pr[= true |
      simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
        ((verifier size ℓ q V) x)] ≤
    Pr[= true |
      simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
        (simulateQ (truthTableImpl (ℓ (size x)))
          (BLR.basicVerifier (F := ZMod 2) (n := ℓ (size x))))] := by
  rw [verifier]
  simp only [simulateQ_bind, simulateQ_ite, simulateQ_pure]
  exact probOutput_bind_if_true_le _ _

private lemma seven_eighths_ne_top : (7 / 8 : ℝ≥0∞) ≠ ∞ := by
  exact ENNReal.div_ne_top (by simp) (by norm_num)

private lemma one_eighth_ne_top : (1 / 8 : ℝ≥0∞) ≠ ∞ := by
  exact ENNReal.div_ne_top (by simp) (by norm_num)

private lemma one_eighth_add_one_eighth_eq_one_quarter :
    (1 / 8 : ℝ≥0∞) + 1 / 8 = 1 / 4 := by
  refine (ENNReal.toReal_eq_toReal_iff' ?_ one_quarter_ne_top).1 ?_
  · exact ENNReal.add_ne_top.2 ⟨one_eighth_ne_top, one_eighth_ne_top⟩
  · rw [ENNReal.toReal_add one_eighth_ne_top one_eighth_ne_top]
    norm_num [ENNReal.toReal_div]

private lemma one_eq_seven_eighths_add_one_eighth :
    (1 : ℝ≥0∞) = 7 / 8 + 1 / 8 := by
  refine (ENNReal.toReal_eq_toReal_iff' (by simp) ?_).1 ?_
  · exact ENNReal.add_ne_top.2 ⟨seven_eighths_ne_top, one_eighth_ne_top⟩
  · rw [ENNReal.toReal_add seven_eighths_ne_top one_eighth_ne_top]
    norm_num

private lemma one_le_seven_eighths_add_of_one_eighth_le {p : ℝ≥0∞}
    (hp : (1 / 8 : ℝ≥0∞) ≤ p) :
    (1 : ℝ≥0∞) ≤ 7 / 8 + p := by
  calc
    (1 : ℝ≥0∞) = 7 / 8 + 1 / 8 := one_eq_seven_eighths_add_one_eighth
    _ ≤ 7 / 8 + p := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hp (7 / 8 : ℝ≥0∞)

private lemma eta_add_pred_mul_le {q : ℕ} (hq : 0 < q) (η P : ℝ≥0∞) :
    η + (P + ((q - 1 : ℕ) : ℝ≥0∞) * η) ≤ P + (q : ℝ≥0∞) * η := by
  have hnat : q = (q - 1) + 1 := by omega
  have hqeq : (q : ℝ≥0∞) = ((q - 1 : ℕ) : ℝ≥0∞) + 1 := by
    rw [hnat]
    norm_num
  calc
    η + (P + ((q - 1 : ℕ) : ℝ≥0∞) * η)
        = P + (((q - 1 : ℕ) : ℝ≥0∞) * η + η) := by
          rw [← add_assoc, add_comm η P, add_assoc]
          rw [add_comm η (((q - 1 : ℕ) : ℝ≥0∞) * η)]
    _ = P + ((((q - 1 : ℕ) : ℝ≥0∞) + 1) * η) := by
          rw [add_mul, one_mul]
    _ ≤ P + (q : ℝ≥0∞) * η := by rw [← hqeq]

lemma corrected_run_accept_le_linear_add {n t : ℕ}
    (πhat : Fin (2 ^ n) → ZMod 2) (π : Fin n → ZMod 2)
    (η : ℝ≥0∞) {oa : OracleComp (LPCP.fullSpec (ZMod 2) n) Bool} {r q : ℕ}
    (hoa : QueryBound oa r q)
    (hQuery : ∀ a : Fin n → ZMod 2,
      Pr[fun shifts => correctedAnswer πhat shifts a ≠ π ⬝ᵥ a |
        simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
          (sampleShifts n t)] ≤ η) :
    Pr[= true | do
      let shifts ← simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
        (sampleShifts n t)
      simulateQ (correctedImpl πhat shifts) oa] ≤
    Pr[= true |
      simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) oa] +
      (q : ℝ≥0∞) * η := by
  let S : ProbComp (Fin t → Fin n → ZMod 2) :=
    simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl) (sampleShifts n t)
  change Pr[= true | S >>= fun shifts => simulateQ (correctedImpl πhat shifts) oa] ≤
    Pr[= true | simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) oa] +
      (q : ℝ≥0∞) * η
  revert r q
  induction oa using OracleComp.inductionOn with
  | pure b =>
      intro r q _hoa
      simp [S]
  | query_bind oracle mx ih =>
      intro r q hoa
      rw [QueryBound, OracleComp.isQueryBound_query_bind_iff] at hoa
      cases oracle with
      | inl u =>
          rcases u
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
            OracleQuery.input_query, correctedImpl, LPCP.proofOracle]
          rw [probOutput_bind_bind_swap]
          simpa [probEvent_eq_eq_probOutput] using
            (probEvent_bind_congr_le_add
              (mx := (randOracle (ZMod 2)).impl ())
              (my := fun y : ZMod 2 =>
                S >>= fun shifts => simulateQ (correctedImpl πhat shifts) (mx y))
              (oc := fun y : ZMod 2 =>
                simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) (mx y))
              (q := fun b : Bool => b = true)
              (ε := (q : ℝ≥0∞) * η)
              (by
                intro y _hy
                simpa [probEvent_eq_eq_probOutput] using ih y (hoa.2 y)))
      | inr a =>
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
            OracleQuery.input_query, correctedImpl, LPCP.proofOracle]
          let ans : ZMod 2 := π ⬝ᵥ a
          have hbad : Pr[fun shifts => correctedAnswer πhat shifts a ≠ ans | S] ≤ η := by
            simpa [S, ans] using hQuery a
          have hsplit :
              Pr[= true | S >>= fun shifts =>
                simulateQ (correctedImpl πhat shifts) (mx (correctedAnswer πhat shifts a))] ≤
              η + Pr[= true | S >>= fun shifts =>
                simulateQ (correctedImpl πhat shifts) (mx ans)] := by
            refine (probOutput_bind_le_bad_add S
              (fun shifts => correctedAnswer πhat shifts a ≠ ans)
              (fun shifts =>
                simulateQ (correctedImpl πhat shifts) (mx (correctedAnswer πhat shifts a)))
              (fun shifts => simulateQ (correctedImpl πhat shifts) (mx ans)) ?_).trans ?_
            · intro shifts _hshifts hgood
              have hcorr : correctedAnswer πhat shifts a = ans := not_not.mp hgood
              simp [hcorr]
            · exact add_le_add_left hbad _
          have htail := ih ans (hoa.2 ans)
          have hqpos : 0 < q := hoa.1
          calc
            Pr[= true | S >>= fun shifts =>
                simulateQ (correctedImpl πhat shifts) (mx (correctedAnswer πhat shifts a))]
                ≤ η + Pr[= true | S >>= fun shifts =>
                    simulateQ (correctedImpl πhat shifts) (mx ans)] := hsplit
            _ ≤ η + (Pr[= true |
                    simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl)
                      (mx ans)] +
                  ((q - 1 : ℕ) : ℝ≥0∞) * η) := add_le_add le_rfl htail
            _ ≤ Pr[= true |
                    simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl)
                      (mx ans)] +
                  (q : ℝ≥0∞) * η := eta_add_pred_mul_le hqpos η _

lemma pluralityZMod2_bad_count_ge_half {t : ℕ} (ys : Fin t → ZMod 2) (b : ZMod 2)
    (hbad : pluralityZMod2 ys ≠ b) :
    (t : ℝ) / 2 ≤ ∑ i : Fin t, if ys i ≠ b then (1 : ℝ) else 0 := by
  classical
  fin_cases b
  · unfold pluralityZMod2 at hbad
    by_cases h : Fintype.card { i : Fin t // ys i = 1 } * 2 > t
    · simp [h] at hbad
      have hsum : (∑ i : Fin t, if ys i ≠ 0 then (1 : ℝ) else 0) =
          Fintype.card { i : Fin t // ys i = 1 } := by
        have hpred : ∀ i : Fin t, (ys i ≠ 0) ↔ (ys i = 1) := by
          intro i
          have h01 : ∀ x : ZMod 2, x ≠ 0 ↔ x = 1 := by
            intro x
            fin_cases x <;> simp
          exact h01 (ys i)
        simp_rw [hpred]
        simp [Fintype.card_subtype]
      change (t : ℝ) / 2 ≤ ∑ i : Fin t, if ys i ≠ (0 : ZMod 2) then (1 : ℝ) else 0
      rw [hsum]
      have hreal : ((Fintype.card { i : Fin t // ys i = 1 }) : ℝ) * 2 > t := by
        exact_mod_cast h
      nlinarith
    · simp [h] at hbad
  · unfold pluralityZMod2 at hbad
    by_cases h : Fintype.card { i : Fin t // ys i = 1 } * 2 > t
    · simp [h] at hbad
    · simp [h] at hbad
      have hle : Fintype.card { i : Fin t // ys i = 1 } * 2 ≤ t := by omega
      have hsum1 : (∑ i : Fin t, if ys i = 1 then (1 : ℝ) else 0) =
          Fintype.card { i : Fin t // ys i = 1 } := by
        simp [Fintype.card_subtype]
      have hsumBad : (∑ i : Fin t, if ys i ≠ 1 then (1 : ℝ) else 0) =
          t - Fintype.card { i : Fin t // ys i = 1 } := by
        have htotal : (∑ i : Fin t, (1 : ℝ)) = t := by simp
        have hsplit : (∑ i : Fin t, (1 : ℝ)) =
            (∑ i : Fin t, if ys i = 1 then (1 : ℝ) else 0) +
            (∑ i : Fin t, if ys i ≠ 1 then (1 : ℝ) else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _hi
          by_cases hy : ys i = 1 <;> simp [hy]
        nlinarith [hsum1, htotal, hsplit]
      change (t : ℝ) / 2 ≤ ∑ i : Fin t, if ys i ≠ (1 : ZMod 2) then (1 : ℝ) else 0
      rw [hsumBad]
      have hlereal : ((Fintype.card { i : Fin t // ys i = 1 }) : ℝ) * 2 ≤ t := by
        exact_mod_cast hle
      nlinarith

lemma correctedAnswer_failure_le_exp_of_mean {n t : ℕ} (ht : 0 < t)
    (πhat : Fin (2 ^ n) → ZMod 2) (π : Fin n → ZMod 2) (a : Fin n → ZMod 2)
    (hmean :
      bernoulliSumMean (fun _ : Fin t =>
        (localCorrectionBad πhat π a) <$>
          simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
            (sampleVector (ZMod 2) n (N := 2 ^ n))) ≤ (t : ℝ) / 4) :
    Pr[fun shifts => correctedAnswer πhat shifts a ≠ π ⬝ᵥ a |
      simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
        (sampleShifts n t)] ≤ ENNReal.ofReal (Real.exp (-(t : ℝ) / 8)) := by
  classical
  let ctx := ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
  let sampleOne : ProbComp (Fin n → ZMod 2) :=
    simulateQ ctx (sampleVector (ZMod 2) n (N := 2 ^ n))
  let bad : (Fin n → ZMod 2) → Bool := localCorrectionBad πhat π a
  let X : Fin t → ProbComp Bool := fun _ => bad <$> sampleOne
  have hS :
      simulateQ ctx (sampleShifts n t) = Fin.mOfFn t fun _ => sampleOne := by
    simp [sampleShifts, sampleOne, simulateQ_mOfFn_prob]
  have hmap :
      (fun shifts : Fin t → Fin n → ZMod 2 => fun i : Fin t => bad (shifts i)) <$>
        simulateQ ctx (sampleShifts n t) =
      Fin.mOfFn t X := by
    rw [hS]
    exact map_mOfFn_const t sampleOne bad
  have hplurality :
      Pr[fun shifts => correctedAnswer πhat shifts a ≠ π ⬝ᵥ a |
        simulateQ ctx (sampleShifts n t)] ≤
      Pr[fun shifts =>
          (t : ℝ) / 2 ≤
            ∑ i : Fin t, if bad (shifts i) then (1 : ℝ) else 0 |
        simulateQ ctx (sampleShifts n t)] := by
    refine probEvent_mono ?_
    intro shifts _ hbad
    simpa [correctedAnswer, bad, localCorrectionBad] using
      pluralityZMod2_bad_count_ge_half
        (fun i : Fin t =>
          πhat (truthTableIndex n fun j => a j + shifts i j) -
            πhat (truthTableIndex n (shifts i)))
        (π ⬝ᵥ a) hbad
  have hchern :
      Pr[fun xs => (t : ℝ) / 2 ≤ ∑ i : Fin t, if xs i then (1 : ℝ) else 0 |
        Fin.mOfFn t X] ≤ ENNReal.ofReal (Real.exp (-(t : ℝ) / 8)) := by
    refine chernoff_half_of_mean_le_quarter ht X ?_
    simpa [X, bad, sampleOne, ctx] using hmean
  refine hplurality.trans ?_
  change Pr[(fun xs : Fin t → Bool =>
      (t : ℝ) / 2 ≤ ∑ i : Fin t, if xs i then (1 : ℝ) else 0) ∘
        (fun shifts : Fin t → Fin n → ZMod 2 => fun i : Fin t => bad (shifts i)) |
      simulateQ ctx (sampleShifts n t)] ≤ ENNReal.ofReal (Real.exp (-(t : ℝ) / 8))
  rw [← probEvent_map
    (mx := simulateQ ctx (sampleShifts n t))
    (f := fun shifts : Fin t → Fin n → ZMod 2 => fun i : Fin t => bad (shifts i))
    (q := fun xs => (t : ℝ) / 2 ≤ ∑ i : Fin t, if xs i then (1 : ℝ) else 0)]
  rw [hmap]
  exact hchern

lemma correctedAnswer_failure_le_exp_of_single {n t : ℕ} (ht : 0 < t)
    (πhat : Fin (2 ^ n) → ZMod 2) (π : Fin n → ZMod 2) (a : Fin n → ZMod 2)
    (hsingle :
      Pr[= true |
        (localCorrectionBad πhat π a) <$>
          simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
            (sampleVector (ZMod 2) n (N := 2 ^ n))] ≤ (1 / 4 : ℝ≥0∞)) :
    Pr[fun shifts => correctedAnswer πhat shifts a ≠ π ⬝ᵥ a |
      simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
        (sampleShifts n t)] ≤ ENNReal.ofReal (Real.exp (-(t : ℝ) / 8)) := by
  refine correctedAnswer_failure_le_exp_of_mean ht πhat π a ?_
  apply bernoulliSumMean_le_quarter
  intro _i
  simpa using hsingle

private def vectorShiftEquiv {n : ℕ} (a : Fin n → ZMod 2) :
    (Fin n → ZMod 2) ≃ (Fin n → ZMod 2) where
  toFun r := fun j => a j + r j
  invFun r := fun j => r j - a j
  left_inv r := by
    funext j
    ring
  right_inv r := by
    funext j
    ring

lemma probEvent_sampleVector_disagree_eq_distance {n : ℕ} [Nonempty (Fin n)]
    (πhat : Fin (2 ^ n) → ZMod 2) (π : Fin n → ZMod 2) :
    Pr[fun r : Fin n → ZMod 2 =>
        tableFunction πhat r ≠ BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π r |
      simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
        (sampleVector (ZMod 2) n (N := 2 ^ n))] =
      ENNReal.ofReal
        (BlrPcp.distance (F := ZMod 2) (Idx := Fin n)
          (tableFunction πhat) (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π)) := by
  classical
  have hprob :
      Pr[fun r : Fin n → ZMod 2 =>
          tableFunction πhat r ≠ BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π r |
        simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
          (sampleVector (ZMod 2) n (N := 2 ^ n))] =
        ∑ y : Fin n → ZMod 2,
          (Fintype.card (Fin n → ZMod 2) : ℝ≥0∞)⁻¹ *
            if tableFunction πhat y ≠
              BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π y then 1 else 0 := by
    simpa using
      (probEvent_simulateQ_sampleVector_eq_sum
        (F := ZMod 2) (m := n) (N := 2 ^ n)
        (impl := (PCP.proofOracle πhat).impl)
        (p := fun r : Fin n → ZMod 2 =>
          tableFunction πhat r ≠ BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π r))
  rw [hprob]
  rw [BlrPcp.distance]
  have hcard_pos : 0 < (Fintype.card (Fin n → ZMod 2) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨0⟩
  rw [ENNReal.ofReal_mul]
  · rw [ENNReal.ofReal_inv_of_pos hcard_pos]
    rw [ENNReal.ofReal_sum_of_nonneg]
    · simp only [ENNReal.ofReal_natCast]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr :
          tableFunction πhat r ≠ BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π r <;>
        simp [hr]
    · intro r _
      by_cases hr :
          tableFunction πhat r ≠ BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π r <;>
        simp [hr]
  · positivity

lemma probEvent_sampleVector_shift_disagree_eq_distance {n : ℕ} [Nonempty (Fin n)]
    (πhat : Fin (2 ^ n) → ZMod 2) (π a : Fin n → ZMod 2) :
    Pr[fun r : Fin n → ZMod 2 =>
        tableFunction πhat (fun j => a j + r j) ≠
          BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π (fun j => a j + r j) |
      simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
        (sampleVector (ZMod 2) n (N := 2 ^ n))] =
      ENNReal.ofReal
        (BlrPcp.distance (F := ZMod 2) (Idx := Fin n)
          (tableFunction πhat) (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π)) := by
  classical
  let sample :=
    simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
      (sampleVector (ZMod 2) n (N := 2 ^ n))
  let p : (Fin n → ZMod 2) → Prop := fun r =>
    tableFunction πhat r ≠ BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π r
  have hprob :
      Pr[fun r : Fin n → ZMod 2 => p (fun j => a j + r j) |
        simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
          (sampleVector (ZMod 2) n (N := 2 ^ n))] =
        ∑ y : Fin n → ZMod 2,
          (Fintype.card (Fin n → ZMod 2) : ℝ≥0∞)⁻¹ *
            if p (fun j => a j + y j) then 1 else 0 := by
    simpa using
      (probEvent_simulateQ_sampleVector_eq_sum
        (F := ZMod 2) (m := n) (N := 2 ^ n)
        (impl := (PCP.proofOracle πhat).impl)
        (p := fun r : Fin n → ZMod 2 => p (fun j => a j + r j)))
  rw [hprob]
  have hsum :
      (∑ r : Fin n → ZMod 2,
          (Fintype.card (Fin n → ZMod 2) : ℝ≥0∞)⁻¹ *
            if p (fun j => a j + r j) then 1 else 0) =
        ∑ r : Fin n → ZMod 2,
          (Fintype.card (Fin n → ZMod 2) : ℝ≥0∞)⁻¹ *
            if p r then 1 else 0 := by
    simpa [vectorShiftEquiv, p] using
      (Equiv.sum_comp (vectorShiftEquiv a)
        (fun r : Fin n → ZMod 2 =>
          (Fintype.card (Fin n → ZMod 2) : ℝ≥0∞)⁻¹ *
            if p r then 1 else 0))
  rw [hsum]
  have hunshift :
      Pr[p |
        simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
          (sampleVector (ZMod 2) n (N := 2 ^ n))] =
        ∑ r : Fin n → ZMod 2,
          (Fintype.card (Fin n → ZMod 2) : ℝ≥0∞)⁻¹ *
            if p r then 1 else 0 := by
    simpa [p] using
      (probEvent_simulateQ_sampleVector_eq_sum
        (F := ZMod 2) (m := n) (N := 2 ^ n)
        (impl := (PCP.proofOracle πhat).impl)
        (p := p))
  rw [← hunshift]
  simpa [p] using probEvent_sampleVector_disagree_eq_distance (n := n) πhat π

lemma localCorrectionBad_single_le_two_distance {n : ℕ} [Nonempty (Fin n)]
    (πhat : Fin (2 ^ n) → ZMod 2) (π a : Fin n → ZMod 2) :
    Pr[= true |
      (localCorrectionBad πhat π a) <$>
        simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
          (sampleVector (ZMod 2) n (N := 2 ^ n))] ≤
      ENNReal.ofReal
        (BlrPcp.distance (F := ZMod 2) (Idx := Fin n)
          (tableFunction πhat) (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π)) +
      ENNReal.ofReal
        (BlrPcp.distance (F := ZMod 2) (Idx := Fin n)
          (tableFunction πhat) (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π)) := by
  classical
  let sample :=
    simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
      (sampleVector (ZMod 2) n (N := 2 ^ n))
  let f : (Fin n → ZMod 2) → ZMod 2 := tableFunction πhat
  let lin : (Fin n → ZMod 2) → ZMod 2 :=
    BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π
  have hbad_imp : ∀ r : Fin n → ZMod 2,
      localCorrectionBad πhat π a r = true →
        f (fun j => a j + r j) ≠ lin (fun j => a j + r j) ∨ f r ≠ lin r := by
    intro r hbad
    by_cases hshift : f (fun j => a j + r j) ≠ lin (fun j => a j + r j)
    · exact Or.inl hshift
    · by_cases hr : f r ≠ lin r
      · exact Or.inr hr
      · have hshift_eq :
            f (fun j => a j + r j) = lin (fun j => a j + r j) := not_not.mp hshift
        have hr_eq : f r = lin r := not_not.mp hr
        have hcorr :
            πhat (truthTableIndex n fun j => a j + r j) -
                πhat (truthTableIndex n r) = π ⬝ᵥ a := by
          have hlin :
              lin (fun j => a j + r j) - lin r = π ⬝ᵥ a := by
            simpa [lin, BlrPcp.linearFn] using dotProduct_add_sub_shift π a r
          rw [← hshift_eq, ← hr_eq] at hlin
          simpa [f, tableFunction] using hlin
        simp [localCorrectionBad, hcorr] at hbad
  have hmono :
      Pr[= true | (localCorrectionBad πhat π a) <$> sample] ≤
      Pr[fun r : Fin n → ZMod 2 =>
          f (fun j => a j + r j) ≠ lin (fun j => a j + r j) ∨ f r ≠ lin r |
        sample] := by
    rw [← probEvent_eq_eq_probOutput, probEvent_map]
    refine probEvent_mono ?_
    intro r _ hbad
    exact hbad_imp r hbad
  have hunion :
      Pr[fun r : Fin n → ZMod 2 =>
          f (fun j => a j + r j) ≠ lin (fun j => a j + r j) ∨ f r ≠ lin r |
        sample] ≤
      Pr[fun r : Fin n → ZMod 2 =>
          f (fun j => a j + r j) ≠ lin (fun j => a j + r j) |
        sample] +
      Pr[fun r : Fin n → ZMod 2 => f r ≠ lin r | sample] := by
    exact probEvent_or_le sample
      (fun r : Fin n → ZMod 2 =>
        f (fun j => a j + r j) ≠ lin (fun j => a j + r j))
      (fun r : Fin n → ZMod 2 => f r ≠ lin r)
  calc
    Pr[= true | (localCorrectionBad πhat π a) <$> sample]
        ≤ Pr[fun r : Fin n → ZMod 2 =>
            f (fun j => a j + r j) ≠ lin (fun j => a j + r j) ∨ f r ≠ lin r |
          sample] := hmono
    _ ≤ Pr[fun r : Fin n → ZMod 2 =>
            f (fun j => a j + r j) ≠ lin (fun j => a j + r j) |
          sample] +
        Pr[fun r : Fin n → ZMod 2 => f r ≠ lin r | sample] := hunion
    _ = ENNReal.ofReal
          (BlrPcp.distance (F := ZMod 2) (Idx := Fin n)
            (tableFunction πhat) (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π)) +
        ENNReal.ofReal
          (BlrPcp.distance (F := ZMod 2) (Idx := Fin n)
            (tableFunction πhat) (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π)) := by
        rw [probEvent_sampleVector_shift_disagree_eq_distance (n := n) πhat π a]
        rw [probEvent_sampleVector_disagree_eq_distance (n := n) πhat π]

lemma localCorrectionBad_single_le_quarter_of_distance_le {n : ℕ} [Nonempty (Fin n)]
    (πhat : Fin (2 ^ n) → ZMod 2) (π : Fin n → ZMod 2)
    (hdist :
      ENNReal.ofReal
        (BlrPcp.distance (F := ZMod 2) (Idx := Fin n)
          (tableFunction πhat) (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π)) ≤
        1 / 8) :
    ∀ a : Fin n → ZMod 2,
      Pr[= true |
        (localCorrectionBad πhat π a) <$>
          simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
            (sampleVector (ZMod 2) n (N := 2 ^ n))] ≤
        (1 / 4 : ℝ≥0∞) := by
  intro a
  have htwo := localCorrectionBad_single_le_two_distance (n := n) πhat π a
  calc
    Pr[= true |
      (localCorrectionBad πhat π a) <$>
        simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
          (sampleVector (ZMod 2) n (N := 2 ^ n))]
        ≤ ENNReal.ofReal
            (BlrPcp.distance (F := ZMod 2) (Idx := Fin n)
              (tableFunction πhat) (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π)) +
          ENNReal.ofReal
            (BlrPcp.distance (F := ZMod 2) (Idx := Fin n)
              (tableFunction πhat) (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π)) := htwo
    _ ≤ 1 / 8 + (1 / 8 : ℝ≥0∞) := add_le_add hdist hdist
    _ = 1 / 4 := one_eighth_add_one_eighth_eq_one_quarter

/-- The blueprint's far case: the PCP truth table is at BLR distance at least `1/8`. -/
def IsFarFromLinear {n : ℕ} (πhat : Fin (2 ^ n) → ZMod 2) : Prop :=
  ∃ hne : Nonempty (Fin n),
    letI : Nonempty (Fin n) := hne
    (1 / 8 : ℝ≥0∞) ≤ distanceToLin (tableFunction πhat)

lemma exists_close_linear_of_not_far {n : ℕ} [Nonempty (Fin n)]
    (πhat : Fin (2 ^ n) → ZMod 2)
    (hnear : ¬ IsFarFromLinear πhat) :
    ∃ π : Fin n → ZMod 2,
      ENNReal.ofReal
        (BlrPcp.distance (F := ZMod 2) (Idx := Fin n)
          (tableFunction πhat) (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π)) <
        1 / 8 := by
  classical
  have hdist_lt : distanceToLin (tableFunction πhat) < (1 / 8 : ℝ≥0∞) := by
    refine lt_of_not_ge ?_
    intro hdist
    exact hnear ⟨inferInstance, hdist⟩
  obtain ⟨π, _hπmem, hπ⟩ :=
    Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset (Fin n → ZMod 2)))
      (H := (Finset.univ_nonempty : (Finset.univ : Finset (Fin n → ZMod 2)).Nonempty))
      (f := fun π : Fin n → ZMod 2 =>
        BlrPcp.distance (F := ZMod 2) (Idx := Fin n)
          (tableFunction πhat) (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π))
  refine ⟨π, ?_⟩
  rw [distanceToLin] at hdist_lt
  rw [BlrPcp.distanceToLinear_eq_inf_linearFn] at hdist_lt
  simpa [hπ] using hdist_lt

lemma localCorrectionBad_single_le_quarter_of_not_far {n : ℕ} [Nonempty (Fin n)]
    (πhat : Fin (2 ^ n) → ZMod 2)
    (hnear : ¬ IsFarFromLinear πhat) :
    ∃ π : Fin n → ZMod 2,
      ∀ a : Fin n → ZMod 2,
        Pr[= true |
          (localCorrectionBad πhat π a) <$>
            simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
              (sampleVector (ZMod 2) n (N := 2 ^ n))] ≤
          (1 / 4 : ℝ≥0∞) := by
  rcases exists_close_linear_of_not_far (n := n) πhat hnear with ⟨π, hπ⟩
  exact ⟨π, localCorrectionBad_single_le_quarter_of_distance_le πhat π (le_of_lt hπ)⟩

lemma localCorrectionBad_single_le_quarter_zero
    (πhat : Fin (2 ^ 0) → ZMod 2) :
    ∃ π : Fin 0 → ZMod 2,
      ∀ a : Fin 0 → ZMod 2,
        Pr[= true |
          (localCorrectionBad πhat π a) <$>
            simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
              (sampleVector (ZMod 2) 0 (N := 2 ^ 0))] ≤
          (1 / 4 : ℝ≥0∞) := by
  refine ⟨0, ?_⟩
  intro a
  rw [← probEvent_eq_eq_probOutput, probEvent_map]
  have hfalse : ∀ r : Fin 0 → ZMod 2, localCorrectionBad πhat 0 a r = false := by
    intro r
    have ha : a = 0 := by
      funext i
      exact Fin.elim0 i
    have hr : r = 0 := by
      funext i
      exact Fin.elim0 i
    subst a
    subst r
    have hsame :
        πhat (truthTableIndex 0 (fun _ : Fin 0 => (0 : ZMod 2))) =
          πhat (truthTableIndex 0 (0 : Fin 0 → ZMod 2)) := by
      apply congrArg πhat
      apply Fin.ext
      omega
    have hcorr :
        πhat (truthTableIndex 0 (fun _ : Fin 0 => (0 : ZMod 2))) -
            πhat (truthTableIndex 0 (0 : Fin 0 → ZMod 2)) =
          (0 : Fin 0 → ZMod 2) ⬝ᵥ (0 : Fin 0 → ZMod 2) := by
      rw [hsame]
      simp
    simpa [localCorrectionBad, hcorr]
  let sample :=
    simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
      (sampleVector (ZMod 2) 0 (N := 2 ^ 0))
  calc
    Pr[(fun x => x = true) ∘ localCorrectionBad πhat 0 a | sample]
        ≤ Pr[fun _ : Fin 0 → ZMod 2 => False | sample] := by
          refine probEvent_mono ?_
          intro r _ h
          change localCorrectionBad πhat 0 a r = true at h
          rw [hfalse r] at h
          simp at h
    _ ≤ (1 / 4 : ℝ≥0∞) := by simp

lemma localCorrectionBad_single_le_quarter_of_length_zero {n : ℕ}
    (hn : n = 0) (πhat : Fin (2 ^ n) → ZMod 2) :
    ∃ π : Fin n → ZMod 2,
      ∀ a : Fin n → ZMod 2,
        Pr[= true |
          (localCorrectionBad πhat π a) <$>
            simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
              (sampleVector (ZMod 2) n (N := 2 ^ n))] ≤
          (1 / 4 : ℝ≥0∞) := by
  subst n
  simpa using localCorrectionBad_single_le_quarter_zero (πhat := πhat)

private lemma real_log_nat_le_nat_log_two_succ (m : ℕ) :
    Real.log (m : ℝ) ≤ (Nat.log 2 m + 1 : ℝ) := by
  by_cases hm : m = 0
  · subst m
    simp
  · have hmposNat : 0 < m := Nat.pos_of_ne_zero hm
    let lf : ℕ := Nat.log 2 m + 1
    have hltNat : m < 2 ^ lf := by
      simpa [lf, Nat.succ_eq_add_one] using
        (Nat.lt_pow_succ_log_self Nat.one_lt_two m)
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmposNat
    have hltReal : (m : ℝ) < ((2 ^ lf : ℕ) : ℝ) := by exact_mod_cast hltNat
    have hloglt : Real.log (m : ℝ) < Real.log (((2 ^ lf : ℕ) : ℝ)) :=
      Real.log_lt_log hmpos hltReal
    have hlogpow : Real.log (((2 ^ lf : ℕ) : ℝ)) = (lf : ℝ) * Real.log 2 := by
      rw [show (((2 ^ lf : ℕ) : ℝ)) = (2 : ℝ) ^ lf by norm_num]
      rw [Real.log_pow]
    have hlog2_le_one : Real.log 2 ≤ (1 : ℝ) := by
      have htwo_le_exp : (2 : ℝ) ≤ Real.exp 1 := by
        linarith [Real.add_one_le_exp (1 : ℝ)]
      exact (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).2 htwo_le_exp
    have hlogpow_le : Real.log (((2 ^ lf : ℕ) : ℝ)) ≤ (lf : ℝ) := by
      rw [hlogpow]
      calc
        (lf : ℝ) * Real.log 2 ≤ (lf : ℝ) * 1 := by
          exact mul_le_mul_of_nonneg_left hlog2_le_one (by positivity)
        _ = (lf : ℝ) := by ring
    exact hloglt.le.trans (by simpa [lf] using hlogpow_le)

private lemma exp_neg_numShifts_le_inv (q : ℕ → ℕ) (n : ℕ) (hq : q n ≠ 0) :
    Real.exp (-(numShifts q n : ℝ) / 8) ≤ ((100 * q n : ℕ) : ℝ)⁻¹ := by
  have hmposNat : 0 < 100 * q n := Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero hq)
  have hmpos : 0 < (((100 * q n : ℕ) : ℝ)) := by exact_mod_cast hmposNat
  have hdiv : (numShifts q n : ℝ) / 8 = (logFactor q n : ℝ) := by
    rw [numShifts]
    norm_num
  have hnegdiv : -(numShifts q n : ℝ) / 8 = -(logFactor q n : ℝ) := by
    linarith
  have hlogle : Real.log (((100 * q n : ℕ) : ℝ)) ≤ (logFactor q n : ℝ) := by
    simpa [logFactor] using real_log_nat_le_nat_log_two_succ (100 * q n)
  calc
    Real.exp (-(numShifts q n : ℝ) / 8)
        = Real.exp (-(logFactor q n : ℝ)) := by rw [hnegdiv]
    _ ≤ Real.exp (-Real.log (((100 * q n : ℕ) : ℝ))) := by
        exact Real.exp_le_exp_of_le (neg_le_neg hlogle)
    _ = (((100 * q n : ℕ) : ℝ))⁻¹ := by
        rw [Real.exp_neg, Real.exp_log hmpos]

lemma numShifts_eta_bound (q : ℕ → ℕ) (n : ℕ) :
    (q n : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-(numShifts q n : ℝ) / 8)) ≤ 1 / 100 := by
  by_cases hq : q n = 0
  · simp [hq]
  · have hqposNat : 0 < q n := Nat.pos_of_ne_zero hq
    have hmpos : 0 < (((100 * q n : ℕ) : ℝ)) := by
      exact_mod_cast Nat.mul_pos (by norm_num) hqposNat
    have hExp :=
      ENNReal.ofReal_le_ofReal (exp_neg_numShifts_le_inv q n hq)
    calc
      (q n : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-(numShifts q n : ℝ) / 8))
          ≤ (q n : ℝ≥0∞) * ENNReal.ofReal (((100 * q n : ℕ) : ℝ)⁻¹) := by
            exact mul_le_mul_right hExp _
      _ = 1 / 100 := by
          rw [ENNReal.ofReal_inv_of_pos hmpos]
          simp only [ENNReal.ofReal_natCast]
          have hcast :
              (((100 * q n : ℕ) : ℝ≥0∞)) = (100 : ℝ≥0∞) * (q n : ℝ≥0∞) := by
            norm_num
          rw [hcast]
          have hq0 : (q n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hqposNat.ne'
          have hqtop : (q n : ℝ≥0∞) ≠ ∞ := by simp
          have h1000 : (100 : ℝ≥0∞) ≠ 0 := by norm_num
          have h100top : (100 : ℝ≥0∞) ≠ ∞ := by simp
          rw [ENNReal.mul_inv (Or.inl h1000) (Or.inl h100top)]
          calc
            (q n : ℝ≥0∞) * ((100 : ℝ≥0∞)⁻¹ * (q n : ℝ≥0∞)⁻¹)
                = (100 : ℝ≥0∞)⁻¹ * ((q n : ℝ≥0∞) * (q n : ℝ≥0∞)⁻¹) := by
                  ac_rfl
            _ = (100 : ℝ≥0∞)⁻¹ * 1 := by
                  rw [ENNReal.mul_inv_cancel hq0 hqtop]
            _ = 1 / 100 := by simp [div_eq_mul_inv]

lemma verifier_accept_le_linear_add_of_query_correction {α : Type}
    (size : α → ℕ) (ℓ q : ℕ → ℕ)
    (V : LPCPVerifier α size (ZMod 2) ℓ) (x : α)
    (πhat : Fin (2 ^ ℓ (size x)) → ZMod 2)
    (π : Fin (ℓ (size x)) → ZMod 2) (η : ℝ≥0∞)
    {r : ℕ} (hQueryBound : QueryBound (V x) r (q (size x)))
    (hQuery : ∀ a : Fin (ℓ (size x)) → ZMod 2,
      Pr[fun shifts => correctedAnswer πhat shifts a ≠ π ⬝ᵥ a |
        simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
          (sampleShifts (ℓ (size x)) (numShifts q (size x)))] ≤ η) :
    Pr[= true |
      simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
        ((verifier size ℓ q V) x)] ≤
    Pr[= true |
      simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) (V x)] +
      (q (size x) : ℝ≥0∞) * η := by
  let n := ℓ (size x)
  let t := numShifts q (size x)
  let ctx := ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
  let blr := simulateQ (truthTableImpl n) (BLR.basicVerifier (F := ZMod 2) (n := n))
  let branch : OracleComp (PCP.fullSpec (ZMod 2) (2 ^ n)) Bool := do
    let shifts : Fin t → Fin n → ZMod 2 ← sampleShifts n t
    simulateQ (decodedImpl shifts) (V x)
  have hdrop :
      Pr[= true | simulateQ ctx (do
        let ok ← blr
        if ok then branch else pure false)] ≤
      Pr[= true | simulateQ ctx branch] := by
    simp only [simulateQ_bind, simulateQ_ite, simulateQ_pure]
    exact probOutput_bind_if_true_le_right _ _
  have hbranch :
      Pr[= true | simulateQ ctx branch] ≤
      Pr[= true |
        simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) (V x)] +
        (q (size x) : ℝ≥0∞) * η := by
    dsimp [branch, ctx]
    simp only [simulateQ_bind]
    simp_rw [simulateQ_decodedImpl_table_eq (πhat := πhat)]
    simpa [n, t] using
      corrected_run_accept_le_linear_add (n := n) (t := t) πhat π η hQueryBound
        (by simpa [n, t] using hQuery)
  simpa [verifier, n, t, ctx, blr, branch] using hdrop.trans hbranch

lemma verifier_soundness_near_case_of_single_query_bound {α : Type} (size : α → ℕ)
    (ε_s : ℝ≥0∞) (ℓ q : ℕ → ℕ)
    (V : LPCPVerifier α size (ZMod 2) ℓ) (x : α)
    (πhat : Fin (2 ^ ℓ (size x)) → ZMod 2)
    (π : Fin (ℓ (size x)) → ZMod 2)
    {r : ℕ} (hQueryBound : QueryBound (V x) r (q (size x)))
    (hSingle : ∀ a : Fin (ℓ (size x)) → ZMod 2,
      Pr[= true |
        (localCorrectionBad πhat π a) <$>
          simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
            (sampleVector (ZMod 2) (ℓ (size x)) (N := 2 ^ ℓ (size x)))] ≤
        (1 / 4 : ℝ≥0∞))
    (hEta :
      (q (size x) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(numShifts q (size x) : ℝ) / 8)) ≤ 1 / 100)
    (hSound :
      ∀ π : Fin (ℓ (size x)) → ZMod 2,
        Pr[= true |
          simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) (V x)]
          ≤ ε_s) :
    Pr[= true |
      simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
        ((verifier size ℓ q V) x)] ≤ ε_s + 1 / 100 := by
  let n := ℓ (size x)
  let t := numShifts q (size x)
  let η := ENNReal.ofReal (Real.exp (-(t : ℝ) / 8))
  have ht : 0 < t := by
    simpa [t] using numShifts_pos q (size x)
  have hQuery : ∀ a : Fin n → ZMod 2,
      Pr[fun shifts => correctedAnswer πhat shifts a ≠ π ⬝ᵥ a |
        simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
          (sampleShifts n t)] ≤ η := by
    intro a
    simpa [n, t, η] using
      correctedAnswer_failure_le_exp_of_single (n := n) (t := t) ht πhat π a
        (by simpa [n] using hSingle a)
  have hacc := verifier_accept_le_linear_add_of_query_correction
    size ℓ q V x πhat π η hQueryBound (by simpa [n, t, η] using hQuery)
  calc
    Pr[= true |
      simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
        ((verifier size ℓ q V) x)]
        ≤ Pr[= true |
            simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) (V x)] +
          (q (size x) : ℝ≥0∞) * η := hacc
    _ ≤ ε_s + 1 / 100 := by
      exact add_le_add (hSound π) (by simpa [t, η] using hEta)

lemma blrPrecheck_accept_le_seven_eighths_of_far {n : ℕ} [Nonempty (Fin n)]
    (πhat : Fin (2 ^ n) → ZMod 2)
    (hfar : (1 / 8 : ℝ≥0∞) ≤ distanceToLin (tableFunction πhat)) :
    Pr[= true |
      simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
        (simulateQ (truthTableImpl n) (BLR.basicVerifier (F := ZMod 2) (n := n)))] ≤
      7 / 8 := by
  let f : (Fin n → ZMod 2) → ZMod 2 := tableFunction πhat
  have hsound := BLR_basic_soundness_ZMod2 (n := n) f
  have hfalse : (1 / 8 : ℝ≥0∞) ≤
      Pr[= false |
        simulateQ ((randOracle (ZMod 2)).impl +
          fun x => (return f x : ProbComp (ZMod 2)))
          (BLR.basicVerifier (F := ZMod 2) (n := n))] := by
    exact hfar.trans (by simpa [f] using hsound)
  have hpre :
      simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
        (simulateQ (truthTableImpl n) (BLR.basicVerifier (F := ZMod 2) (n := n))) =
      simulateQ ((randOracle (ZMod 2)).impl +
        fun x => (return f x : ProbComp (ZMod 2)))
        (BLR.basicVerifier (F := ZMod 2) (n := n)) := by
    simpa [f] using
      (simulateQ_truthTableImpl_table_eq (n := n) πhat
        (BLR.basicVerifier (F := ZMod 2) (n := n)))
  rw [hpre, probOutput_true_eq_sub]
  simp
  exact one_le_seven_eighths_add_of_one_eighth_le hfalse

lemma verifier_soundness_far_case {α : Type} (size : α → ℕ)
    (ℓ q : ℕ → ℕ) (V : LPCPVerifier α size (ZMod 2) ℓ) (x : α)
    [Nonempty (Fin (ℓ (size x)))]
    (πhat : Fin (2 ^ ℓ (size x)) → ZMod 2)
    (hfar : (1 / 8 : ℝ≥0∞) ≤ distanceToLin (tableFunction πhat)) :
    Pr[= true |
      simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
        ((verifier size ℓ q V) x)] ≤ 7 / 8 := by
  exact (verifier_accept_le_blrPrecheck_accept size ℓ q V x πhat).trans
    (blrPrecheck_accept_le_seven_eighths_of_far (n := ℓ (size x)) πhat hfar)

lemma verifier_soundness_far_case_of_isFar {α : Type} (size : α → ℕ)
    (ℓ q : ℕ → ℕ) (V : LPCPVerifier α size (ZMod 2) ℓ) (x : α)
    (πhat : Fin (2 ^ ℓ (size x)) → ZMod 2)
    (hfar : IsFarFromLinear πhat) :
    Pr[= true |
      simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
        ((verifier size ℓ q V) x)] ≤ 7 / 8 := by
  rcases hfar with ⟨hne, hdist⟩
  letI : Nonempty (Fin (ℓ (size x))) := hne
  exact verifier_soundness_far_case size ℓ q V x πhat hdist

/--
Top-level soundness glue for the LPCP-to-PCP reduction.

`IsFar πhat` is the formal placeholder for the first case in the blueprint,
namely `δ(πhat, LIN) ≥ 1/8`.  The two hypotheses `hFar` and `hNear` are the
two probabilistic case analyses; this lemma packages them into the final
`max {7/8, ε_s + 1/100}` PCP soundness statement.
-/
lemma verifier_soundness_of_cases {α : Type} (size : α → ℕ) (ε_s : ℝ≥0∞)
    (ℓ q : ℕ → ℕ) {L : Set α} (V : LPCPVerifier α size (ZMod 2) ℓ) (x : α)
    (IsFar : (Fin (2 ^ ℓ (size x)) → ZMod 2) → Prop)
    (hFar : ∀ πhat : Fin (2 ^ ℓ (size x)) → ZMod 2,
      IsFar πhat →
        Pr[= true |
          simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
            ((verifier size ℓ q V) x)] ≤ 7 / 8)
    (hNear : ∀ πhat : Fin (2 ^ ℓ (size x)) → ZMod 2,
      ¬ IsFar πhat →
      x ∉ L →
      (∀ π : Fin (ℓ (size x)) → ZMod 2,
        Pr[= true |
          simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) (V x)]
          ≤ ε_s) →
        Pr[= true |
          simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
            ((verifier size ℓ q V) x)] ≤ ε_s + 1 / 100)
    (hx : x ∉ L)
    (hSound :
      ∀ π : Fin (ℓ (size x)) → ZMod 2,
        Pr[= true |
          simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) (V x)]
          ≤ ε_s) :
    ∀ πhat : Fin (2 ^ ℓ (size x)) → ZMod 2,
      Pr[= true |
        simulateQ ((randOracle (ZMod 2)).impl + (PCP.proofOracle πhat).impl)
          ((verifier size ℓ q V) x)] ≤ max (7 / 8) (ε_s + 1 / 100) := by
  intro πhat
  by_cases hπ : IsFar πhat
  · exact (hFar πhat hπ).trans (le_max_left _ _)
  · exact (hNear πhat hπ hx hSound).trans (le_max_right _ _)

/--
The constructed verifier has alphabet `ZMod 2` and proof length `2 ^ ℓ n` by its type, and
it satisfies the claimed query and randomness bounds.
-/
lemma verifier_has_claimed_parameters {α : Type} (size : α → ℕ) (ℓ q r : ℕ → ℕ)
    (V : LPCPVerifier α size (ZMod 2) ℓ)
    (hV : ∀ x, QueryBound (V x) (r (size x)) (q (size x))) :
    ∀ x,
      QueryBound
        (((verifier size ℓ q V :
          PCPVerifier α size (ZMod 2) (fun n => 2 ^ ℓ n)) x))
        (r (size x) + (2 + numShifts q (size x)) * ℓ (size x))
        (3 + 2 * numShifts q (size x) * q (size x)) := by
  intro x
  let n := ℓ (size x)
  let t := numShifts q (size x)
  let rx := r (size x)
  let qx := q (size x)
  have hBLR :
      QueryBound
        (simulateQ (truthTableImpl n)
          (BLR.basicVerifier (F := ZMod 2) (n := n)))
        (2 * n) 3 :=
    queryBound_simulateQ_truthTableImpl (BLR_basic_query_complexity (F := ZMod 2) (n := n))
  have hDecoded : ∀ shifts : Fin t → Fin n → ZMod 2,
      QueryBound (simulateQ (decodedImpl shifts) (V x)) rx (2 * t * qx) := by
    intro shifts
    exact queryBound_simulateQ_decodedImpl shifts (by simpa [n, rx, qx] using hV x)
  have hBranch : ∀ ok : Bool,
      QueryBound
        (if ok then
          (do
            let shifts : Fin t → Fin n → ZMod 2 ←
              sampleShifts n t
            simulateQ (decodedImpl shifts) (V x))
        else
          pure false)
        (t * n + rx) (2 * t * qx) := by
    intro ok
    cases ok
    · simp [QueryBound]
    · simpa [Nat.zero_add] using
        queryBound_bind (sampleShifts_queryBound n t) hDecoded
  have hAll :
      QueryBound
        (do
          let ok ← simulateQ (truthTableImpl n)
            (BLR.basicVerifier (F := ZMod 2) (n := n))
          if ok then
            (do
              let shifts : Fin t → Fin n → ZMod 2 ←
                sampleShifts n t
              simulateQ (decodedImpl shifts) (V x))
          else
            pure false)
        (2 * n + (t * n + rx)) (3 + 2 * t * qx) :=
    queryBound_bind hBLR hBranch
  have hrand : 2 * n + (t * n + rx) = rx + (2 + t) * n := by
    ring
  simpa [verifier, n, t, rx, qx, Nat.mul_assoc] using
    queryBound_mono hAll (by simp [t, qx, Nat.mul_assoc]) (by rw [hrand])

end LPCPToPCP

theorem LPCP_to_PCP_ZMod2 {α : Type} (size : α → ℕ)
    (ε_c ε_s : ℝ≥0∞) (ℓ q r : ℕ → ℕ) :
    LPCP size ε_c ε_s (ZMod 2) ℓ q r
    ⊆ PCP size ε_c (max (7 / 8) (ε_s + 1 / 100)) (ZMod 2)
      (fun n => 2 ^ ℓ n)
      (fun n => 3 + 2 * LPCPToPCP.numShifts q n * q n)
      (fun n => r n + (2 + LPCPToPCP.numShifts q n) * ℓ n) :=
by
  intro L hL
  rcases hL with ⟨V, time, hV⟩
  refine ⟨LPCPToPCP.verifier size ℓ q V, time, fun x => ?_⟩
  rcases hV x with ⟨hTime, hQuery, hComplete, hSound⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [RunsInTime]
  · exact LPCPToPCP.verifier_has_claimed_parameters size ℓ q r V
      (fun y => (hV y).2.1) x
  · intro hx
    exact LPCPToPCP.verifier_completeness size ε_c ℓ q r V x hQuery (hComplete hx)
  · intro hx
    refine LPCPToPCP.verifier_soundness_of_cases size ε_s ℓ q (L := L) V x
      LPCPToPCP.IsFarFromLinear ?_ ?_ hx (hSound hx)
    · intro πhat hfar
      exact LPCPToPCP.verifier_soundness_far_case_of_isFar size ℓ q V x πhat hfar
    · intro πhat hnear _hx hSoundx
      have hEta := LPCPToPCP.numShifts_eta_bound q (size x)
      by_cases hn : ℓ (size x) = 0
      · have hSingleExists :=
          LPCPToPCP.localCorrectionBad_single_le_quarter_of_length_zero
            (n := ℓ (size x)) hn πhat
        rcases hSingleExists with ⟨π, hSingle⟩
        exact LPCPToPCP.verifier_soundness_near_case_of_single_query_bound
          size ε_s ℓ q V x πhat π hQuery hSingle hEta hSoundx
      · haveI : Nonempty (Fin (ℓ (size x))) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
        rcases LPCPToPCP.localCorrectionBad_single_le_quarter_of_not_far
          (n := ℓ (size x)) πhat hnear with ⟨π, hSingle⟩
        exact LPCPToPCP.verifier_soundness_near_case_of_single_query_bound
          size ε_s ℓ q V x πhat π hQuery hSingle hEta hSoundx
