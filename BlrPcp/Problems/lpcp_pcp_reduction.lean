import Architect
import BlrPcp.Oracle
import BlrPcp.Problems.BLR
import CompPoly.Multivariate.CMvPolynomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
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
noncomputable def truthTableIndex (n : ℕ) : (Fin n → ZMod 2) → Fin (2 ^ n) :=
  fun v => Fin.cast (by simp [ZMod.card]) ((Fintype.equivFin (Fin n → ZMod 2)) v)

/-- `⌈log (100q)⌉`, where `log` is the natural logarithm. -/
noncomputable def logFactor (q : ℕ → ℕ) (n : ℕ) : ℕ :=
  ⌈Real.log (100 * q n)⌉₊

/-- Number of random shifts used to decode a linear query by plurality. -/
noncomputable def numShifts (q : ℕ → ℕ) (n : ℕ) : ℕ :=
  8 * logFactor q n

/-- Plurality over `ZMod 2`, with ties broken toward `0`. -/
def pluralityZMod2 {t : ℕ} (ys : Fin t → ZMod 2) : ZMod 2 :=
  if Fintype.card { i : Fin t // ys i = 1 } * 2 > t then 1 else 0

def sampleField {F : Type} {N : ℕ} : OracleComp (PCP.fullSpec F N) F :=
  query (spec := PCP.fullSpec F N) (.inl ())

def sampleVector (F : Type) (m : ℕ) {N : ℕ} :
    OracleComp (PCP.fullSpec F N) (Fin m → F) :=
  Fin.mOfFn m fun _ => sampleField (F := F) (N := N)

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

/-- Run an LPCP-style vector query against a PCP truth table. -/
noncomputable def truthTableImpl (n : ℕ) :
    QueryImpl (LPCP.fullSpec (ZMod 2) n) (OracleComp (PCP.fullSpec (ZMod 2) (2 ^ n)))
  | .inl () => query (spec := PCP.fullSpec (ZMod 2) (2 ^ n)) (.inl ())
  | .inr a => query (spec := PCP.fullSpec (ZMod 2) (2 ^ n)) (.inr (truthTableIndex n a))

/-- Answer one LPCP linear query using the sampled shifts and plurality decoding. -/
noncomputable def decodedLinearQuery {n t : ℕ}
    (shifts : Fin t → Fin n → ZMod 2) (a : Fin n → ZMod 2) :
    OracleComp (PCP.fullSpec (ZMod 2) (2 ^ n)) (ZMod 2) := do
  let ys : Fin t → ZMod 2 ← Fin.mOfFn t fun i => do
    let y₁ : ZMod 2 ← query (spec := PCP.fullSpec (ZMod 2) (2 ^ n))
      (.inr (truthTableIndex n fun j => a j + shifts i j))
    let y₀ : ZMod 2 ← query (spec := PCP.fullSpec (ZMod 2) (2 ^ n))
      (.inr (truthTableIndex n (shifts i)))
    pure (y₁ - y₀)
  pure (pluralityZMod2 ys)

/-- Simulate LPCP oracle queries using a PCP truth table and fixed random shifts. -/
noncomputable def decodedImpl {n t : ℕ}
    (shifts : Fin t → Fin n → ZMod 2) :
    QueryImpl (LPCP.fullSpec (ZMod 2) n) (OracleComp (PCP.fullSpec (ZMod 2) (2 ^ n)))
  | .inl () => query (spec := PCP.fullSpec (ZMod 2) (2 ^ n)) (.inl ())
  | .inr a => decodedLinearQuery shifts a

/-- The PCP verifier obtained from an LPCP verifier over `ZMod 2`. -/
noncomputable def verifier {α : Type} (size : α → ℕ) (ℓ q : ℕ → ℕ)
    (V : LPCPVerifier α size (ZMod 2) ℓ) :
    PCPVerifier α size (ZMod 2) (fun n => 2 ^ (ℓ n)) :=
  fun x => do
    let ok ← simulateQ (truthTableImpl (ℓ (size x)))
      (BLR.basicVerifier (F := ZMod 2) (n := ℓ (size x)))
    if ok then
      let shifts : Fin (numShifts q (size x)) → Fin (ℓ (size x)) → ZMod 2 ←
        Fin.mOfFn (numShifts q (size x)) fun _ =>
          sampleVector (ZMod 2) (ℓ (size x))
      simulateQ (decodedImpl shifts) (V x)
    else
      pure false

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
  · sorry
  · sorry
  · sorry
