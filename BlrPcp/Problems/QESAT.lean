import Architect
import BlrPcp.Oracle
import BlrPcp.Problems.TensorEq
import CompPoly.Data.Nat.Bitwise
import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Multivariate.MvPolyEquiv.Eval
import VCVio.OracleComp.Constructions.Replicate

/-!
# Quadratic equation satisfiability

This file defines the QESAT language and the exponential-length PCP for it.

Unless stated otherwise, all definitions and lemmas are for F = Z/2.

## Main declarations

- `QESAT`: the language of quadratic equation satisfiability instances.
- `QESAT.size`: the binary-size proxy for QESAT instances.
- `QESAT_poly_LPCP`: QESAT over `ZMod 2` has an exponential-length LPCP.
- `LPCP_to_PCP_ZMod2`: the conversion lemma from LPCP to PCP for `ZMod 2`.
- `QESAT_exp_PCP`: QESAT over `ZMod 2` has an exponential-length PCP.
-/

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
    [SampleableType F]

open CPoly CMvPolynomial
open OracleComp
open scoped ENNReal
open scoped Matrix

abbrev QESAT (F : Type) [Field F] (n : ℕ) : Set (List (CMvPolynomial n F)) :=
  fun polys => (∀ p ∈ polys, p.totalDegree ≤ 2) ∧
    ∃ (a : Fin n → F), ∀ p ∈ polys, CMvPolynomial.eval a p = 0

example : QESAT (ZMod 2) 3 [X 0 + C 1, X 0 * X 1 + X 2] := by native_decide

namespace QESAT

/-- The size of a QESAT instance if it was a binary string
TODO: the proper way would be to use this:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/Encoding.html -/
def size {n : ℕ} (polys : List (CMvPolynomial n F)) :
    ℕ :=  polys.length * (n + 1)^2

private abbrev mvPoly {n : ℕ} (p : CMvPolynomial n (ZMod 2)) :
    MvPolynomial (Fin n) (ZMod 2) :=
  fromCMvPolynomial p

private abbrev mvCoeff {n : ℕ} (p : CMvPolynomial n (ZMod 2)) (m : Fin n →₀ ℕ) :
    ZMod 2 :=
  MvPolynomial.coeff m (mvPoly p)

private def cmvCoeff {n : ℕ} (p : CMvPolynomial n (ZMod 2)) (m : Fin n →₀ ℕ) :
    ZMod 2 :=
  CMvPolynomial.coeff (CMvMonomial.ofFinsupp m) p

private def singleMonomial {n : ℕ} (i : Fin n) (e : ℕ) : CMvMonomial n :=
  Vector.ofFn fun j => if j = i then e else 0

private def pairMonomial {n : ℕ} (i j : Fin n) : CMvMonomial n :=
  Vector.ofFn fun k => (if k = i then 1 else 0) + if k = j then 1 else 0

@[simp]
private lemma singleMonomial_eq_ofFinsupp_single {n : ℕ} (i : Fin n) (e : ℕ) :
    singleMonomial i e = CMvMonomial.ofFinsupp (Finsupp.single i e) := by
  apply Vector.ext
  intro k hk
  unfold singleMonomial CMvMonomial.ofFinsupp
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  let l : Fin n := ⟨k, hk⟩
  change (if l = i then e else 0) = (Finsupp.single i e) l
  by_cases h : l = i
  · rw [if_pos h, h, Finsupp.single_eq_same]
  · rw [if_neg h, Finsupp.single_eq_of_ne h]

@[simp]
private lemma pairMonomial_eq_ofFinsupp_pair {n : ℕ} (i j : Fin n) :
    pairMonomial i j =
      CMvMonomial.ofFinsupp (Finsupp.single i 1 + Finsupp.single j 1) := by
  apply Vector.ext
  intro k hk
  unfold pairMonomial CMvMonomial.ofFinsupp
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  let l : Fin n := ⟨k, hk⟩
  change ((if l = i then 1 else 0) + if l = j then 1 else 0) =
    (Finsupp.single i 1) l + (Finsupp.single j 1) l
  by_cases hi : l = i
  · by_cases hj : l = j
    · have hij : i = j := hi.symm.trans hj
      subst j
      simp [hi]
    · have hij : i ≠ j := fun h => hj (hi.trans h)
      rw [if_pos hi, if_neg hj, hi, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne hij]
  · by_cases hj : l = j
    · have hji : j ≠ i := fun h => hi (hj.trans h)
      rw [if_neg hi, if_pos hj, hj, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne hji]
    · rw [if_neg hi, if_neg hj, Finsupp.single_eq_of_ne hi,
        Finsupp.single_eq_of_ne hj]

@[simp]
private lemma ofFinsupp_eq_iff {n : ℕ} {m₁ m₂ : Fin n →₀ ℕ} :
    CMvMonomial.ofFinsupp m₁ = CMvMonomial.ofFinsupp m₂ ↔ m₁ = m₂ := by
  constructor
  · exact fun h => CMvMonomial.injective_ofFinsupp h
  · intro h
    rw [h]

private def monomialQuery {n : ℕ} (m : CMvMonomial n) :
    Fin (n + n * n) → ZMod 2 :=
  Fin.append (Function.const _ 0) fun k =>
    let ij := finProdFinEquiv.symm k
    if m = singleMonomial ij.1 1 then
      if ij.1 = ij.2 then 1 else 0
    else if m = singleMonomial ij.1 2 then
      if ij.1 = ij.2 then 1 else 0
    else if m = pairMonomial ij.1 ij.2 then
      if ij.1.val < ij.2.val then 1 else 0
    else
      0

private def linearCoeff {n : ℕ} (p : CMvPolynomial n (ZMod 2)) :
    Fin (n + n * n) → ZMod 2 :=
  fun k => ∑ m ∈ p.support.erase 0,
    cmvCoeff p m * monomialQuery (CMvMonomial.ofFinsupp m) k

private def constantCoeff {n : ℕ} (p : CMvPolynomial n (ZMod 2)) : ZMod 2 :=
  cmvCoeff p 0

private def linearMatrix {n : ℕ} (polys : List (CMvPolynomial n (ZMod 2))) :
    Matrix (Fin polys.length) (Fin (n + n * n)) (ZMod 2) :=
  fun i => linearCoeff (polys.get i)

private def linearTarget {n : ℕ} (polys : List (CMvPolynomial n (ZMod 2))) :
    Fin polys.length → ZMod 2 :=
  fun i => -constantCoeff (polys.get i)

private def tensorSelfVerifier {n : ℕ} :
    OracleComp (LPCP.spec (ZMod 2) (n + n * n)) Bool := do
  let s ← LINEQ.sampleRandomVector n (n + n * n) (ZMod 2)
  let t ← LINEQ.sampleRandomVector n (n + n * n) (ZMod 2)
  let yA : ZMod 2 ← query (spec := LPCP.spec (ZMod 2) (n + n * n)) (.inr (TENSORQ.queryA s))
  let yA' : ZMod 2 ← query (spec := LPCP.spec (ZMod 2) (n + n * n)) (.inr (TENSORQ.queryA t))
  let yB : ZMod 2 ← query (spec := LPCP.spec (ZMod 2) (n + n * n)) (.inr (TENSORQ.queryB s t))
  pure (yB = yA * yA')

private def polyVerifier {n : ℕ} :
    LPCPVerifier (List (CMvPolynomial n (ZMod 2))) size (ZMod 2) (fun _ => n + n * n) :=
  fun polys =>
    if ∀ p ∈ polys, p.totalDegree ≤ 2 then do
      let hLine ← LINEQ.verifier (F := ZMod 2)
        (linearMatrix polys, linearTarget polys)
      let hTensor ← tensorSelfVerifier (n := n)
      pure (hLine && hTensor)
    else
      pure false

private lemma zmod2_mul_self (x : ZMod 2) : x * x = x := by
  fin_cases x <;> norm_num

private lemma finsupp_single_one_ne_single_two {n : ℕ} (i j : Fin n) :
    Finsupp.single i 1 ≠ Finsupp.single j 2 := by
  intro h
  have := congrArg (fun m : Fin n →₀ ℕ => m.sum fun _ e => e) h
  norm_num at this

private lemma finsupp_single_two_ne_single_one {n : ℕ} (i j : Fin n) :
    Finsupp.single i 2 ≠ Finsupp.single j 1 :=
  fun h => finsupp_single_one_ne_single_two j i h.symm

private lemma finsupp_single_one_ne_pair {n : ℕ} (i j k : Fin n) :
    Finsupp.single i 1 ≠ Finsupp.single j 1 + Finsupp.single k 1 := by
  intro h
  have := congrArg (fun m : Fin n →₀ ℕ => m.sum fun _ e => e) h
  have hpair :
      (Finsupp.single j 1 + Finsupp.single k 1).sum (fun _ e => e) = 2 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp
  simp [hpair] at this

private lemma finsupp_single_two_ne_pair_of_left_ne {n : ℕ} {i j k : Fin n}
    (hji : j ≠ i) :
    Finsupp.single i 2 ≠ Finsupp.single j 1 + Finsupp.single k 1 := by
  intro h
  have hj := congrFun (congrArg DFunLike.coe h) j
  by_cases hkj : k = j
  · subst k
    simp [hji] at hj
  · simp [hji, hkj] at hj

private lemma finsupp_pair_ne_single_two_of_ne {n : ℕ} {i j k : Fin n}
    (hij : i ≠ j) :
    Finsupp.single i 1 + Finsupp.single j 1 ≠ Finsupp.single k 2 := by
  intro h
  have hi := congrFun (congrArg DFunLike.coe h) i
  by_cases hki : k = i
  · subst k
    simp [hij] at hi
  · simp [hki, hij] at hi

private lemma finsupp_pair_eq_pair_of_lt {n : ℕ} {i j u v : Fin n}
    (hij : i.val < j.val) (huv : u.val < v.val)
    (h : Finsupp.single i 1 + Finsupp.single j 1 =
        Finsupp.single u 1 + Finsupp.single v 1) :
    i = u ∧ j = v := by
  have hi := congrFun (congrArg DFunLike.coe h) i
  have hj := congrFun (congrArg DFunLike.coe h) j
  have hijne : i ≠ j := Fin.ne_of_val_ne (ne_of_lt hij)
  by_cases hiu : i = u
  · subst u
    have hjv : j = v := by
      by_contra hjv
      have hji : j ≠ i := hijne.symm
      simp [hji, hjv] at hj
    exact ⟨rfl, hjv⟩
  · have hiv : i = v := by
      by_contra hiv
      simp [hiu, hiv, hijne] at hi
    subst v
    have hju : j = u := by
      by_contra hju
      have hji : j ≠ i := hijne.symm
      simp [hji, hju] at hj
    subst u
    omega

private lemma finsupp_sum_le_two_cases {n : ℕ} (m : Fin n →₀ ℕ)
    (hm : m.sum (fun _ e => e) ≤ 2) :
    m = 0 ∨
      (∃ i, m = Finsupp.single i 1) ∨
      (∃ i, m = Finsupp.single i 2) ∨
      (∃ i j, i.val < j.val ∧ m = Finsupp.single i 1 + Finsupp.single j 1) := by
  classical
  have hcard : Multiset.card (Finsupp.toMultiset m) ≤ 2 := by
    simpa [Finsupp.card_toMultiset] using hm
  interval_cases h : Multiset.card (Finsupp.toMultiset m)
  · left
    have hms : Finsupp.toMultiset m = 0 := Multiset.card_eq_zero.mp h
    simpa using (Finsupp.toMultiset_eq_iff.mp hms)
  · right; left
    rcases Multiset.card_eq_one.mp h with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simpa using (Finsupp.toMultiset_eq_iff.mp hi)
  · rcases Multiset.card_eq_two.mp h with ⟨i, j, hij⟩
    have hmij : m = Finsupp.single i 1 + Finsupp.single j 1 := by
      have hto :
          Multiset.toFinsupp ({i, j} : Multiset (Fin n)) =
            Finsupp.single i 1 + Finsupp.single j 1 := by
        ext k
        by_cases hki : k = i
        · subst k
          by_cases hij' : i = j <;> simp [hij']
        · by_cases hkj : k = j
          · subst k
            simp [hki]
          · simp [hki, hkj]
      exact (Finsupp.toMultiset_eq_iff.mp hij).trans hto
    by_cases hEq : i = j
    · right; right; left
      refine ⟨i, ?_⟩
      subst hEq
      rw [hmij]
      ext k
      by_cases hk : k = i <;> simp [Finsupp.single_eq_same, Finsupp.single_eq_of_ne, hk]
    · right; right; right
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hEq) with hijlt | hjilt
      · exact ⟨i, j, hijlt, hmij⟩
      · refine ⟨j, i, hjilt, ?_⟩
        rw [hmij, add_comm]

private lemma dotProduct_monomialQuery_single_one {n : ℕ} (a : Fin n → ZMod 2)
    (i : Fin n) :
    TENSORQ.honestProof (a, fun p : Fin n × Fin n => a p.1 * a p.2) ⬝ᵥ
        monomialQuery (CMvMonomial.ofFinsupp (Finsupp.single i 1)) =
      a i := by
  simp only [dotProduct, monomialQuery, TENSORQ.honestProof]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Function.const_apply, mul_zero, Finset.sum_const_zero,
    Fin.append_right, zero_add]
  rw [← finProdFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.sum_eq_single (i, i)]
  · simp [zmod2_mul_self]
  · rintro ⟨j, k⟩ _ hne
    by_cases hji : j = i
    · subst j
      by_cases hki : k = i
      · subst k
        exact (hne rfl).elim
      · have hik : i ≠ k := fun h => hki h.symm
        simp [hik]
    · have hsing : Finsupp.single i 1 ≠ Finsupp.single j 1 := by
        intro h
        rcases (Finsupp.single_eq_single_iff i j 1 1).mp h with hij | hzero
        · exact hji hij.1.symm
        · norm_num at hzero
      simp [hsing, finsupp_single_one_ne_single_two, finsupp_single_one_ne_pair]
  · intro hmem
    simp at hmem

private lemma dotProduct_monomialQuery_single_two {n : ℕ} (a : Fin n → ZMod 2)
    (i : Fin n) :
    TENSORQ.honestProof (a, fun p : Fin n × Fin n => a p.1 * a p.2) ⬝ᵥ
        monomialQuery (CMvMonomial.ofFinsupp (Finsupp.single i 2)) =
      a i := by
  simp only [dotProduct, monomialQuery, TENSORQ.honestProof]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Function.const_apply, mul_zero, Finset.sum_const_zero,
    Fin.append_right, zero_add]
  rw [← finProdFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.sum_eq_single (i, i)]
  · simp [zmod2_mul_self, finsupp_single_two_ne_single_one]
  · rintro ⟨j, k⟩ _ hne
    by_cases hji : j = i
    · subst j
      by_cases hki : k = i
      · subst k
        exact (hne rfl).elim
      · have hik : i ≠ k := fun h => hki h.symm
        simp [hik, finsupp_single_two_ne_single_one]
    · have hsing : Finsupp.single i 2 ≠ Finsupp.single j 2 := by
        intro h
        rcases (Finsupp.single_eq_single_iff i j 2 2).mp h with hij | hzero
        · exact hji hij.1.symm
        · norm_num at hzero
      have hpair := finsupp_single_two_ne_pair_of_left_ne (i := i) (j := j) (k := k) hji
      simp [hsing, hpair, finsupp_single_two_ne_single_one]
  · intro hmem
    simp at hmem

private lemma dotProduct_monomialQuery_pair {n : ℕ} (a : Fin n → ZMod 2)
    {i j : Fin n} (hij : i.val < j.val) :
    TENSORQ.honestProof (a, fun p : Fin n × Fin n => a p.1 * a p.2) ⬝ᵥ
        monomialQuery (CMvMonomial.ofFinsupp
          (Finsupp.single i 1 + Finsupp.single j 1)) =
      a i * a j := by
  simp only [dotProduct, monomialQuery, TENSORQ.honestProof]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Function.const_apply, mul_zero, Finset.sum_const_zero,
    Fin.append_right, zero_add]
  rw [← finProdFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.sum_eq_single (i, j)]
  · have hijne : i ≠ j := Fin.ne_of_val_ne (ne_of_lt hij)
    simp [hij,
      finsupp_pair_ne_single_two_of_ne (i := i) (j := j) (k := i) hijne]
  · rintro ⟨u, v⟩ _ hne
    have hpair_ne_one : Finsupp.single i 1 + Finsupp.single j 1 ≠ Finsupp.single u 1 :=
      fun h => finsupp_single_one_ne_pair u i j h.symm
    have hijne : i ≠ j := Fin.ne_of_val_ne (ne_of_lt hij)
    have hpair_ne_two : Finsupp.single i 1 + Finsupp.single j 1 ≠ Finsupp.single u 2 :=
      finsupp_pair_ne_single_two_of_ne (i := i) (j := j) (k := u) hijne
    by_cases huv : u.val < v.val
    · by_cases hp : Finsupp.single i 1 + Finsupp.single j 1 =
          Finsupp.single u 1 + Finsupp.single v 1
      · have hcoords := finsupp_pair_eq_pair_of_lt hij huv hp
        exact (hne (by ext <;> simp [hcoords.1, hcoords.2])).elim
      · simp [hpair_ne_one, hpair_ne_two, hp]
    · simp [hpair_ne_one, hpair_ne_two, huv]
  · intro hmem
    simp at hmem

private lemma monomialQuery_eval {n : ℕ} (a : Fin n → ZMod 2) {m : Fin n →₀ ℕ}
    (hm0 : m ≠ 0) (hmdeg : m.sum (fun _ e => e) ≤ 2) :
    (∏ i ∈ m.support, a i ^ m i) =
      TENSORQ.honestProof (a, fun p : Fin n × Fin n => a p.1 * a p.2) ⬝ᵥ
        monomialQuery (CMvMonomial.ofFinsupp m) := by
  classical
  rcases finsupp_sum_le_two_cases m hmdeg with hzero | hlin | hsquare | hpair
  · exact (hm0 hzero).elim
  · rcases hlin with ⟨i, rfl⟩
    rw [dotProduct_monomialQuery_single_one]
    rw [Finsupp.support_single_ne_zero i (by norm_num : (1 : ℕ) ≠ 0)]
    simp
  · rcases hsquare with ⟨i, rfl⟩
    rw [dotProduct_monomialQuery_single_two]
    rw [Finsupp.support_single_ne_zero i (by norm_num : (2 : ℕ) ≠ 0)]
    simp
  · rcases hpair with ⟨i, j, hij, rfl⟩
    rw [dotProduct_monomialQuery_pair (hij := hij)]
    have hijne : i ≠ j := Fin.ne_of_val_ne (ne_of_lt hij)
    have hsupp :
        (Finsupp.single i 1 + Finsupp.single j 1).support = {i, j} := by
      ext x
      by_cases hxi : x = i <;> by_cases hxj : x = j <;>
        simp [Finsupp.mem_support_iff, hxi, hxj, hijne, hijne.symm]
    rw [hsupp]
    simp [hijne, hijne.symm]

private lemma dotProduct_linearCoeff_eq_sum {n : ℕ} (p : CMvPolynomial n (ZMod 2))
    (π : Fin (n + n * n) → ZMod 2) :
    π ⬝ᵥ linearCoeff p =
      ∑ m ∈ (mvPoly p).support.erase 0,
        mvCoeff p m * (π ⬝ᵥ monomialQuery (CMvMonomial.ofFinsupp m)) := by
  simp only [dotProduct, linearCoeff]
  calc
    ∑ k, π k * (∑ m ∈ (mvPoly p).support.erase 0,
          mvCoeff p m * monomialQuery (CMvMonomial.ofFinsupp m) k)
        = ∑ k, ∑ m ∈ (mvPoly p).support.erase 0,
            π k * (mvCoeff p m * monomialQuery (CMvMonomial.ofFinsupp m) k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp [Finset.mul_sum]
    _ = ∑ m ∈ (mvPoly p).support.erase 0, ∑ k,
            π k * (mvCoeff p m * monomialQuery (CMvMonomial.ofFinsupp m) k) := by
          rw [Finset.sum_comm]
    _ = ∑ m ∈ (mvPoly p).support.erase 0, mvCoeff p m * ∑ k,
            π k * monomialQuery (CMvMonomial.ofFinsupp m) k := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun _ _ => ?_
          ring

private lemma linearCoeff_eval {n : ℕ} (p : CMvPolynomial n (ZMod 2))
    (hpdeg : p.totalDegree ≤ 2) (a : Fin n → ZMod 2) :
    TENSORQ.honestProof (a, fun q : Fin n × Fin n => a q.1 * a q.2) ⬝ᵥ
        linearCoeff p + constantCoeff p =
      CMvPolynomial.eval a p := by
  classical
  rw [eval_equiv, MvPolynomial.eval_eq]
  rw [dotProduct_linearCoeff_eq_sum]
  let P := mvPoly p
  have hdeg : P.totalDegree ≤ 2 := by
    simpa [P, mvPoly, totalDegree_equiv] using hpdeg
  have hterm : ∀ m ∈ P.support, m ≠ 0 →
      (∏ i ∈ m.support, a i ^ m i) =
        TENSORQ.honestProof (a, fun q : Fin n × Fin n => a q.1 * a q.2) ⬝ᵥ
          monomialQuery (CMvMonomial.ofFinsupp m) := by
    intro m hm hm0
    exact monomialQuery_eval a hm0 ((MvPolynomial.le_totalDegree hm).trans hdeg)
  by_cases h0 : (0 : Fin n →₀ ℕ) ∈ P.support
  · rw [← Finset.add_sum_erase P.support
        (fun m => P.coeff m * ∏ i ∈ m.support, a i ^ m i) h0]
    simp only [constantCoeff, mvCoeff, P]
    rw [add_comm]
    simp only [Finsupp.support_zero, Finset.prod_empty, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : m ≠ 0 := by
      intro hz
      exact Finset.notMem_erase _ _ (hz ▸ hm)
    rw [hterm m (Finset.mem_of_mem_erase hm) hm0]
  · have hcoeff0 : P.coeff 0 = 0 := by
      simpa [MvPolynomial.notMem_support_iff] using h0
    rw [Finset.erase_eq_of_notMem h0]
    have hconst : constantCoeff p = 0 := by
      simpa [constantCoeff, cmvCoeff, mvCoeff, P] using hcoeff0
    rw [hconst, add_zero]
    simp only [mvCoeff, P]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : m ≠ 0 := by
      intro hz
      exact h0 (hz ▸ hm)
    rw [← hterm m hm hm0]

private lemma tensorSelfVerifier_queryBound {n : ℕ} :
    QueryBound (tensorSelfVerifier (n := n)) 3 (2 * n) := by
  have hQuery : ∀ s t : Fin n → ZMod 2,
      QueryBound
        (do
          let yA : ZMod 2 ←
            (liftM (query (spec := LPCP.spec (ZMod 2) (n + n * n))
              (.inr (TENSORQ.queryA s))) :
              OracleComp (LPCP.spec (ZMod 2) (n + n * n)) (ZMod 2))
          let yA' : ZMod 2 ←
            (liftM (query (spec := LPCP.spec (ZMod 2) (n + n * n))
              (.inr (TENSORQ.queryA t))) :
              OracleComp (LPCP.spec (ZMod 2) (n + n * n)) (ZMod 2))
          let yB : ZMod 2 ←
            (liftM (query (spec := LPCP.spec (ZMod 2) (n + n * n))
              (.inr (TENSORQ.queryB s t))) :
              OracleComp (LPCP.spec (ZMod 2) (n + n * n)) (ZMod 2))
          pure (decide (yB = yA * yA'))) 3 0 := by
    intro s t
    simp only [QueryBound]
    rw [OracleComp.isQueryBound_query_bind_iff]
    refine ⟨by simp, fun _ => ?_⟩
    rw [OracleComp.isQueryBound_query_bind_iff]
    refine ⟨by simp, fun _ => ?_⟩
    rw [OracleComp.isQueryBound_query_bind_iff]
    exact ⟨by simp, fun _ => trivial⟩
  simpa [tensorSelfVerifier, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    queryBound_bind (LINEQ.sampleRandomVector_queryBound (F := ZMod 2) n (n + n * n)) fun s =>
      queryBound_bind (LINEQ.sampleRandomVector_queryBound (F := ZMod 2) n (n + n * n)) fun t =>
        hQuery s t

private lemma length_le_size {n : ℕ} (polys : List (CMvPolynomial n (ZMod 2))) :
    polys.length ≤ QESAT.size polys := by
  unfold QESAT.size
  exact Nat.le_mul_of_pos_right _ (by positivity : 0 < (n + 1) ^ 2)

private lemma polyVerifier_queryBound {n : ℕ} (polys : List (CMvPolynomial n (ZMod 2))) :
    QueryBound (polyVerifier polys) 4 (QESAT.size polys + 2 * n) := by
  by_cases hdeg : ∀ p ∈ polys, p.totalDegree ≤ 2
  · have hqb :
        QueryBound
          (do
            let hLine ← LINEQ.verifier (F := ZMod 2)
              (linearMatrix polys, linearTarget polys)
            let hTensor ← tensorSelfVerifier (n := n)
            pure (hLine && hTensor)) 4 (polys.length + 2 * n) := by
      simpa [Nat.add_assoc] using
        queryBound_bind
          (LINEQ.verifier_queryBound (F := ZMod 2)
            (linearMatrix polys, linearTarget polys))
          (fun hLine =>
            queryBound_bind (tensorSelfVerifier_queryBound (n := n)) fun hTensor => by
              show QueryBound
                (pure (hLine && hTensor) :
                  OracleComp (LPCP.spec (ZMod 2) (n + n * n)) Bool) 0 0
              simp [QueryBound])
    dsimp [polyVerifier]
    rw [if_pos hdeg]
    exact queryBound_mono hqb (by rfl) (Nat.add_le_add_right (length_le_size polys) (2 * n))
  · dsimp [polyVerifier]
    rw [if_neg hdeg]
    simp [QueryBound]

private lemma linearMatrix_mul_honestProof {n : ℕ}
    {polys : List (CMvPolynomial n (ZMod 2))}
    (hdeg : ∀ p ∈ polys, p.totalDegree ≤ 2) {a : Fin n → ZMod 2}
    (ha : ∀ p ∈ polys, CMvPolynomial.eval a p = 0) :
    (linearMatrix polys) *ᵥ (TENSORQ.honestProof (a, fun q : Fin n × Fin n => a q.1 * a q.2)) =
      linearTarget polys := by
  funext i
  have hEval := linearCoeff_eval (polys.get i)
    (hdeg (polys.get i) (List.get_mem polys i)) a
  rw [ha (polys.get i) (List.get_mem polys i)] at hEval
  have hdot :
      TENSORQ.honestProof (a, fun q : Fin n × Fin n => a q.1 * a q.2) ⬝ᵥ
          linearCoeff (polys.get i) =
        -constantCoeff (polys.get i) := by
    linear_combination hEval
  simpa [linearMatrix, linearTarget, Matrix.mulVec, dotProduct, mul_comm] using hdot

private lemma tensor_honestProof_proj {n : ℕ}
    (π : Fin (n + n * n) → ZMod 2) :
    TENSORQ.honestProof (TENSORQ.projA π, TENSORQ.projB π) = π := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp [TENSORQ.honestProof, TENSORQ.projA]
  · simp only [TENSORQ.honestProof, TENSORQ.projB, Fin.append_right]
    rw [Equiv.apply_symm_apply]

private lemma mem_of_tensor_linear {n : ℕ} {polys : List (CMvPolynomial n (ZMod 2))}
    {π : Fin (n + n * n) → ZMod 2}
    (hdeg : ∀ p ∈ polys, p.totalDegree ≤ 2)
    (htensor : (TENSORQ.projA π, TENSORQ.projB π) ∈ TENSORQ (ZMod 2) n)
    (hline : (linearMatrix polys) *ᵥ π = linearTarget polys) :
    polys ∈ QESAT (ZMod 2) n := by
  refine ⟨hdeg, TENSORQ.projA π, ?_⟩
  rw [List.forall_mem_iff_get]
  intro i
  have hπ :
      TENSORQ.honestProof
          (TENSORQ.projA π, fun q : Fin n × Fin n => TENSORQ.projA π q.1 * TENSORQ.projA π q.2) =
        π := by
    have hb :
        TENSORQ.projB π =
          fun q : Fin n × Fin n => TENSORQ.projA π q.1 * TENSORQ.projA π q.2 := htensor
    simpa [hb] using tensor_honestProof_proj π
  have hEval := linearCoeff_eval (polys.get i)
    (hdeg (polys.get i) (List.get_mem polys i)) (TENSORQ.projA π)
  rw [hπ] at hEval
  have hdot :
      π ⬝ᵥ linearCoeff (polys.get i) = -constantCoeff (polys.get i) := by
    simpa [linearMatrix, linearTarget, Matrix.mulVec, dotProduct, mul_comm] using congrFun hline i
  rw [hdot] at hEval
  rw [← hEval]
  exact neg_add_cancel (constantCoeff (polys.get i))

private lemma lineSubcheck_soundness {n : ℕ} (polys : List (CMvPolynomial n (ZMod 2)))
    (π : Fin (n + n * n) → ZMod 2)
    (hd : (linearMatrix polys) *ᵥ π - linearTarget polys ≠ 0) :
    Pr[= true | simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl)
      (LINEQ.verifier (F := ZMod 2) (linearMatrix polys, linearTarget polys))] ≤
        1 / (Fintype.card (ZMod 2) : ENNReal) := by
  simp [LINEQ.verifier]
  rw [← probEvent_eq_eq_probOutput]
  rw [probEvent_map]
  let accept : (Fin polys.length → ZMod 2) → Prop := fun r =>
    decide (π ⬝ᵥ (linearMatrix polys)ᵀ *ᵥ r = linearTarget polys ⬝ᵥ r) = true
  rw [LINEQ.simulateQ_sampleRandomVector (F := ZMod 2) polys.length (n + n * n)
    (LPCP.proof π).impl]
  change Pr[accept | ($ᵗ (Fin polys.length → ZMod 2) : ProbComp (Fin polys.length → ZMod 2))] *
    (2 : ENNReal) ≤ 1
  rw [show
      Pr[accept |
          ($ᵗ (Fin polys.length → ZMod 2) : ProbComp (Fin polys.length → ZMod 2))] =
        Pr[fun r : Fin polys.length → ZMod 2 =>
            ((linearMatrix polys) *ᵥ π - linearTarget polys) ⬝ᵥ r = 0 |
          ($ᵗ (Fin polys.length → ZMod 2) : ProbComp (Fin polys.length → ZMod 2))] by
    apply probEvent_ext
    intro r _hr
    dsimp [accept]
    simp [LINEQ.dotProduct_transpose_mulVec_eq (F := ZMod 2) (linearMatrix polys) π
      ((linearMatrix polys) *ᵥ π) r rfl, sub_eq_zero]]
  simpa [ZMod.card] using LINEQ.linear_form_uniform_prob_mul_card_le_one (F := ZMod 2) hd

private lemma tensorSelfVerifier_soundness {n : ℕ}
    (π : Fin (n + n * n) → ZMod 2)
    (hπ : (TENSORQ.projA π, TENSORQ.projB π) ∉ TENSORQ (ZMod 2) n) :
    Pr[= true | simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl)
      (tensorSelfVerifier (n := n))] ≤ 3 / 4 := by
  simp [tensorSelfVerifier]
  rw [← probEvent_eq_eq_probOutput]
  rw [LINEQ.simulateQ_sampleRandomVector (F := ZMod 2) n (n + n * n) (LPCP.proof π).impl]
  have h := TENSORQ.verifier_soundness_after_sampling (F := ZMod 2)
    (TENSORQ.projA π) (TENSORQ.projB π) π hπ
  have hcard :
      (2 * (Fintype.card (ZMod 2) : ENNReal) - 1)
          / (Fintype.card (ZMod 2) : ENNReal) ^ 2 = 3 / 4 := by
    rw [show Fintype.card (ZMod 2) = 2 from ZMod.card 2]
    norm_num [ENNReal.div_eq_inv_mul]
    rw [show (4 : ENNReal) - 1 = 3 by
      exact ENNReal.sub_eq_of_eq_add (by simp : (1 : ENNReal) ≠ ⊤) (by norm_num)]
  rw [hcard] at h
  simpa [TENSORQ.dotProduct_queryA, TENSORQ.dotProduct_queryB] using h

private lemma length_eq_zero_of_not_pow_le {vars : ℕ}
    (x : List (CMvPolynomial vars (ZMod 2)))
    (hlen : ¬2 ^ (vars + vars ^ 2) ≤ 2 ^ (QESAT.size x)) :
    x.length = 0 := by
  by_contra hx
  have hpos : 0 < x.length := Nat.pos_of_ne_zero hx
  have hpow : 2 ^ (vars + vars ^ 2) ≤ 2 ^ (QESAT.size x) := by
    unfold QESAT.size
    apply Nat.pow_le_pow_right
    · norm_num
    · nlinarith [sq_nonneg (vars : ℤ), hpos]
  exact hlen hpow

private lemma mem_of_length_eq_zero {vars : ℕ} (x : List (CMvPolynomial vars (ZMod 2)))
    (hx : x.length = 0) :
    x ∈ QESAT (ZMod 2) vars := by
  have hxnil : x = [] := List.eq_nil_of_length_eq_zero hx
  subst hxnil
  constructor
  · simp
  · exact ⟨fun _ => 0, by simp⟩

private lemma soundness_before_repetition :
    max (7 / 8 : ℝ≥0∞) (3 / 4 + 1 / 100) = 7 / 8 := by
  rw [max_eq_left]
  refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
  · exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.div_ne_top (by simp) (by norm_num),
        ENNReal.div_ne_top (by simp) (by norm_num)⟩
  · exact ENNReal.div_ne_top (by simp) (by norm_num)
  · rw [ENNReal.toReal_add]
    · rw [ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_div]
      norm_num
    · exact ENNReal.div_ne_top (by simp) (by norm_num)
    · exact ENNReal.div_ne_top (by simp) (by norm_num)

def verifier {m n : ℕ} :
    LPCPVerifier (List (CMvPolynomial n F)) size F (fun _ => n + n * n) :=
  fun x => do
    -- create M and c from the input
    -- sample
    -- 4 queries
    sorry

end QESAT

namespace PCP

private def padImpl (F : Type) {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) :
    QueryImpl (PCP.spec F n₀) (OracleComp (PCP.spec F n₁))
  | .inl () => query (spec := PCP.spec F n₁) (.inl ())
  | .inr i => query (spec := PCP.spec F n₁) (.inr (Fin.castLE h i))

private lemma queryBound_simulateQ_padImpl {F : Type} {n₀ n₁ : ℕ} (h : n₀ ≤ n₁)
    {α : Type} {oa : OracleComp (PCP.spec F n₀) α} {q r : ℕ}
    (hoa : QueryBound oa q r) :
    QueryBound (simulateQ (padImpl F h) oa) q r := by
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
            OracleQuery.input_query, padImpl]
          rw [QueryBound, OracleComp.isQueryBound_query_bind_iff]
          exact ⟨hoa.1, fun y => ih y (hoa.2 y)⟩
      | inr _ =>
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
            OracleQuery.input_query, padImpl]
          rw [QueryBound, OracleComp.isQueryBound_query_bind_iff]
          exact ⟨hoa.1, fun y => ih y (hoa.2 y)⟩

private lemma simulateQ_padImpl_eq {F : Type} [SampleableType F] {n₀ n₁ : ℕ}
    (h : n₀ ≤ n₁) {α : Type} (oa : OracleComp (PCP.spec F n₀) α)
    (π₀ : Fin n₀ → F) (π₁ : Fin n₁ → F)
    (hπ : ∀ i, π₁ (Fin.castLE h i) = π₀ i) :
    simulateQ ((rand F).impl + (PCP.proof π₁).impl) (simulateQ (padImpl F h) oa) =
      simulateQ ((rand F).impl + (PCP.proof π₀).impl) oa := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  apply QueryImpl.ext
  intro t
  cases t with
  | inl u =>
      rcases u
      simp [padImpl]
  | inr i =>
      simp [padImpl, hπ i]

end PCP

private lemma queryBound_map {ρ ι α β : Type} {randSpec : OracleSpec ρ}
    {proofSpec : OracleSpec ι} {oa : OracleComp (randSpec + proofSpec) α}
    {q r : ℕ} (f : α → β) (hoa : QueryBound oa q r) :
    QueryBound (f <$> oa) q r := by
  simpa [QueryBound] using
    (OracleComp.isQueryBound_map_iff oa f (r, q)
      (fun
        | .inl _, (r, _) => 0 < r
        | .inr _, (_, q) => 0 < q)
      (fun
        | .inl _, (r, q) => (r - 1, q)
        | .inr _, (r, q) => (r, q - 1))).2 hoa

private lemma queryBound_replicate {ρ ι α : Type} {randSpec : OracleSpec ρ}
    {proofSpec : OracleSpec ι} {oa : OracleComp (randSpec + proofSpec) α}
    {q r : ℕ} (n : ℕ) (hoa : QueryBound oa q r) :
    QueryBound (OracleComp.replicate n oa) (n * q) (n * r) := by
  induction n with
  | zero =>
      simp [OracleComp.replicate, QueryBound]
  | succ n ih =>
      rw [OracleComp.replicate_succ_bind]
      simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        queryBound_bind hoa fun x => queryBound_map (List.cons x) ih

private lemma simulateQ_replicate {ι ι' α : Type} {spec : OracleSpec ι}
    {spec' : OracleSpec ι'} (impl : QueryImpl spec (OracleComp spec')) (n : ℕ)
    (oa : OracleComp spec α) :
    simulateQ impl (OracleComp.replicate n oa) =
      OracleComp.replicate n (simulateQ impl oa) := by
  induction n with
  | zero =>
      simp [OracleComp.replicate]
  | succ n ih =>
      simp [OracleComp.replicate_succ_bind, ih]

private lemma probOutput_true_all_replicate (mx : ProbComp Bool) (n : ℕ) :
    Pr[= true | do
      let xs ← OracleComp.replicate n mx
      pure (xs.all id)] = Pr[= true | mx] ^ n := by
  have hEvent :
      Pr[= true | do
        let xs ← OracleComp.replicate n mx
        pure (xs.all id)] =
        Pr[fun xs : List Bool => xs.all id = true | OracleComp.replicate n mx] := by
    rw [show (do
        let xs ← OracleComp.replicate n mx
        pure (xs.all id)) =
        (fun xs : List Bool => xs.all id) <$> OracleComp.replicate n mx by rfl]
    rw [probOutput_map_eq_tsum_ite, probEvent_eq_tsum_ite]
    apply tsum_congr
    intro xs
    by_cases h : xs.all id = true <;> simp [h]
  rw [hEvent]
  simpa using OracleComp.probEvent_replicate_of_probEvent_cons mx n
    (p := fun xs : List Bool => xs.all id = true)
    (by simp)
    (q := fun b : Bool => b = true)
    (by intro x xs; cases x <;> simp)

private lemma repeated_accept_le {mx : ProbComp Bool} {ε : ℝ≥0∞} {n : ℕ}
    (hmx : Pr[= true | mx] ≤ ε) :
    Pr[= true | do
      let xs ← OracleComp.replicate n mx
      pure (xs.all id)] ≤ ε ^ n := by
  rw [probOutput_true_all_replicate]
  exact pow_le_pow_left₀ (by simp) hmx n

private lemma repeated_accept_ge_one {mx : ProbComp Bool} {n : ℕ}
    (hmx : Pr[= true | mx] ≥ 1) :
    Pr[= true | do
      let xs ← OracleComp.replicate n mx
      pure (xs.all id)] ≥ 1 := by
  rw [probOutput_true_all_replicate]
  exact one_le_pow₀ hmx

private lemma seven_eighths_pow_six_le_half : ((7 / 8 : ℝ≥0∞) ^ 6) ≤ 1 / 2 := by
  refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
  · simp [ENNReal.div_ne_top]
  · exact ENNReal.div_ne_top (by simp) (by norm_num)
  · rw [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_div]
    norm_num

private lemma one_sub_seven_eighths : (1 : ℝ≥0∞) - 7 / 8 = 1 / 8 := by
  apply ENNReal.sub_eq_of_eq_add
  · exact ENNReal.div_ne_top (by simp) (by norm_num)
  · symm
    refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
    · exact ENNReal.add_ne_top.mpr
        ⟨ENNReal.div_ne_top (by simp) (by norm_num),
          ENNReal.div_ne_top (by simp) (by norm_num)⟩
    · simp
    · rw [ENNReal.toReal_add]
      · norm_num [ENNReal.toReal_div]
      · exact ENNReal.div_ne_top (by simp) (by norm_num)
      · exact ENNReal.div_ne_top (by simp) (by norm_num)

private lemma two_eighths_le_half : (1 / 8 : ℝ≥0∞) + 1 / 8 ≤ 1 / 2 := by
  refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
  · exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.div_ne_top (by simp) (by norm_num),
        ENNReal.div_ne_top (by simp) (by norm_num)⟩
  · exact ENNReal.div_ne_top (by simp) (by norm_num)
  · rw [ENNReal.toReal_add]
    · norm_num [ENNReal.toReal_div]
    · exact ENNReal.div_ne_top (by simp) (by norm_num)
    · exact ENNReal.div_ne_top (by simp) (by norm_num)

private lemma false_prob_le_eighth_of_accept_ge_seven_eighths (mx : ProbComp Bool)
    (haccept : (7 / 8 : ℝ≥0∞) ≤ Pr[= true | mx]) :
    Pr[= false | mx] ≤ 1 / 8 := by
  have hsumle : Pr[= true | mx] + Pr[= false | mx] ≤ (1 : ℝ≥0∞) := by
    rw [probOutput_true_add_false]
    exact tsub_le_self
  have hfalse_sub : Pr[= false | mx] ≤ 1 - Pr[= true | mx] :=
    ENNReal.le_sub_of_add_le_left (probOutput_ne_top (mx := mx) (x := true)) hsumle
  exact hfalse_sub.trans (by
    rw [← one_sub_seven_eighths]
    exact tsub_le_tsub_left haccept 1)

private lemma nat_mul_half_pow_clog_le (q : ℕ) :
    (q : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ Nat.clog 2 (100 * q) ≤ 1 / 100 := by
  by_cases hq : q = 0
  · subst q
    simp
  · let rep := Nat.clog 2 (100 * q)
    have hpow_nat : 100 * q ≤ 2 ^ rep := by
      simpa [rep] using Nat.le_pow_clog (by norm_num : 1 < 2) (100 * q)
    have hpow_real : (100 : ℝ) * q ≤ (2 : ℝ) ^ rep := by
      exact_mod_cast hpow_nat
    refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
    · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top q)
        (ENNReal.pow_ne_top (ENNReal.div_ne_top (by simp) (by norm_num)))
    · exact ENNReal.div_ne_top (by simp) (by norm_num)
    · rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
        ENNReal.toReal_div, ENNReal.toReal_natCast]
      norm_num [ENNReal.toReal_ofNat]
      change (q : ℝ) * (1 / 2) ^ rep ≤ 1 / 100
      have hpow_pos : 0 < (2 : ℝ) ^ rep := pow_pos (by norm_num) rep
      rw [show (1 / 2 : ℝ) ^ rep = ((2 : ℝ) ^ rep)⁻¹ by
        rw [one_div, inv_pow]]
      rw [mul_inv_le_iff₀ hpow_pos]
      nlinarith

namespace LPCPToPCP

private def zmod2Bit (a : ZMod 2) : ℕ :=
  if a = 0 then 0 else 1

private lemma zmod2Bit_le_one (a : ZMod 2) : zmod2Bit a ≤ 1 := by
  unfold zmod2Bit
  split <;> omega

private lemma zmod2Bit_cast (a : ZMod 2) : (zmod2Bit a : ZMod 2) = a := by
  unfold zmod2Bit
  by_cases ha : a = 0
  · simp [ha]
  · have hval : a.val = 1 := by
      have hlt : a.val < 2 := ZMod.val_lt a
      have hne : a.val ≠ 0 := by
        intro hzero
        exact ha ((ZMod.val_eq_zero a).mp hzero)
      omega
    simp [(ZMod.val_eq_one (by norm_num) a).mp hval]

private def vectorIndex {n : ℕ} (u : Fin n → ZMod 2) : Fin (2 ^ n) :=
  Nat.binaryFinMapToNat (fun i => zmod2Bit (u i)) fun i => zmod2Bit_le_one (u i)

private def vectorOfIndex {n : ℕ} (i : Fin (2 ^ n)) : Fin n → ZMod 2 :=
  fun j => Nat.getBit j.val i.val

private lemma vectorOfIndex_vectorIndex {n : ℕ} (u : Fin n → ZMod 2) :
    vectorOfIndex (vectorIndex u) = u := by
  funext j
  unfold vectorOfIndex vectorIndex
  rw [Nat.getBit_of_binaryFinMapToNat]
  simp [zmod2Bit_cast]

private def tableFn {n : ℕ} (π : Fin (2 ^ n) → ZMod 2) :
    (Fin n → ZMod 2) → ZMod 2 :=
  fun u => π (vectorIndex u)

private def linearTable {n : ℕ} (π : Fin n → ZMod 2) :
    Fin (2 ^ n) → ZMod 2 :=
  fun i => π ⬝ᵥ vectorOfIndex i

private def tableImpl (n : ℕ) :
    QueryImpl (LPCP.spec (ZMod 2) n) (OracleComp (PCP.spec (ZMod 2) (2 ^ n)))
  | .inl () => query (spec := PCP.spec (ZMod 2) (2 ^ n)) (.inl ())
  | .inr u => query (spec := PCP.spec (ZMod 2) (2 ^ n)) (.inr (vectorIndex u))

@[simp]
private lemma tableFn_linearTable {n : ℕ} (π : Fin n → ZMod 2)
    (u : Fin n → ZMod 2) :
    tableFn (linearTable π) u = π ⬝ᵥ u := by
  simp [tableFn, linearTable, vectorOfIndex_vectorIndex]

private lemma simulateQ_tableImpl_eq {n : ℕ} [SampleableType (ZMod 2)] {α : Type}
    (oa : OracleComp (LPCP.spec (ZMod 2) n) α) (π : Fin (2 ^ n) → ZMod 2) :
    simulateQ ((rand (ZMod 2)).impl + (PCP.proof π).impl) (simulateQ (tableImpl n) oa) =
      simulateQ ((rand (ZMod 2)).impl +
        fun u => (return tableFn π u : ProbComp (ZMod 2))) oa := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  apply QueryImpl.ext
  intro t
  cases t with
  | inl u =>
      rcases u
      simp [tableImpl]
      dsimp [HAdd.hAdd, QueryImpl.add]
  | inr u =>
      simp [tableImpl, tableFn]
      dsimp [HAdd.hAdd, QueryImpl.add]

private lemma simulateQ_tableImpl_linearTable_eq {n : ℕ} [SampleableType (ZMod 2)]
    {α : Type} (oa : OracleComp (LPCP.spec (ZMod 2) n) α) (π : Fin n → ZMod 2) :
    simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
        (simulateQ (tableImpl n) oa) =
      simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) oa := by
  rw [simulateQ_tableImpl_eq]
  congr 1
  apply QueryImpl.ext
  intro u
  simp [LPCP.proof]

private lemma queryBound_simulateQ_tableImpl {n : ℕ} {α : Type}
    {oa : OracleComp (LPCP.spec (ZMod 2) n) α} {q r : ℕ}
    (hoa : QueryBound oa q r) :
    QueryBound (simulateQ (tableImpl n) oa) q r := by
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
            OracleQuery.input_query, tableImpl]
          rw [QueryBound, OracleComp.isQueryBound_query_bind_iff]
          exact ⟨hoa.1, fun y => ih y (hoa.2 y)⟩
      | inr _ =>
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
            OracleQuery.input_query, tableImpl]
          rw [QueryBound, OracleComp.isQueryBound_query_bind_iff]
          exact ⟨hoa.1, fun y => ih y (hoa.2 y)⟩

private def sampleField {n : ℕ} : OracleComp (PCP.spec (ZMod 2) n) (ZMod 2) :=
  query (spec := PCP.spec (ZMod 2) n) (.inl ())

private def sampleVector (tableLength n : ℕ) :
    OracleComp (PCP.spec (ZMod 2) tableLength) (Fin n → ZMod 2) :=
  Fin.mOfFn n fun _ => sampleField (n := tableLength)

private lemma sampleVector_queryBoundAux (m tableLength : ℕ) :
    QueryBound
      (Fin.mOfFn m fun _ => sampleField (n := tableLength)) 0 m := by
  induction m with
  | zero =>
      simp [Fin.mOfFn, QueryBound]
  | succ m ih =>
      simp only [Fin.mOfFn]
      have hHead : QueryBound (sampleField (n := tableLength)) 0 1 := by
        simp [sampleField, QueryBound]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        queryBound_bind hHead fun _ => by
          simpa [QueryBound] using ih

private lemma sampleVector_queryBound (tableLength n : ℕ) :
    QueryBound (sampleVector tableLength n) 0 n := by
  simpa [sampleVector] using sampleVector_queryBoundAux n tableLength

private lemma probOutput_simulateQ_sampleVectorAux [SampleableType (ZMod 2)]
    (m tableLength : ℕ) (impl : QueryImpl (PCP.proofSpec (ZMod 2) tableLength) ProbComp)
    (x : Fin m → ZMod 2) :
    Pr[= x |
      simulateQ ((rand (ZMod 2)).impl + impl)
        (Fin.mOfFn m fun _ => sampleField (n := tableLength))] =
      (Fintype.card (Fin m → ZMod 2) : ENNReal)⁻¹ := by
  induction m with
  | zero =>
      have hx : x = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      subst hx
      simp [Fin.mOfFn]
  | succ m ih =>
      simp only [Fin.mOfFn, sampleField, simulateQ_bind, simulateQ_query,
        simulateQ_pure, OracleQuery.cont_query, id_map, OracleQuery.input_query, rand]
      rw [probOutput_bind_eq_tsum, tsum_fintype]
      rw [Finset.sum_eq_single (x 0)]
      · change Pr[= x 0 | ($ᵗ ZMod 2 : ProbComp (ZMod 2))] *
            Pr[= x |
              (Fin.cons (x 0)) <$>
                simulateQ ((rand (ZMod 2)).impl + impl)
                  (Fin.mOfFn m fun _ => sampleField (n := tableLength))] = _
        rw [probOutput_uniformSample, probOutput_finCons_map_eq, ih]
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin]
        rw [Nat.pow_succ]
        simp only [Nat.cast_mul, Nat.cast_pow]
        rw [ENNReal.mul_inv]
        · rw [mul_comm]
        · left
          exact_mod_cast pow_ne_zero m (Fintype.card_ne_zero (α := ZMod 2))
        · left
          simp
      · intro a _ ha
        change Pr[= a | ($ᵗ ZMod 2 : ProbComp (ZMod 2))] *
            Pr[= x |
              (Fin.cons a) <$>
                simulateQ ((rand (ZMod 2)).impl + impl)
                  (Fin.mOfFn m fun _ => sampleField (n := tableLength))] = 0
        rw [probOutput_finCons_map_ne _ x ha]
        simp
      · intro h
        simp at h

private lemma probOutput_simulateQ_sampleVector [SampleableType (ZMod 2)]
    {tableLength n : ℕ} (impl : QueryImpl (PCP.proofSpec (ZMod 2) tableLength) ProbComp)
    (x : Fin n → ZMod 2) :
    Pr[= x | simulateQ ((rand (ZMod 2)).impl + impl) (sampleVector tableLength n)] =
      (Fintype.card (Fin n → ZMod 2) : ENNReal)⁻¹ := by
  simpa [sampleVector] using probOutput_simulateQ_sampleVectorAux n tableLength impl x

private lemma ofReal_distance_eq_sum {n : ℕ}
    (f g : (Fin n → ZMod 2) → ZMod 2) :
    ENNReal.ofReal (BlrPcp.distance f g) =
      ∑ x : Fin n → ZMod 2,
        (Fintype.card (Fin n → ZMod 2) : ENNReal)⁻¹ * if f x ≠ g x then 1 else 0 := by
  have hvec_pos : 0 < (Fintype.card (Fin n → ZMod 2) : Real) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨0⟩
  rw [BlrPcp.distance]
  rw [ENNReal.ofReal_mul]
  · rw [ENNReal.ofReal_sum_of_nonneg]
    · simp only [ENNReal.ofReal_inv_of_pos hvec_pos, ENNReal.ofReal_natCast]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : f x ≠ g x <;> simp [hx]
    · intro x _
      by_cases hx : f x ≠ g x <;> simp [hx]
  · positivity

private lemma probEvent_sampleVector_eq_distance [SampleableType (ZMod 2)]
    {tableLength n : ℕ} (impl : QueryImpl (PCP.proofSpec (ZMod 2) tableLength) ProbComp)
    (f g : (Fin n → ZMod 2) → ZMod 2) :
    Pr[fun x => f x ≠ g x |
      simulateQ ((rand (ZMod 2)).impl + impl) (sampleVector tableLength n)] =
      ENNReal.ofReal (BlrPcp.distance f g) := by
  rw [ofReal_distance_eq_sum f g]
  rw [probEvent_eq_tsum_ite, tsum_fintype]
  apply Finset.sum_congr rfl
  intro y _
  rw [probOutput_simulateQ_sampleVector (impl := impl) y]
  by_cases hy : f y ≠ g y <;> simp [hy, mul_comm]

private def translateEquiv {n : ℕ} (u : Fin n → ZMod 2) :
    (Fin n → ZMod 2) ≃ (Fin n → ZMod 2) where
  toFun z := fun i => u i + z i
  invFun z := fun i => u i + z i
  left_inv z := by
    funext i
    change u i + (u i + z i) = z i
    have htwo : (2 : ZMod 2) = 0 := by native_decide
    ring_nf
    rw [htwo]
    simp
  right_inv z := by
    funext i
    change u i + (u i + z i) = z i
    have htwo : (2 : ZMod 2) = 0 := by native_decide
    ring_nf
    rw [htwo]
    simp

private lemma probEvent_sampleVector_translate_eq_distance [SampleableType (ZMod 2)]
    {tableLength n : ℕ} (impl : QueryImpl (PCP.proofSpec (ZMod 2) tableLength) ProbComp)
    (f g : (Fin n → ZMod 2) → ZMod 2) (u : Fin n → ZMod 2) :
    Pr[fun z => f (fun i => u i + z i) ≠ g (fun i => u i + z i) |
      simulateQ ((rand (ZMod 2)).impl + impl) (sampleVector tableLength n)] =
      ENNReal.ofReal (BlrPcp.distance f g) := by
  rw [ofReal_distance_eq_sum f g]
  rw [probEvent_eq_tsum_ite, tsum_fintype]
  simp_rw [probOutput_simulateQ_sampleVector (impl := impl)]
  change (∑ z : Fin n → ZMod 2,
      if f (fun i => u i + z i) ≠ g (fun i => u i + z i) then
        (Fintype.card (Fin n → ZMod 2) : ENNReal)⁻¹ else 0) = _
  rw [show (∑ z : Fin n → ZMod 2,
      if f (fun i => u i + z i) ≠ g (fun i => u i + z i) then
        (Fintype.card (Fin n → ZMod 2) : ENNReal)⁻¹ else 0) =
    ∑ z : Fin n → ZMod 2,
      (Fintype.card (Fin n → ZMod 2) : ENNReal)⁻¹ *
        if f (fun i => u i + z i) ≠ g (fun i => u i + z i) then 1 else 0 by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : f (fun i => u i + z i) ≠ g (fun i => u i + z i) <;>
        simp [hz]]
  simpa [translateEquiv] using
    (Equiv.sum_comp (translateEquiv u)
      (fun x : Fin n → ZMod 2 =>
        (Fintype.card (Fin n → ZMod 2) : ENNReal)⁻¹ * if f x ≠ g x then 1 else 0))

private def selfCorrectSample {n : ℕ} (u : Fin n → ZMod 2) :
    OracleComp (PCP.spec (ZMod 2) (2 ^ n)) (ZMod 2) := do
  let z ← sampleVector (2 ^ n) n
  let fz : ZMod 2 ← query (spec := PCP.spec (ZMod 2) (2 ^ n)) (.inr (vectorIndex z))
  let fuz : ZMod 2 ←
    query (spec := PCP.spec (ZMod 2) (2 ^ n)) (.inr (vectorIndex fun i => u i + z i))
  pure (fuz + fz)

private lemma selfCorrectSample_queryBound {n : ℕ} (u : Fin n → ZMod 2) :
    QueryBound (selfCorrectSample u) 2 n := by
  have hProof : ∀ z : Fin n → ZMod 2,
      QueryBound
        (do
          let fz : ZMod 2 ←
            (liftM (query (spec := PCP.spec (ZMod 2) (2 ^ n)) (.inr (vectorIndex z))) :
              OracleComp (PCP.spec (ZMod 2) (2 ^ n)) (ZMod 2))
          let fuz : ZMod 2 ←
            (liftM
              (query (spec := PCP.spec (ZMod 2) (2 ^ n))
                (.inr (vectorIndex fun i => u i + z i))) :
              OracleComp (PCP.spec (ZMod 2) (2 ^ n)) (ZMod 2))
          pure (fuz + fz)) 2 0 := by
    intro z
    simp only [QueryBound]
    rw [OracleComp.isQueryBound_query_bind_iff]
    refine ⟨by simp, fun _ => ?_⟩
    rw [OracleComp.isQueryBound_query_bind_iff]
    exact ⟨by simp, fun _ => trivial⟩
  simpa [selfCorrectSample, Nat.add_assoc] using
    queryBound_bind (sampleVector_queryBound (2 ^ n) n) fun z => hProof z

private def repeatedValue? : List (ZMod 2) → Option (ZMod 2)
  | [] => none
  | y :: ys => if ys.all (fun z => decide (z = y)) then some y else none

private def selfCorrect {n : ℕ} (t : ℕ) (u : Fin n → ZMod 2) :
    OracleComp (PCP.spec (ZMod 2) (2 ^ n)) (Option (ZMod 2)) := do
  let ys ← OracleComp.replicate t (selfCorrectSample u)
  pure (repeatedValue? ys)

private lemma selfCorrect_queryBound {n t : ℕ} (u : Fin n → ZMod 2) :
    QueryBound (selfCorrect (n := n) t u) (2 * t) (t * n) := by
  simpa [selfCorrect, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    queryBound_map repeatedValue? (queryBound_replicate t (selfCorrectSample_queryBound u))

private def simulateVerifier {n : ℕ} (t : ℕ) :
    OracleComp (LPCP.spec (ZMod 2) n) Bool →
      OracleComp (PCP.spec (ZMod 2) (2 ^ n)) Bool :=
  OracleComp.construct
    (fun b => pure b)
    (fun q _oa rec =>
      match q with
      | .inl () => do
          let z : ZMod 2 ← query (spec := PCP.spec (ZMod 2) (2 ^ n)) (.inl ())
          rec z
      | .inr u => do
          let z? ← selfCorrect t u
          match z? with
          | none => pure false
          | some z => rec z)

private lemma simulateVerifier_queryBound {n rep : ℕ}
    {oa : OracleComp (LPCP.spec (ZMod 2) n) Bool} {q r : ℕ}
    (hoa : QueryBound oa q r) :
    QueryBound (simulateVerifier (n := n) rep oa)
      (2 * rep * q) (r + rep * q * n) := by
  revert q r
  induction oa using OracleComp.inductionOn with
  | pure b =>
      intro q r hoa
      simp [simulateVerifier, QueryBound]
  | query_bind t mx ih =>
      intro q r hoa
      rw [QueryBound, OracleComp.isQueryBound_query_bind_iff] at hoa
      cases t with
      | inl u =>
          rcases u
          simp only [simulateVerifier, OracleComp.construct_query_bind]
          rw [QueryBound, OracleComp.isQueryBound_query_bind_iff]
          refine ⟨by omega, fun z => ?_⟩
          refine queryBound_mono (ih z (hoa.2 z)) (by rfl) ?_
          omega
      | inr u =>
          simp only [simulateVerifier, OracleComp.construct_query_bind]
          have hCont : ∀ z? : Option (ZMod 2),
              QueryBound
                (match z? with
                | none => (pure false : OracleComp (PCP.spec (ZMod 2) (2 ^ n)) Bool)
                | some z => simulateVerifier (n := n) rep (mx z))
                (2 * rep * (q - 1)) (r + rep * (q - 1) * n) := by
            intro z?
            cases z? with
            | none =>
                simp [QueryBound]
            | some z =>
                exact ih z (hoa.2 z)
          refine queryBound_mono
            (queryBound_bind (selfCorrect_queryBound (n := n) (t := rep) u) hCont)
            ?_ ?_
          · have hq : q = q - 1 + 1 := by omega
            rw [hq]
            have hq' : q - 1 + 1 - 1 = q - 1 := by omega
            rw [hq']
            calc
              2 * rep + 2 * rep * (q - 1) = 2 * rep * (q - 1 + 1) := by ring
              _ ≤ 2 * rep * (q - 1 + 1) := le_rfl
          · have hq : q = q - 1 + 1 := by omega
            rw [hq]
            have hq' : q - 1 + 1 - 1 = q - 1 := by omega
            rw [hq']
            calc
              rep * n + (r + rep * (q - 1) * n) =
                  r + rep * (q - 1 + 1) * n := by ring
              _ ≤ r + rep * (q - 1 + 1) * n := le_rfl

def verifier {α : Type} (size : α → ℕ) (ℓ q : ℕ → ℕ)
    (V : LPCPVerifier α size (ZMod 2) ℓ) :
    PCPVerifier α size (ZMod 2) (fun n => 2 ^ ℓ n) :=
  fun x => do
    let n := ℓ (size x)
    let rep := Nat.clog 2 (100 * q (size x))
    let hBLR ← simulateQ (tableImpl n) (BLR.basicVerifier (F := ZMod 2) (n := n))
    if hBLR then
      simulateVerifier (n := n) rep (V x)
    else
      pure false

private lemma verifier_queryBound {α : Type} {size : α → ℕ} {ℓ q r : ℕ → ℕ}
    {V : LPCPVerifier α size (ZMod 2) ℓ} {x : α}
    (hV : QueryBound (V x) (q (size x)) (r (size x))) :
    QueryBound (verifier size ℓ q V x)
      (3 + 2 * Nat.clog 2 (100 * q (size x)) * q (size x))
      (r (size x) +
        (2 + Nat.clog 2 (100 * q (size x)) * q (size x)) * ℓ (size x)) := by
  let n := ℓ (size x)
  let rep := Nat.clog 2 (100 * q (size x))
  have hBLR :
      QueryBound
        (simulateQ (tableImpl n) (BLR.basicVerifier (F := ZMod 2) (n := n))) 3 (2 * n) :=
    queryBound_simulateQ_tableImpl BLR_basic_query_complexity
  have hSim :
      QueryBound (simulateVerifier (n := n) rep (V x))
        (2 * rep * q (size x)) (r (size x) + rep * q (size x) * n) :=
    simulateVerifier_queryBound hV
  simp only [verifier]
  refine queryBound_mono
    (queryBound_bind hBLR fun h => by
      cases h
      · simp [QueryBound]
      · exact hSim)
    ?_ ?_
  · subst rep
    rw [Nat.mul_comm 100 (q (size x))]
  · subst n
    subst rep
    rw [Nat.mul_comm 100 (q (size x))]
    ring_nf
    exact le_rfl

private lemma verifier_accept_le_blr {α : Type} [SampleableType (ZMod 2)]
    {size : α → ℕ} {ℓ q : ℕ → ℕ}
    (V : LPCPVerifier α size (ZMod 2) ℓ) (x : α)
    (π : Fin (2 ^ ℓ (size x)) → ZMod 2) :
    Pr[= true | simulateQ ((rand (ZMod 2)).impl + (PCP.proof π).impl)
        (verifier size ℓ q V x)] ≤
      Pr[= true | simulateQ ((rand (ZMod 2)).impl + (PCP.proof π).impl)
        (simulateQ (tableImpl (ℓ (size x)))
          (BLR.basicVerifier (F := ZMod 2) (n := ℓ (size x))))] := by
  simp only [verifier, simulateQ_bind]
  have hle := probOutput_bind_mono
      (mx := simulateQ ((rand (ZMod 2)).impl + (PCP.proof π).impl)
        (simulateQ (tableImpl (ℓ (size x)))
          (BLR.basicVerifier (F := ZMod 2) (n := ℓ (size x)))))
      (my := fun hBLR =>
        simulateQ ((rand (ZMod 2)).impl + (PCP.proof π).impl)
          (if hBLR then
            simulateVerifier (n := ℓ (size x)) (Nat.clog 2 (100 * q (size x))) (V x)
          else
            pure false))
      (oc := fun hBLR => (pure hBLR : ProbComp Bool))
      (y := true) (z := true) (by
        intro hBLR _
        cases hBLR <;> simp [simulateQ_pure])
  simpa [simulateQ_pure] using hle

private lemma verifier_accept_le_simulateVerifier {α : Type} [SampleableType (ZMod 2)]
    {size : α → ℕ} {ℓ q : ℕ → ℕ}
    (V : LPCPVerifier α size (ZMod 2) ℓ) (x : α)
    (π : Fin (2 ^ ℓ (size x)) → ZMod 2) :
    Pr[= true | simulateQ ((rand (ZMod 2)).impl + (PCP.proof π).impl)
        (verifier size ℓ q V x)] ≤
      Pr[= true | simulateQ ((rand (ZMod 2)).impl + (PCP.proof π).impl)
        (simulateVerifier (n := ℓ (size x)) (Nat.clog 2 (100 * q (size x))) (V x))] := by
  simp only [verifier, simulateQ_bind]
  have hle := probOutput_bind_mono
    (mx := simulateQ ((rand (ZMod 2)).impl + (PCP.proof π).impl)
      (simulateQ (tableImpl (ℓ (size x)))
        (BLR.basicVerifier (F := ZMod 2) (n := ℓ (size x)))))
    (my := fun hBLR =>
      simulateQ ((rand (ZMod 2)).impl + (PCP.proof π).impl)
        (if hBLR then
          simulateVerifier (n := ℓ (size x)) (Nat.clog 2 (100 * q (size x))) (V x)
        else
          pure false))
    (oc := fun _ =>
      simulateQ ((rand (ZMod 2)).impl + (PCP.proof π).impl)
        (simulateVerifier (n := ℓ (size x)) (Nat.clog 2 (100 * q (size x))) (V x)))
    (y := true) (z := true) (by
      intro hBLR _
      cases hBLR <;> simp [simulateQ_pure])
  refine hle.trans ?_
  rw [probOutput_bind_const]
  exact mul_le_of_le_one_left (zero_le _) tsub_le_self

private lemma optionBind_accept_le
    (mx : ProbComp (Option (ZMod 2))) (cont : ZMod 2 → ProbComp Bool)
    (exact : ProbComp Bool) (c : ZMod 2) {ε δ : ℝ≥0∞}
    (hcont : Pr[= true | cont c] ≤ Pr[= true | exact] + ε)
    (hbad : Pr[fun z? => ∃ z, z? = some z ∧ z ≠ c | mx] ≤ δ) :
    Pr[= true | mx >>= fun
      | none => pure false
      | some z => cont z] ≤
        Pr[= true | exact] + ε + δ := by
  classical
  let bad : Option (ZMod 2) → Prop := fun z? => ∃ z, z? = some z ∧ z ≠ c
  let branch : Option (ZMod 2) → ProbComp Bool
    | none => pure false
    | some z => cont z
  let mix : Option (ZMod 2) → ProbComp Bool := fun z? =>
    if bad z? then pure true else exact
  have hStep1 :
      Pr[= true | mx >>= branch] ≤ Pr[= true | mx >>= mix] + ε := by
    have hEvent := probEvent_bind_congr_le_add
      (mx := mx) (my := branch) (oc := mix) (q := fun b : Bool => b = true)
      (ε := ε) (by
        intro z? _hz?
        by_cases hz : bad z?
        · simpa [mix, hz] using (calc
            Pr[fun b => b = true | branch z?] ≤ 1 := probEvent_le_one
            _ ≤ 1 + ε := by simp)
        · cases z? with
          | none =>
              simp [branch, mix, hz]
          | some z =>
              have hzc : z = c := by
                by_contra hne
                exact hz ⟨z, rfl, hne⟩
              subst z
              simpa [branch, mix, hz] using hcont)
    simpa [probEvent_eq_eq_probOutput, branch, mix] using hEvent
  have hStep2 :
      Pr[= true | mx >>= mix] ≤ Pr[= true | exact] + δ := by
    have hmix := probOutput_bind_congr_le_add
      (mx := mx) (my := mix)
      (oc₁ := fun _ => exact)
      (oc₂ := fun z? => (pure (decide (bad z?)) : ProbComp Bool))
      (y := true) (z₁ := true) (z₂ := true) (by
        intro z? _hz?
        by_cases hz : bad z? <;> simp [mix, hz])
    have hconst :
        Pr[= true | mx >>= fun _ : Option (ZMod 2) => exact] ≤
          Pr[= true | exact] := by
      rw [probOutput_bind_const]
      exact mul_le_of_le_one_left (zero_le _) tsub_le_self
    have hbad' :
        Pr[= true | mx >>= fun z? => (pure (decide (bad z?)) : ProbComp Bool)] =
          Pr[bad | mx] := by
      rw [← probEvent_eq_eq_probOutput]
      simpa [Function.comp_def] using
        (probEvent_bind_pure_comp (m := ProbComp) (mx := mx)
          (f := fun z? => decide (bad z?)) (q := fun b : Bool => b = true))
    calc
      Pr[= true | mx >>= mix] ≤
          Pr[= true | mx >>= fun _ : Option (ZMod 2) => exact] +
            Pr[= true | mx >>= fun z? => (pure (decide (bad z?)) : ProbComp Bool)] := hmix
      _ ≤ Pr[= true | exact] + δ := by
        rw [hbad']
        exact add_le_add hconst hbad
  calc
    Pr[= true | mx >>= fun
      | none => pure false
      | some z => cont z] = Pr[= true | mx >>= branch] := rfl
    _ ≤ Pr[= true | mx >>= mix] + ε := hStep1
    _ ≤ (Pr[= true | exact] + δ) + ε := add_le_add hStep2 le_rfl
    _ = Pr[= true | exact] + ε + δ := by
      rw [add_assoc, add_comm δ ε, ← add_assoc]

private lemma simulateVerifier_accept_le {n rep : ℕ}
    {oa : OracleComp (LPCP.spec (ZMod 2) n) Bool} {q r : ℕ}
    (hoa : QueryBound oa q r) (πTable : Fin (2 ^ n) → ZMod 2)
    (πLin : Fin n → ZMod 2) {δ : ℝ≥0∞}
    (hWrong : ∀ u : Fin n → ZMod 2,
      Pr[fun z? => ∃ z, z? = some z ∧ z ≠ πLin ⬝ᵥ u |
        simulateQ ((rand (ZMod 2)).impl + (PCP.proof πTable).impl)
          (selfCorrect (n := n) rep u)] ≤ δ) :
    Pr[= true |
      simulateQ ((rand (ZMod 2)).impl + (PCP.proof πTable).impl)
        (simulateVerifier (n := n) rep oa)] ≤
      Pr[= true | simulateQ ((rand (ZMod 2)).impl + (LPCP.proof πLin).impl) oa] +
        q * δ := by
  revert q r
  induction oa using OracleComp.inductionOn with
  | pure b =>
      intro q r hoa
      cases b <;> simp [simulateVerifier]
  | query_bind t mx ih =>
      intro q r hoa
      rw [QueryBound, OracleComp.isQueryBound_query_bind_iff] at hoa
      cases t with
      | inl u =>
          rcases u
          simp only [simulateVerifier, OracleComp.construct_query_bind, simulateQ_bind,
            simulateQ_query, OracleQuery.cont_query, id_map, OracleQuery.input_query]
          dsimp [HAdd.hAdd, QueryImpl.add, rand]
          have hEvent := probEvent_bind_congr_le_add
            (mx := ($ᵗ ZMod 2 : ProbComp (ZMod 2)))
            (my := fun z =>
              simulateQ ((rand (ZMod 2)).impl + (PCP.proof πTable).impl)
                (simulateVerifier (n := n) rep (mx z)))
            (oc := fun z =>
              simulateQ ((rand (ZMod 2)).impl + (LPCP.proof πLin).impl) (mx z))
            (q := fun b : Bool => b = true) (ε := q * δ) (by
              intro z _hz
              simpa [probEvent_eq_eq_probOutput] using ih z (hoa.2 z))
          simpa [probEvent_eq_eq_probOutput] using hEvent
      | inr u =>
          simp only [simulateVerifier, OracleComp.construct_query_bind, simulateQ_bind,
            simulateQ_query, OracleQuery.cont_query, id_map, OracleQuery.input_query]
          dsimp [HAdd.hAdd, QueryImpl.add, LPCP.proof]
          let ans : ZMod 2 := πLin ⬝ᵥ (u : Fin n → ZMod 2)
          have hCont :
              Pr[= true |
                simulateQ ((rand (ZMod 2)).impl + (PCP.proof πTable).impl)
                  (simulateVerifier (n := n) rep (mx ans))] ≤
              Pr[= true |
                  simulateQ ((rand (ZMod 2)).impl + (LPCP.proof πLin).impl)
                    (mx ans)] + ((q - 1 : ℕ) : ℝ≥0∞) * δ :=
            ih ans (hoa.2 ans)
          have hOpt := optionBind_accept_le
            (mx := simulateQ ((rand (ZMod 2)).impl + (PCP.proof πTable).impl)
              (selfCorrect (n := n) rep (u : Fin n → ZMod 2)))
            (cont := fun z =>
              simulateQ ((rand (ZMod 2)).impl + (PCP.proof πTable).impl)
                (simulateVerifier (n := n) rep (mx z)))
            (exact := simulateQ ((rand (ZMod 2)).impl + (LPCP.proof πLin).impl)
              (mx ans))
            (c := ans) hCont (by simpa [ans] using hWrong (u : Fin n → ZMod 2))
          have hOpt' :
              Pr[= true | do
                let z? ← simulateQ ((rand (ZMod 2)).impl + (PCP.proof πTable).impl)
                  (selfCorrect (n := n) rep (u : Fin n → ZMod 2))
                simulateQ ((rand (ZMod 2)).impl + (PCP.proof πTable).impl)
                  (match z? with
                  | none => pure false
                  | some z => simulateVerifier (n := n) rep (mx z))] ≤
                Pr[= true |
                  simulateQ ((rand (ZMod 2)).impl + (LPCP.proof πLin).impl) (mx ans)] +
                  ((q - 1 : ℕ) : ℝ≥0∞) * δ + δ := by
            let impl := (rand (ZMod 2)).impl + (PCP.proof πTable).impl
            let sc := simulateQ impl (selfCorrect (n := n) rep (u : Fin n → ZMod 2))
            have hbranch :
                Pr[= true | sc >>= fun z? =>
                  simulateQ impl
                    (match z? with
                    | none => pure false
                    | some z => simulateVerifier (n := n) rep (mx z))] =
                  Pr[= true | sc >>= fun
                    | none => pure false
                    | some z =>
                        simulateQ impl (simulateVerifier (n := n) rep (mx z))] := by
              apply probOutput_bind_congr
              intro z? _hz?
              cases z? <;> simp [simulateQ_pure]
            simpa [impl, sc, ans] using hbranch.trans_le hOpt
          refine hOpt'.trans ?_
          have hqNat : q = q - 1 + 1 := by omega
          have hq : (q : ℝ≥0∞) = ((q - 1 : ℕ) : ℝ≥0∞) + 1 := by
            exact_mod_cast hqNat
          simpa [ans, simulateQ_pure] using le_of_eq (calc
            Pr[= true | simulateQ ((rand (ZMod 2)).impl + (LPCP.proof πLin).impl)
                (mx ans)] + ((q - 1 : ℕ) : ℝ≥0∞) * δ + δ =
              Pr[= true | simulateQ ((rand (ZMod 2)).impl + (LPCP.proof πLin).impl)
                (mx ans)] + (((q - 1 : ℕ) : ℝ≥0∞) * δ + δ) := by rw [add_assoc]
            _ = Pr[= true | simulateQ ((rand (ZMod 2)).impl + (LPCP.proof πLin).impl)
                (mx ans)] + ((((q - 1 : ℕ) : ℝ≥0∞) + 1) * δ) := by
                  rw [add_mul, one_mul]
            _ = Pr[= true | simulateQ ((rand (ZMod 2)).impl + (LPCP.proof πLin).impl)
                (mx ans)] + (q : ℝ≥0∞) * δ := by rw [← hq])

private lemma repeatedValue?_wrong_imp_all_ne {c : ZMod 2} :
    ∀ {ys : List (ZMod 2)},
      (∃ z, repeatedValue? ys = some z ∧ z ≠ c) → ∀ y ∈ ys, y ≠ c
  | [], h => by
      simp [repeatedValue?] at h
  | y :: ys, h => by
      simp only [List.mem_cons]
      intro z hz
      simp only [repeatedValue?] at h
      by_cases hall : ys.all (fun z => decide (z = y))
      · simp [hall] at h
        have hyc : y ≠ c := h
        rcases hz with rfl | hz
        · exact hyc
        · have hy : z = y := by
            have := List.all_eq_true.mp hall z hz
            simpa using this
          exact hy ▸ hyc
      · simp [hall] at h

private lemma repeated_selfCorrect_wrong_le_pow (mx : ProbComp (ZMod 2))
    (rep : ℕ) (c : ZMod 2) :
    Pr[fun z? => ∃ z, z? = some z ∧ z ≠ c |
      do
        let ys ← OracleComp.replicate rep mx
        pure (repeatedValue? ys)] ≤
      Pr[fun z => z ≠ c | mx] ^ rep := by
  rw [show (do
      let ys ← OracleComp.replicate rep mx
      pure (repeatedValue? ys)) =
        repeatedValue? <$> OracleComp.replicate rep mx by rfl]
  rw [probEvent_map]
  refine (probEvent_mono (mx := OracleComp.replicate rep mx)
    (p := fun ys => ∃ z, repeatedValue? ys = some z ∧ z ≠ c)
    (q := fun ys => ∀ y ∈ ys, y ≠ c) ?_).trans ?_
  · intro ys _ hys
    exact repeatedValue?_wrong_imp_all_ne hys
  · exact le_of_eq (by
      simpa using
        (OracleComp.probEvent_replicate_of_probEvent_cons mx rep
          (p := fun ys : List (ZMod 2) => ∀ y ∈ ys, y ≠ c)
          (by simp)
          (q := fun y : ZMod 2 => y ≠ c)
          (by
            intro y ys
            simp)))

private lemma selfCorrect_wrong_le_of_sample {n rep : ℕ}
    (πTable : Fin (2 ^ n) → ZMod 2) (u : Fin n → ZMod 2) (c : ZMod 2)
    {η : ℝ≥0∞}
    (hSample :
      Pr[fun z => z ≠ c |
        simulateQ ((rand (ZMod 2)).impl + (PCP.proof πTable).impl)
          (selfCorrectSample (n := n) u)] ≤ η) :
    Pr[fun z? => ∃ z, z? = some z ∧ z ≠ c |
      simulateQ ((rand (ZMod 2)).impl + (PCP.proof πTable).impl)
        (selfCorrect (n := n) rep u)] ≤ η ^ rep := by
  simp only [selfCorrect, simulateQ_bind, simulateQ_pure]
  rw [simulateQ_replicate]
  exact (repeated_selfCorrect_wrong_le_pow
    (simulateQ ((rand (ZMod 2)).impl + (PCP.proof πTable).impl)
      (selfCorrectSample (n := n) u)) rep c).trans
    (pow_le_pow_left₀ (by simp) hSample rep)

private lemma linear_selfCorrect_value {n : ℕ} (π : Fin n → ZMod 2)
    (u z : Fin n → ZMod 2) :
    π ⬝ᵥ (fun i => u i + z i) + π ⬝ᵥ z = π ⬝ᵥ u := by
  simp only [dotProduct, mul_add]
  rw [Finset.sum_add_distrib]
  have hdouble : ∑ x : Fin n, π x * z x + ∑ x : Fin n, π x * z x = 0 := by
    have htwo : (2 : ZMod 2) = 0 := by native_decide
    rw [← two_mul]
    rw [htwo, zero_mul]
  rw [add_assoc, hdouble, add_zero]

private lemma selfCorrectSample_wrong_le_two_distance [SampleableType (ZMod 2)]
    {n : ℕ} (πTable : Fin (2 ^ n) → ZMod 2) (πLin : Fin n → ZMod 2)
    (u : Fin n → ZMod 2) :
    Pr[fun y => y ≠ πLin ⬝ᵥ u |
      simulateQ ((rand (ZMod 2)).impl + (PCP.proof πTable).impl) (selfCorrectSample u)] ≤
      ENNReal.ofReal (BlrPcp.distance (tableFn πTable)
        (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) πLin)) +
      ENNReal.ofReal (BlrPcp.distance (tableFn πTable)
        (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) πLin)) := by
  let g := BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) πLin
  have hpoint : ∀ z : Fin n → ZMod 2,
      tableFn πTable (fun i => u i + z i) + tableFn πTable z ≠ πLin ⬝ᵥ u →
        tableFn πTable (fun i => u i + z i) ≠ g (fun i => u i + z i) ∨
          tableFn πTable z ≠ g z := by
    intro z hbad
    by_contra hnot
    push_neg at hnot
    apply hbad
    rw [hnot.1, hnot.2]
    simpa [g, BlrPcp.linearFn, dotProduct] using linear_selfCorrect_value πLin u z
  simp only [selfCorrectSample, simulateQ_bind, simulateQ_query, simulateQ_pure,
    OracleQuery.cont_query, id_map, OracleQuery.input_query]
  dsimp [HAdd.hAdd, QueryImpl.add, PCP.proof]
  simp only [pure_bind]
  change Pr[fun y => y ≠ πLin ⬝ᵥ u |
      (fun z : Fin n → ZMod 2 => tableFn πTable (fun i => u i + z i) + tableFn πTable z) <$>
        simulateQ ((rand (ZMod 2)).impl + (PCP.proof πTable).impl)
          (sampleVector (2 ^ n) n)] ≤ _
  rw [probEvent_map]
  change Pr[fun z : Fin n → ZMod 2 => tableFn πTable (fun i => u i + z i) +
      tableFn πTable z ≠ πLin ⬝ᵥ u |
      simulateQ ((rand (ZMod 2)).impl + (PCP.proof πTable).impl)
        (sampleVector (2 ^ n) n)] ≤ _
  refine (probEvent_mono
      (mx := simulateQ ((rand (ZMod 2)).impl + (PCP.proof πTable).impl)
        (sampleVector (2 ^ n) n))
      (p := fun z : Fin n → ZMod 2 =>
        tableFn πTable (fun i => u i + z i) + tableFn πTable z ≠ πLin ⬝ᵥ u)
      (q := fun z : Fin n → ZMod 2 =>
        tableFn πTable (fun i => u i + z i) ≠ g (fun i => u i + z i) ∨
          tableFn πTable z ≠ g z) ?_).trans ?_
  · intro z _ hz
    exact hpoint z hz
  · refine (probEvent_or_le _ _ _).trans ?_
    rw [probEvent_sampleVector_translate_eq_distance (impl := (PCP.proof πTable).impl)
      (f := tableFn πTable) (g := g) (u := u)]
    rw [probEvent_sampleVector_eq_distance (impl := (PCP.proof πTable).impl)
      (f := tableFn πTable) (g := g)]
    rfl

private lemma selfCorrectSample_linear_probOutput [SampleableType (ZMod 2)]
    {n : ℕ} (π : Fin n → ZMod 2) (u : Fin n → ZMod 2) :
    Pr[= π ⬝ᵥ u |
      simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
        (selfCorrectSample u)] = 1 := by
  simp only [selfCorrectSample, simulateQ_bind, simulateQ_query, simulateQ_pure,
    OracleQuery.cont_query, id_map, OracleQuery.input_query]
  dsimp [HAdd.hAdd, QueryImpl.add, PCP.proof]
  simp only [pure_bind]
  change Pr[= π ⬝ᵥ u |
      (fun z : Fin n → ZMod 2 =>
        linearTable π (vectorIndex (fun i => u i + z i)) + linearTable π (vectorIndex z)) <$>
        simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
          (sampleVector (2 ^ n) n)] = 1
  have hconst :
      (fun z : Fin n → ZMod 2 =>
          linearTable π (vectorIndex (fun i => u i + z i)) + linearTable π (vectorIndex z)) =
        fun _ => π ⬝ᵥ u := by
    funext z
    simpa [linearTable, vectorOfIndex_vectorIndex] using linear_selfCorrect_value π u z
  rw [hconst]
  rw [show (fun _ : Fin n → ZMod 2 => π ⬝ᵥ u) <$>
      simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
        (sampleVector (2 ^ n) n) =
      (do
        let _z ← simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
          (sampleVector (2 ^ n) n)
        pure (π ⬝ᵥ u)) by rfl]
  rw [probOutput_bind_const]
  simp

private lemma repeatedValue?_eq_some_of_forall_eq {c : ZMod 2} :
    ∀ {ys : List (ZMod 2)}, ys ≠ [] → (∀ y ∈ ys, y = c) → repeatedValue? ys = some c
  | [], hnil, _ => (hnil rfl).elim
  | y :: ys, _hnil, hall => by
      have hy : y = c := hall y (by simp)
      have hys : ys.all (fun z => decide (z = y)) = true := by
        apply List.all_eq_true.mpr
        intro z hz
        have hzc : z = c := hall z (by simp [hz])
        exact show decide (z = y) = true by simp [hzc, hy]
      have hysc : ys.all (fun z => decide (z = c)) = true := by
        apply List.all_eq_true.mpr
        intro z hz
        have hzc : z = c := hall z (by simp [hz])
        simp [hzc]
      simp only [repeatedValue?, hy, hysc, if_true]

private lemma selfCorrect_linear_probOutput [SampleableType (ZMod 2)]
    {n rep : ℕ} (hrep : 0 < rep) (π : Fin n → ZMod 2) (u : Fin n → ZMod 2) :
    Pr[= some (π ⬝ᵥ u) |
      simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
        (selfCorrect (n := n) rep u)] = 1 := by
  let c : ZMod 2 := π ⬝ᵥ u
  let mx :=
    simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
      (selfCorrectSample (n := n) u)
  have hmx : Pr[= c | mx] = 1 := by
    simpa [mx, c] using selfCorrectSample_linear_probOutput π u
  have hsupport : support mx = {c} := (probOutput_eq_one_iff.mp hmx).2
  simp only [selfCorrect, simulateQ_bind, simulateQ_pure]
  rw [simulateQ_replicate]
  rw [show (do
      let ys ← OracleComp.replicate rep mx
      pure (repeatedValue? ys)) =
      repeatedValue? <$> OracleComp.replicate rep mx by rfl]
  rw [← probEvent_eq_eq_probOutput]
  rw [probEvent_map]
  have hall :
      Pr[fun ys : List (ZMod 2) => ∀ y ∈ ys, y = c | OracleComp.replicate rep mx] = 1 := by
    rw [OracleComp.probEvent_replicate_of_probEvent_cons mx rep
      (p := fun ys : List (ZMod 2) => ∀ y ∈ ys, y = c)
      (by simp)
      (q := fun y : ZMod 2 => y = c)]
    · rw [probEvent_eq_eq_probOutput, hmx]
      simp
    · intro y ys
      simp
  have hmono :
      Pr[fun ys : List (ZMod 2) => ∀ y ∈ ys, y = c | OracleComp.replicate rep mx] ≤
        Pr[fun ys : List (ZMod 2) => repeatedValue? ys = some c |
          OracleComp.replicate rep mx] := by
    refine probEvent_mono
      (mx := OracleComp.replicate rep mx)
      (p := fun ys : List (ZMod 2) => ∀ y ∈ ys, y = c)
      (q := fun ys : List (ZMod 2) => repeatedValue? ys = some c) ?_
    intro ys hys hall'
    rw [OracleComp.support_replicate] at hys
    exact repeatedValue?_eq_some_of_forall_eq
      (by
        intro hnil
        have hlen : ys.length = rep := hys.1
        rw [hnil] at hlen
        simp at hlen
        omega)
      hall'
  exact le_antisymm probEvent_le_one (by simpa [hall] using hmono)

private lemma simulateVerifier_linear_accept_ge [SampleableType (ZMod 2)] {n rep : ℕ}
    {oa : OracleComp (LPCP.spec (ZMod 2) n) Bool} {q r : ℕ}
    (hoa : QueryBound oa q r) (hrep : q = 0 ∨ 0 < rep) (π : Fin n → ZMod 2) :
    Pr[= true | simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) oa] ≤
      Pr[= true |
        simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
          (simulateVerifier (n := n) rep oa)] := by
  revert q r
  induction oa using OracleComp.inductionOn with
  | pure b =>
      intro q r _ _
      cases b <;> simp [simulateVerifier]
  | query_bind t mx ih =>
      intro q r hoa hrep
      rw [QueryBound, OracleComp.isQueryBound_query_bind_iff] at hoa
      cases t with
      | inl u =>
          rcases u
          simp only [simulateVerifier, OracleComp.construct_query_bind, simulateQ_bind,
            simulateQ_query, OracleQuery.cont_query, id_map, OracleQuery.input_query]
          dsimp [HAdd.hAdd, QueryImpl.add, rand]
          refine probOutput_bind_mono (y := true) (z := true) ?_
          intro z _
          exact ih z (hoa.2 z) hrep
      | inr u =>
          simp only [simulateVerifier, OracleComp.construct_query_bind, simulateQ_bind,
            simulateQ_query, OracleQuery.cont_query, id_map, OracleQuery.input_query]
          dsimp [HAdd.hAdd, QueryImpl.add, LPCP.proof]
          let ans : ZMod 2 := π ⬝ᵥ (u : Fin n → ZMod 2)
          have hrep_pos : 0 < rep := by
            rcases hrep with hq | hrep_pos
            · omega
            · exact hrep_pos
          have hcont :
              Pr[= true | simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl)
                (mx ans)] ≤
              Pr[= true |
                simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
                  (simulateVerifier (n := n) rep (mx ans))] :=
            ih ans (hoa.2 ans) (by omega)
          let sc :=
            simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
              (selfCorrect (n := n) rep (u : Fin n → ZMod 2))
          have hsc : Pr[= some ans | sc] = 1 := by
            simpa [sc, ans] using selfCorrect_linear_probOutput hrep_pos π (u : Fin n → ZMod 2)
          have hsupport : support sc = {some ans} := (probOutput_eq_one_iff.mp hsc).2
          have hbind :
              Pr[= true | sc >>= fun
                | none =>
                    simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
                      (pure false)
                | some z =>
                    simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
                      (simulateVerifier (n := n) rep (mx z))] =
              Pr[= true | sc >>= fun _ =>
                    simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
                      (simulateVerifier (n := n) rep (mx ans))] := by
            apply probOutput_bind_congr
            intro z hz
            have hz' : z = some ans := by
              simpa [hsupport] using hz
            subst z
            simp
          have hfail : Pr[⊥ | sc] = 0 := (probOutput_eq_one_iff.mp hsc).1
          have hmatch :
              Pr[= true | sc >>= fun
                  | none =>
                      simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
                        (pure false)
                  | some z =>
                      simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
                        (simulateVerifier (n := n) rep (mx z))] =
              Pr[= true | sc >>= fun x =>
                  simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
                    (match x with
                    | none => pure false
                    | some z => simulateVerifier (n := n) rep (mx z))] := by
            apply probOutput_bind_congr
            intro z _hz
            cases z <;> simp [simulateQ_pure]
          calc
            Pr[= true | simulateQ (QueryImpl.add (fun _ => $ᵗ ZMod 2)
                (fun u => pure (π ⬝ᵥ u))) (mx ans)] ≤
                Pr[= true |
                  simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
                    (simulateVerifier (n := n) rep (mx ans))] := by
                  simpa [LPCP.proof, ans] using hcont
            _ = Pr[= true | sc >>= fun _ =>
                  simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
                    (simulateVerifier (n := n) rep (mx ans))] := by
                  rw [probOutput_bind_const, hfail]
                  simp
            _ = Pr[= true | sc >>= fun
                  | none =>
                      simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
                        (pure false)
                  | some z =>
                      simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
                        (simulateVerifier (n := n) rep (mx z))] := hbind.symm
            _ = Pr[= true | sc >>= fun x =>
                  simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
                    (match x with
                    | none => pure false
                    | some z => simulateVerifier (n := n) rep (mx z))] := hmatch
            _ = Pr[= true | do
                  let x ← simulateQ (QueryImpl.add (fun _ => $ᵗ ZMod 2)
                    (fun q => pure (linearTable π q))) (selfCorrect rep u)
                  simulateQ (QueryImpl.add (fun _ => $ᵗ ZMod 2)
                    (fun q => pure (linearTable π q)))
                    (match x with
                    | none => pure false
                    | some z => simulateVerifier (n := n) rep (mx z))] := by
                  simp [sc, PCP.proof, rand, HAdd.hAdd, simulateVerifier]
            _ ≤ _ := by
                  simp [simulateVerifier]

private lemma blrPrecheck_linear_probOutput [SampleableType (ZMod 2)]
    {n : ℕ} (π : Fin n → ZMod 2) :
    Pr[= true |
      simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
        (simulateQ (tableImpl n) (BLR.basicVerifier (F := ZMod 2) (n := n)))] = 1 := by
  rw [simulateQ_tableImpl_linearTable_eq]
  simp [BLR.basicVerifier, BLR.basicSampleVector, BLR.basicSampleField, LPCP.proof,
    dotProduct, Finset.sum_add_distrib, mul_add]

private lemma verifier_linear_accept_ge {α : Type} [SampleableType (ZMod 2)]
    {size : α → ℕ} {ℓ q : ℕ → ℕ}
    {V : LPCPVerifier α size (ZMod 2) ℓ} {x : α}
    {rV : ℕ} (hV : QueryBound (V x) (q (size x)) rV)
    (hrep : q (size x) = 0 ∨ 0 < Nat.clog 2 (100 * q (size x)))
    (π : Fin (ℓ (size x)) → ZMod 2) :
    Pr[= true | simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) (V x)] ≤
      Pr[= true | simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
        (verifier size ℓ q V x)] := by
  let n := ℓ (size x)
  let rep := Nat.clog 2 (100 * q (size x))
  let blr :=
    simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
      (simulateQ (tableImpl n) (BLR.basicVerifier (F := ZMod 2) (n := n)))
  let sim :=
    simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
      (simulateVerifier (n := n) rep (V x))
  have hSim :
      Pr[= true | simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) (V x)] ≤
        Pr[= true | sim] := by
    simpa [sim, n, rep] using
      simulateVerifier_linear_accept_ge (n := n) (rep := rep) hV hrep π
  have hBLR : Pr[= true | blr] = 1 := by
    simpa [blr, n] using blrPrecheck_linear_probOutput (n := n) π
  have hsupport : support blr = {true} := (probOutput_eq_one_iff.mp hBLR).2
  have hfail : Pr[⊥ | blr] = 0 := (probOutput_eq_one_iff.mp hBLR).1
  have hfinal :
      Pr[= true | blr >>= fun h => if h then sim else pure false] =
        Pr[= true | blr >>= fun _ => sim] := by
    apply probOutput_bind_congr
    intro b hb
    have hbtrue : b = true := by simpa [hsupport] using hb
    subst b
    simp
  simp only [verifier, simulateQ_bind]
  calc
    Pr[= true | simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) (V x)] ≤
        Pr[= true | sim] := hSim
    _ = Pr[= true | blr >>= fun _ => sim] := by
      rw [probOutput_bind_const, hfail]
      simp
    _ = Pr[= true | blr >>= fun h => if h then sim else pure false] := hfinal.symm
    _ = Pr[= true | do
          let hBLR ←
            simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
              (simulateQ (tableImpl (ℓ (size x)))
                (BLR.basicVerifier (F := ZMod 2) (n := ℓ (size x))))
          simulateQ ((rand (ZMod 2)).impl + (PCP.proof (linearTable π)).impl)
            (if hBLR then
              simulateVerifier (n := ℓ (size x)) (Nat.clog 2 (100 * q (size x))) (V x)
            else
              pure false)] := by
      simp [blr, sim, n, rep, PCP.proof, rand, HAdd.hAdd]
    _ ≤ _ := by
      simp [PCP.proof, rand, HAdd.hAdd]

private noncomputable def nearestLinearCoeff {n : ℕ}
    (f : (Fin n → ZMod 2) → ZMod 2) : Fin n → ZMod 2 :=
  Classical.choose (Finset.exists_min_image
    (s := (Finset.univ : Finset (Fin n → ZMod 2)))
    (f := fun π => BlrPcp.distance f (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π))
    ⟨0, by simp⟩)

private lemma nearestLinearCoeff_min {n : ℕ}
    (f : (Fin n → ZMod 2) → ZMod 2) (π : Fin n → ZMod 2) :
    BlrPcp.distance f (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n)
      (nearestLinearCoeff f)) ≤
      BlrPcp.distance f (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π) := by
  classical
  have h := Classical.choose_spec (Finset.exists_min_image
    (s := (Finset.univ : Finset (Fin n → ZMod 2)))
    (f := fun π => BlrPcp.distance f (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π))
    ⟨0, by simp⟩)
  exact h.2 π (by simp)

private lemma distanceToLinear_le_linearFn {n : ℕ}
    (f : (Fin n → ZMod 2) → ZMod 2) (π : Fin n → ZMod 2) :
    BlrPcp.distanceToLinear (F := ZMod 2) (Idx := Fin n) f ≤
      BlrPcp.distance f (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π) := by
  classical
  unfold BlrPcp.distanceToLinear
  apply Finset.inf'_le
  change BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π ∈
    ((Finset.univ : Finset (BlrPcp.ScalarFn (ZMod 2) (Fin n))).filter fun g =>
      g ∈ BlrPcp.LinearSet (F := ZMod 2) (Idx := Fin n))
  simp [BlrPcp.LinearSet, BlrPcp.IsLinear]
  exact ⟨π, fun _ => rfl⟩

private lemma nearestLinearCoeff_distance_le_distanceToLinear {n : ℕ}
    (f : (Fin n → ZMod 2) → ZMod 2) :
    BlrPcp.distance f (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n)
      (nearestLinearCoeff f)) ≤
    BlrPcp.distanceToLinear (F := ZMod 2) (Idx := Fin n) f := by
  classical
  unfold BlrPcp.distanceToLinear
  apply Finset.le_inf'
  intro g hg
  change g ∈ ((Finset.univ : Finset (BlrPcp.ScalarFn (ZMod 2) (Fin n))).filter fun g =>
    g ∈ BlrPcp.LinearSet (F := ZMod 2) (Idx := Fin n)) at hg
  rw [Finset.mem_filter] at hg
  rcases hg.2 with ⟨π, hπ⟩
  have hdist :
      BlrPcp.distance f g =
        BlrPcp.distance f (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) π) := by
    congr 1
    ext x
    exact hπ x
  rw [hdist]
  exact nearestLinearCoeff_min f π

private lemma nearestLinearCoeff_distance_eq_distanceToLinear {n : ℕ}
    (f : (Fin n → ZMod 2) → ZMod 2) :
    BlrPcp.distance f (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n)
      (nearestLinearCoeff f)) =
    BlrPcp.distanceToLinear (F := ZMod 2) (Idx := Fin n) f := by
  exact le_antisymm (nearestLinearCoeff_distance_le_distanceToLinear f)
    (distanceToLinear_le_linearFn f (nearestLinearCoeff f))

private lemma nearestLinearCoeff_distance_le_basicReject [SampleableType (ZMod 2)]
    {n : ℕ} (πTable : Fin (2 ^ n) → ZMod 2) :
    ENNReal.ofReal (BlrPcp.distance (tableFn πTable)
      (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n)
        (nearestLinearCoeff (tableFn πTable)))) ≤
    Pr[= false |
      simulateQ ((rand (ZMod 2)).impl + (PCP.proof πTable).impl)
        (simulateQ (tableImpl n) (BLR.basicVerifier (F := ZMod 2) (n := n)))] := by
  by_cases hn : n = 0
  · subst n
    haveI : Subsingleton (Fin 0 → ZMod 2) := ⟨by
      intro u v
      funext i
      exact Fin.elim0 i⟩
    have hdouble : ∀ a : ZMod 2, a + a = 0 := by
      intro a
      have htwo : (2 : ZMod 2) = 0 := by native_decide
      rw [← two_mul, htwo, zero_mul]
    rw [simulateQ_tableImpl_eq]
    simp [BLR.basicVerifier, BLR.basicSampleVector, Fin.mOfFn, tableFn, BlrPcp.distance,
      BlrPcp.linearFn, HAdd.hAdd, QueryImpl.add]
    have hidx0 : vectorIndex Fin.elim0 = vectorIndex default := by
      congr
      exact Subsingleton.elim _ _
    have hidx_add :
        vectorIndex (fun i : Fin 0 => Add.add i.elim0 i.elim0) = vectorIndex default := by
      congr
      exact Subsingleton.elim _ _
    have hidx_const : vectorIndex (fun _ : Fin 0 => default) = vectorIndex default := by
      congr
    rw [hidx0, hidx_add]
    have ha :
        Add.add (πTable (vectorIndex default)) (πTable (vectorIndex default)) = 0 :=
      hdouble (πTable (vectorIndex default))
    rw [ha]
    by_cases h : 0 = πTable (vectorIndex
        (@default (BlrPcp.Vec (ZMod 2) (Fin 0))
          (@Unique.instInhabited (BlrPcp.Vec (ZMod 2) (Fin 0)) inferInstance)))
    · have h' : πTable (vectorIndex
          (@default (BlrPcp.Vec (ZMod 2) (Fin 0))
            (@Unique.instInhabited (BlrPcp.Vec (ZMod 2) (Fin 0)) inferInstance))) = 0 :=
        h.symm
      have hleft :
          ENNReal.ofReal
            (if πTable (vectorIndex
                (@default (BlrPcp.Vec (ZMod 2) (Fin 0))
                  (@Unique.instInhabited (BlrPcp.Vec (ZMod 2) (Fin 0)) inferInstance))) =
              0 then (0 : ℝ) else 1) = 0 := by
        simp only [if_pos h', ENNReal.ofReal_zero]
      have hright : (if 0 = πTable
          (vectorIndex
            (@default (BlrPcp.Vec (ZMod 2) (Fin 0))
              (@Unique.instInhabited (BlrPcp.Vec (ZMod 2) (Fin 0)) inferInstance))) then
          (0 : ℝ≥0∞) else 1) = 0 := by
        simp only [if_pos h]
      exact hleft.trans_le (zero_le _)
    · have hleft :
          ¬πTable (vectorIndex
            (@default (BlrPcp.Vec (ZMod 2) (Fin 0))
              (@Unique.instInhabited (BlrPcp.Vec (ZMod 2) (Fin 0)) inferInstance))) = 0 :=
        fun h' => h h'.symm
      split_ifs with hA hB <;> simp_all
      exact h (by
        congr
        exact Subsingleton.elim _ _)
  · letI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    rw [simulateQ_tableImpl_eq]
    simpa [distanceToLin, nearestLinearCoeff_distance_eq_distanceToLinear] using
      BLR_basic_soundness_ZMod2 (n := n) (tableFn πTable)

end LPCPToPCP

theorem QESAT_poly_LPCP {vars : ℕ} :
    QESAT (ZMod 2) vars ∈
      LPCP (QESAT.size) 0 (3 / 4) (ZMod 2)
        (fun _ => vars + vars ^ 2) (fun _ => 4) (fun n => n + 2 * vars) := by
  have hpoly :
      QESAT (ZMod 2) vars ∈
        LPCP (QESAT.size) 0 (3 / 4) (ZMod 2)
          (fun _ => vars + vars * vars) (fun _ => 4) (fun n => n + 2 * vars) := by
    refine ⟨QESAT.polyVerifier (n := vars), 0, fun polys => ?_⟩
    refine ⟨by simp [RunsInTime], ?_, ?_, ?_⟩
    · exact QESAT.polyVerifier_queryBound (n := vars) polys
    · rintro ⟨hdeg, a, ha⟩
      refine ⟨TENSORQ.honestProof (a, fun q : Fin vars × Fin vars => a q.1 * a q.2), ?_⟩
      have hlin :
          (QESAT.linearMatrix polys) *ᵥ
              TENSORQ.honestProof (a, fun q : Fin vars × Fin vars => a q.1 * a q.2) =
            QESAT.linearTarget polys :=
        QESAT.linearMatrix_mul_honestProof hdeg ha
      have hline_r (r : Fin polys.length → ZMod 2) :
          TENSORQ.honestProof (a, fun q : Fin vars × Fin vars => a q.1 * a q.2) ⬝ᵥ
              (QESAT.linearMatrix polys)ᵀ *ᵥ r =
            QESAT.linearTarget polys ⬝ᵥ r :=
        LINEQ.dotProduct_transpose_mulVec_eq (F := ZMod 2) (QESAT.linearMatrix polys)
          (TENSORQ.honestProof (a, fun q : Fin vars × Fin vars => a q.1 * a q.2))
          (QESAT.linearTarget polys) r hlin
      simp [QESAT.polyVerifier, LINEQ.verifier, LINEQ.sampleRandomVector,
        hline_r,
        QESAT.tensorSelfVerifier, TENSORQ.dotProduct_queryA, TENSORQ.dotProduct_queryB,
        TENSORQ.projA_honestProof, TENSORQ.projB_honestProof,
        TENSORQ.tensor_check_complete]
      rw [if_pos hdeg]
    · intro hx π
      by_cases hdeg : ∀ p ∈ polys, p.totalDegree ≤ 2
      · let impl := (rand (ZMod 2)).impl + (LPCP.proof π).impl
        let line :=
          LINEQ.verifier (F := ZMod 2) (QESAT.linearMatrix polys, QESAT.linearTarget polys)
        let tensor := QESAT.tensorSelfVerifier (n := vars)
        by_cases htensor : (TENSORQ.projA π, TENSORQ.projB π) ∈ TENSORQ (ZMod 2) vars
        · have hd :
              (QESAT.linearMatrix polys) *ᵥ π - QESAT.linearTarget polys ≠ 0 := by
            intro hzero
            exact hx (QESAT.mem_of_tensor_linear hdeg htensor (sub_eq_zero.mp hzero))
          have hline := QESAT.lineSubcheck_soundness (n := vars) polys π hd
          have hmain_le_line :
              Pr[= true | simulateQ impl (QESAT.polyVerifier (n := vars) polys)] ≤
                Pr[= true | simulateQ impl line] := by
            dsimp [QESAT.polyVerifier, impl]
            rw [if_pos hdeg]
            change
              Pr[= true | simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl)
                (do
                  let hLine ← line
                  let hTensor ← tensor
                  pure (hLine && hTensor))] ≤
              Pr[= true | simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) line]
            simp only [simulateQ_bind, simulateQ_pure]
            have hle :
                Pr[= true | do
                  let hLine ← simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) line
                  let hTensor ← simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) tensor
                  pure (hLine && hTensor)] ≤
                Pr[= true | do
                  let hLine ← simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) line
                  pure hLine] := by
              refine probOutput_bind_mono
                (mx := simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) line)
                (my := fun hLine => do
                  let hTensor ← simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) tensor
                  pure (hLine && hTensor))
                (oc := fun hLine => (pure hLine : ProbComp Bool))
                (y := true) (z := true) ?_
              intro hLine _
              cases hLine <;> simp
            simpa using hle
          have hhalf : 1 / (Fintype.card (ZMod 2) : ENNReal) ≤ 3 / 4 := by
            rw [show Fintype.card (ZMod 2) = 2 from ZMod.card 2]
            refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
            · exact ENNReal.div_ne_top (by simp) (by norm_num)
            · exact ENNReal.div_ne_top (by simp) (by norm_num)
            · rw [ENNReal.toReal_div, ENNReal.toReal_div]
              all_goals norm_num
          exact hmain_le_line.trans (hline.trans hhalf)
        · have htensor_bound := QESAT.tensorSelfVerifier_soundness (n := vars) π htensor
          have hmain_le_tensor :
              Pr[= true | simulateQ impl (QESAT.polyVerifier (n := vars) polys)] ≤
                Pr[= true | simulateQ impl tensor] := by
            dsimp [QESAT.polyVerifier, impl]
            rw [if_pos hdeg]
            change
              Pr[= true | simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl)
                (do
                  let hLine ← line
                  let hTensor ← tensor
                  pure (hLine && hTensor))] ≤
              Pr[= true | simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) tensor]
            simp only [simulateQ_bind, simulateQ_pure]
            rw [probOutput_bind_bind_swap
              (mx := simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) line)
              (my := simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) tensor)
              (f := fun hLine hTensor => (pure (hLine && hTensor) : ProbComp Bool))
              (z := true)]
            have hle :
                Pr[= true | do
                  let hTensor ← simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) tensor
                  let hLine ← simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) line
                  pure (hLine && hTensor)] ≤
                Pr[= true | do
                  let hTensor ← simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) tensor
                  pure hTensor] := by
              refine probOutput_bind_mono
                (mx := simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) tensor)
                (my := fun hTensor => do
                  let hLine ← simulateQ ((rand (ZMod 2)).impl + (LPCP.proof π).impl) line
                  pure (hLine && hTensor))
                (oc := fun hTensor => (pure hTensor : ProbComp Bool))
                (y := true) (z := true) ?_
              intro hTensor _
              cases hTensor <;> simp
            simpa using hle
          exact hmain_le_tensor.trans htensor_bound
      · dsimp [QESAT.polyVerifier]
        rw [if_neg hdeg]
        simp
  simpa [sq] using hpoly

theorem LPCP_to_PCP_ZMod2 {α : Type} (size : α → ℕ)
    (ε_c ε_s : ℝ≥0∞) (ℓ q r : ℕ → ℕ) :
    LPCP size ε_c ε_s (ZMod 2) ℓ q r
    ⊆ PCP size ε_c (max (7 / 8) (ε_s + 1 / 100)) (ZMod 2)
      (fun n => 2 ^ ℓ n)
      (fun n => 3 + 2 * Nat.clog 2 (100 * q n) * q n)
      (fun n => r n + (2 + Nat.clog 2 (100 * q n) * q n) * ℓ n) :=
by
  intro L hL
  rcases hL with ⟨V, t, hV⟩
  refine ⟨LPCPToPCP.verifier size ℓ q V, t, fun x => ?_⟩
  rcases hV x with ⟨hTime, hQuery, hComplete, hSound⟩
  refine ⟨by simp [RunsInTime], LPCPToPCP.verifier_queryBound hQuery, ?_, ?_⟩
  · intro hx
    rcases hComplete hx with ⟨πLin, hπLin⟩
    refine ⟨LPCPToPCP.linearTable πLin, ?_⟩
    have hrep : q (size x) = 0 ∨ 0 < Nat.clog 2 (100 * q (size x)) := by
      by_cases hq : q (size x) = 0
      · exact Or.inl hq
      · right
        exact Nat.clog_pos (by norm_num) (by
          have hqpos : 0 < q (size x) := Nat.pos_of_ne_zero hq
          omega)
    exact le_trans hπLin (LPCPToPCP.verifier_linear_accept_ge hQuery hrep πLin)
  · intro hx π
    let n := ℓ (size x)
    let rep := Nat.clog 2 (100 * q (size x))
    let blr :=
      simulateQ ((rand (ZMod 2)).impl + (PCP.proof π).impl)
        (simulateQ (LPCPToPCP.tableImpl n) (BLR.basicVerifier (F := ZMod 2) (n := n)))
    by_cases hLow : Pr[= true | blr] ≤ (7 / 8 : ℝ≥0∞)
    · exact (LPCPToPCP.verifier_accept_le_blr V x π).trans
        (hLow.trans (le_max_left _ _))
    · let πLin := LPCPToPCP.nearestLinearCoeff (LPCPToPCP.tableFn π)
      have hHigh : (7 / 8 : ℝ≥0∞) ≤ Pr[= true | blr] := le_of_not_ge hLow
      have hRejectSmall : Pr[= false | blr] ≤ 1 / 8 :=
        false_prob_le_eighth_of_accept_ge_seven_eighths blr hHigh
      have hDistSmall :
          ENNReal.ofReal (BlrPcp.distance (LPCPToPCP.tableFn π)
            (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) πLin)) ≤ 1 / 8 := by
        have hDistReject := LPCPToPCP.nearestLinearCoeff_distance_le_basicReject
          (n := n) π
        have hDistReject' :
            ENNReal.ofReal (BlrPcp.distance (LPCPToPCP.tableFn π)
              (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) πLin)) ≤
              Pr[= false | blr] := by
          simpa [πLin, blr, n] using hDistReject
        exact hDistReject'.trans hRejectSmall
      have hSample :
          ∀ u : Fin n → ZMod 2,
            Pr[fun y => y ≠ πLin ⬝ᵥ u |
              simulateQ ((rand (ZMod 2)).impl + (PCP.proof π).impl)
                (LPCPToPCP.selfCorrectSample (n := n) u)] ≤ 1 / 2 := by
        intro u
        have hOne := LPCPToPCP.selfCorrectSample_wrong_le_two_distance
          (n := n) π πLin u
        calc
          Pr[fun y => y ≠ πLin ⬝ᵥ u |
              simulateQ ((rand (ZMod 2)).impl + (PCP.proof π).impl)
                (LPCPToPCP.selfCorrectSample (n := n) u)] ≤
              ENNReal.ofReal (BlrPcp.distance (LPCPToPCP.tableFn π)
                (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) πLin)) +
              ENNReal.ofReal (BlrPcp.distance (LPCPToPCP.tableFn π)
                (BlrPcp.linearFn (F := ZMod 2) (Idx := Fin n) πLin)) := hOne
          _ ≤ 1 / 8 + 1 / 8 := add_le_add hDistSmall hDistSmall
          _ ≤ 1 / 2 := two_eighths_le_half
      have hWrong :
          ∀ u : Fin n → ZMod 2,
            Pr[fun z? => ∃ z, z? = some z ∧ z ≠ πLin ⬝ᵥ u |
              simulateQ ((rand (ZMod 2)).impl + (PCP.proof π).impl)
                (LPCPToPCP.selfCorrect (n := n) rep u)] ≤
              (1 / 2 : ℝ≥0∞) ^ rep := by
        intro u
        exact LPCPToPCP.selfCorrect_wrong_le_of_sample
          (n := n) (rep := rep) π u (πLin ⬝ᵥ u) (hSample u)
      have hSim := LPCPToPCP.simulateVerifier_accept_le
        (n := n) (rep := rep) hQuery π πLin hWrong
      have hFinal := LPCPToPCP.verifier_accept_le_simulateVerifier
        (ℓ := ℓ) (q := q) V x π
      have hPow :
          (q (size x) : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ rep ≤ 1 / 100 := by
        simpa [rep] using nat_mul_half_pow_clog_le (q (size x))
      calc
        Pr[= true | simulateQ ((rand (ZMod 2)).impl + (PCP.proof π).impl)
            (LPCPToPCP.verifier size ℓ q V x)] ≤
            Pr[= true | simulateQ ((rand (ZMod 2)).impl + (PCP.proof π).impl)
              (LPCPToPCP.simulateVerifier (n := ℓ (size x))
                (Nat.clog 2 (100 * q (size x))) (V x))] := hFinal
        _ ≤ Pr[= true | simulateQ ((rand (ZMod 2)).impl + (LPCP.proof πLin).impl)
              (V x)] + (q (size x) : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ rep := by
            simpa [n, rep] using hSim
        _ ≤ ε_s + 1 / 100 := add_le_add (hSound hx πLin) hPow
        _ ≤ max (7 / 8) (ε_s + 1 / 100) := le_max_right _ _

theorem QESAT_exp_PCP_before_repetition {vars : ℕ} : ∃ (q : ℕ) (r : Polynomial ℕ),
    QESAT (ZMod 2) vars ∈
      PCP (QESAT.size) 0 (7 / 8) (ZMod 2)
        (fun n => 2 ^ n) (fun _ => q) r.eval := by
  let q' := 3 + 2 * Nat.clog 2 (100 * 4) * 4
  let c := 2 + Nat.clog 2 (100 * 4) * 4
  let r' : Polynomial ℕ :=
    Polynomial.X + Polynomial.C (2 * vars) + Polynomial.C c * Polynomial.C (vars + vars ^ 2)
  refine ⟨q', r', ?_⟩
  have hConverted := (LPCP_to_PCP_ZMod2 (QESAT.size)
    0 (3 / 4) (fun _ => vars + vars ^ 2) (fun _ => 4) (fun n => n + 2 * vars))
      (QESAT_poly_LPCP (vars := vars))
  rw [QESAT.soundness_before_repetition] at hConverted
  rcases hConverted with ⟨V₀, t, hV₀⟩
  let V : PCPVerifier (List (CMvPolynomial vars (ZMod 2))) (QESAT.size)
      (ZMod 2) (fun n => 2 ^ n) := fun x =>
    if hlen : 2 ^ (vars + vars ^ 2) ≤ 2 ^ (QESAT.size x) then
      simulateQ (PCP.padImpl (ZMod 2) hlen) (V₀ x)
    else pure true
  refine ⟨V, t, fun x => ?_⟩
  rcases hV₀ x with ⟨_, hQuery, hComplete, hSound⟩
  refine ⟨by simp [RunsInTime], ?_, ?_, ?_⟩
  · by_cases hlen : 2 ^ (vars + vars ^ 2) ≤ 2 ^ (QESAT.size x)
    · simp only [V, hlen, ↓reduceDIte]
      simpa [q', r', c, Polynomial.eval_add, Polynomial.eval_mul] using
        PCP.queryBound_simulateQ_padImpl hlen hQuery
    · simp [V, hlen, QueryBound]
  · intro hxL
    by_cases hlen : 2 ^ (vars + vars ^ 2) ≤ 2 ^ (QESAT.size x)
    · rcases hComplete hxL with ⟨π₀, hπ₀⟩
      let π₁ : Fin (2 ^ QESAT.size x) → ZMod 2 := fun j =>
        if hj : j.val < 2 ^ (vars + vars ^ 2) then π₀ ⟨j.val, hj⟩ else default
      refine ⟨π₁, ?_⟩
      have hπ : ∀ i, π₁ (Fin.castLE hlen i) = π₀ i := by
        intro i
        simp [π₁]
      simp only [V, hlen, ↓reduceDIte]
      rw [PCP.simulateQ_padImpl_eq hlen (V₀ x) π₀ π₁ hπ]
      exact hπ₀
    · refine ⟨fun _ => default, ?_⟩
      simp [V, hlen]
  · intro hxNot π₁
    by_cases hlen : 2 ^ (vars + vars ^ 2) ≤ 2 ^ (QESAT.size x)
    · let π₀ : Fin (2 ^ (vars + vars ^ 2)) → ZMod 2 := fun i => π₁ (Fin.castLE hlen i)
      have hπ : ∀ i, π₁ (Fin.castLE hlen i) = π₀ i := by
        intro i
        rfl
      simp only [V, hlen, ↓reduceDIte]
      rw [PCP.simulateQ_padImpl_eq hlen (V₀ x) π₀ π₁ hπ]
      exact hSound hxNot π₀
    · exfalso
      exact hxNot (QESAT.mem_of_length_eq_zero x (QESAT.length_eq_zero_of_not_pow_le x hlen))

theorem QESAT_exp_PCP {vars : ℕ} : ∃ (q : ℕ) (r : Polynomial ℕ),
    QESAT (ZMod 2) vars ∈
      PCP (QESAT.size) 0 (1 / 2) (ZMod 2)
        (fun n => 2 ^ n) (fun _ => q) r.eval := by
  rcases QESAT_exp_PCP_before_repetition (vars := vars) with ⟨q₀, r₀, hBefore⟩
  rcases hBefore with ⟨V₀, t, hV₀⟩
  let V : PCPVerifier (List (CMvPolynomial vars (ZMod 2))) (QESAT.size)
      (ZMod 2) (fun n => 2 ^ n) := fun x => do
    let xs ← OracleComp.replicate 6 (V₀ x)
    pure (xs.all id)
  refine ⟨6 * q₀, Polynomial.C 6 * r₀, V, t, fun x => ?_⟩
  rcases hV₀ x with ⟨_, hQuery, hComplete, hSound⟩
  refine ⟨by simp [RunsInTime], ?_, ?_, ?_⟩
  · simpa [V, Polynomial.eval_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      queryBound_map (fun xs : List Bool => xs.all id) (queryBound_replicate 6 hQuery)
  · intro hxL
    rcases hComplete hxL with ⟨π, hπ⟩
    refine ⟨π, ?_⟩
    simp only [V, simulateQ_bind, simulateQ_pure]
    rw [simulateQ_replicate]
    simpa using repeated_accept_ge_one (n := 6) (by simpa using hπ)
  · intro hxNot π
    have hBase := hSound hxNot π
    simp only [V, simulateQ_bind, simulateQ_pure]
    rw [simulateQ_replicate]
    exact (repeated_accept_le (n := 6) hBase).trans seven_eighths_pow_six_le_half
