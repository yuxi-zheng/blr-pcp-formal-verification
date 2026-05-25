import Architect
import BlrPcp.QESATExpSizePCP.PCPs
import BlrPcp.QESATExpSizePCP.TensorEq
import BlrPcp.QESATExpSizePCP.LPCPtoExpSizePCP
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

/-- The language of satisfiable quadratic equation systems over `F`. -/
abbrev QESAT (F : Type) [Field F] (n : ℕ) : Set (List (CMvPolynomial n F)) :=
  fun polys => (∀ p ∈ polys, p.totalDegree ≤ 2) ∧
    ∃ (a : Fin n → F), ∀ p ∈ polys, CMvPolynomial.eval a p = 0

/- Sanity check for a small satisfiable QESAT instance. -/
example : QESAT (ZMod 2) 3 [X 0 + C 1, X 0 * X 1 + X 2] := by native_decide

namespace QESAT

/-- A coarse encoding size for one stored monomial.
We charge for the ambient number of variables, for the total exponent mass, and for the
coefficient/term overhead. This makes high-degree or large-support polynomials visible to
`QESAT.size`, even before the verifier rejects them as non-quadratic. -/
private def monomialEncodingSize {n : ℕ} (m : CMvMonomial n) : ℕ :=
  n + m.totalDegree + 1

/-- A coarse encoding size for one computable multivariate polynomial.
The `Lawful.monomials` list is the actual stored support of the polynomial, so this term
accounts for the representation that the verifier inspects when checking degrees and
extracting coefficients. -/
private def polynomialEncodingSize {n : ℕ} (p : CMvPolynomial n F) : ℕ :=
  1 + ((Lawful.monomials p).map monomialEncodingSize).sum

/-- Size proxy for a QESAT instance.
The first summand is the dense quadratic size used by the proof-dimension bookkeeping.
The second summand charges the actual stored polynomial representation, so pathological
inputs with huge support or high-degree monomials are not assigned artificially small size. -/
def size {n : ℕ} (polys : List (CMvPolynomial n F)) :
    ℕ :=
  polys.length * (n + 1)^2 + (polys.map polynomialEncodingSize).sum

/-- Convert a computable polynomial over `ZMod 2` to the corresponding mathlib polynomial. -/
private abbrev mvPoly {n : ℕ} (p : CMvPolynomial n (ZMod 2)) :
    MvPolynomial (Fin n) (ZMod 2) :=
  fromCMvPolynomial p

/-- Coefficient lookup in the mathlib polynomial corresponding to `p`. -/
private abbrev mvCoeff {n : ℕ} (p : CMvPolynomial n (ZMod 2)) (m : Fin n →₀ ℕ) :
    ZMod 2 :=
  MvPolynomial.coeff m (mvPoly p)

/-- Coefficient lookup in the computable polynomial using a finsupp monomial. -/
private def cmvCoeff {n : ℕ} (p : CMvPolynomial n (ZMod 2)) (m : Fin n →₀ ℕ) :
    ZMod 2 :=
  CMvPolynomial.coeff (CMvMonomial.ofFinsupp m) p

/-- The computable monomial `x_i^e`. -/
private def singleMonomial {n : ℕ} (i : Fin n) (e : ℕ) : CMvMonomial n :=
  Vector.ofFn fun j => if j = i then e else 0

/-- The computable monomial `x_i * x_j`, with `i = j` allowed. -/
private def pairMonomial {n : ℕ} (i j : Fin n) : CMvMonomial n :=
  Vector.ofFn fun k => (if k = i then 1 else 0) + if k = j then 1 else 0

/-- Test whether all nonzero coordinates of a monomial lie in a chosen set. -/
private def monomialSupportedOnly {n : ℕ} (m : CMvMonomial n) (keep : Fin n → Bool) :
    Bool :=
  (List.finRange n).all fun i => keep i || m.get i == 0

/-- Fast executable linear-query encoding for degree-at-most-two monomials. -/
private def monomialQueryFast {n : ℕ} (m : CMvMonomial n) :
    Fin (n + n * n) → ZMod 2 :=
  fun k =>
    if hk : k.val < n then
      let i : Fin n := ⟨k.val, hk⟩
      if (m.get i == 1) && monomialSupportedOnly m (fun l => l == i) then
        1
      else
        0
    else
      let q : Fin (n * n) := ⟨k.val - n, by have := k.isLt; omega⟩
      let ij := finProdFinEquiv.symm q
      let i := ij.1
      let j := ij.2
      if i = j then
        if (m.get i == 2) && monomialSupportedOnly m (fun l => l == i) then
          1
        else
          0
      else if decide (i.val < j.val) && (m.get i == 1) && (m.get j == 1) &&
          monomialSupportedOnly m (fun l => (l == i) || (l == j)) then
        1
      else
        0

/-- `singleMonomial` agrees with the corresponding finsupp singleton. -/
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

/-- `pairMonomial` agrees with the sum of two finsupp singletons. -/
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

/-- Equality of computable monomials obtained from finsupps is equality of the finsupps. -/
@[simp]
private lemma ofFinsupp_eq_iff {n : ℕ} {m₁ m₂ : Fin n →₀ ℕ} :
    CMvMonomial.ofFinsupp m₁ = CMvMonomial.ofFinsupp m₂ ↔ m₁ = m₂ := by
  constructor
  · exact fun h => CMvMonomial.injective_ofFinsupp h
  · intro h
    rw [h]

/-- Linear query representing a degree-at-most-two monomial against `(a, a ⊗ a)`. -/
@[implemented_by monomialQueryFast]
private def monomialQuery {n : ℕ} (m : CMvMonomial n) :
    Fin (n + n * n) → ZMod 2 :=
  Fin.append (fun i => if m = singleMonomial i 1 then 1 else 0) fun k =>
    let ij := finProdFinEquiv.symm k
    if m = singleMonomial ij.1 2 then
      if ij.1 = ij.2 then 1 else 0
    else if m = pairMonomial ij.1 ij.2 then
      if ij.1.val < ij.2.val then 1 else 0
    else
      0

/-- Linear coefficients of a quadratic polynomial in the proof vector `(a, a ⊗ a)`. -/
private def linearCoeff {n : ℕ} (p : CMvPolynomial n (ZMod 2)) :
    Fin (n + n * n) → ZMod 2 :=
  fun k => ∑ m ∈ p.support.erase 0,
    cmvCoeff p m * monomialQuery (CMvMonomial.ofFinsupp m) k

/-- Constant coefficient of a computable polynomial over `ZMod 2`. -/
private def constantCoeff {n : ℕ} (p : CMvPolynomial n (ZMod 2)) : ZMod 2 :=
  cmvCoeff p 0

/-- Matrix encoding the nonconstant parts of all QESAT equations as linear constraints. -/
private def linearMatrix {n : ℕ} (polys : List (CMvPolynomial n (ZMod 2))) :
    Matrix (Fin polys.length) (Fin (n + n * n)) (ZMod 2) :=
  fun i => linearCoeff (polys.get i)

/-- Right-hand side for the linearized QESAT constraints. -/
private def linearTarget {n : ℕ} (polys : List (CMvPolynomial n (ZMod 2))) :
    Fin polys.length → ZMod 2 :=
  fun i => -constantCoeff (polys.get i)

/-- LPCP verifier for QESAT: check linearized equations and tensor consistency. -/
def verifier {n : ℕ} :
    LPCPVerifier (List (CMvPolynomial n (ZMod 2))) size (ZMod 2) (fun _ => n + n * n) :=
  fun polys =>
    if ∀ p ∈ polys, p.totalDegree ≤ 2 then do
      let hLine ← LINEQ.verifier (F := ZMod 2)
        (linearMatrix polys, linearTarget polys)
      let hTensor ← TENSORQ.selfVerifier (F := ZMod 2) (n := n)
      pure (hLine && hTensor)
    else
      pure false

/-- In `ZMod 2`, every element is idempotent under multiplication. -/
private lemma zmod2_mul_self (x : ZMod 2) : x * x = x := by
  fin_cases x <;> norm_num

/-- A degree-one singleton finsupp cannot equal a degree-two singleton. -/
private lemma finsupp_single_one_ne_single_two {n : ℕ} (i j : Fin n) :
    Finsupp.single i 1 ≠ Finsupp.single j 2 := by
  intro h
  have := congrArg (fun m : Fin n →₀ ℕ => m.sum fun _ e => e) h
  norm_num at this

/-- A degree-two singleton finsupp cannot equal a degree-one singleton. -/
private lemma finsupp_single_two_ne_single_one {n : ℕ} (i j : Fin n) :
    Finsupp.single i 2 ≠ Finsupp.single j 1 :=
  fun h => finsupp_single_one_ne_single_two j i h.symm

/-- A degree-one singleton cannot equal a product-pair finsupp. -/
private lemma finsupp_single_one_ne_pair {n : ℕ} (i j k : Fin n) :
    Finsupp.single i 1 ≠ Finsupp.single j 1 + Finsupp.single k 1 := by
  intro h
  have := congrArg (fun m : Fin n →₀ ℕ => m.sum fun _ e => e) h
  have hpair :
      (Finsupp.single j 1 + Finsupp.single k 1).sum (fun _ e => e) = 2 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp
  simp [hpair] at this

/-- A degree-two singleton cannot equal a product pair when the left index differs. -/
private lemma finsupp_single_two_ne_pair_of_left_ne {n : ℕ} {i j k : Fin n}
    (hji : j ≠ i) :
    Finsupp.single i 2 ≠ Finsupp.single j 1 + Finsupp.single k 1 := by
  intro h
  have hj := congrFun (congrArg DFunLike.coe h) j
  by_cases hkj : k = j
  · subst k
    simp [hji] at hj
  · simp [hji, hkj] at hj

/-- A product pair with distinct indices cannot equal a degree-two singleton. -/
private lemma finsupp_pair_ne_single_two_of_ne {n : ℕ} {i j k : Fin n}
    (hij : i ≠ j) :
    Finsupp.single i 1 + Finsupp.single j 1 ≠ Finsupp.single k 2 := by
  intro h
  have hi := congrFun (congrArg DFunLike.coe h) i
  by_cases hki : k = i
  · subst k
    simp [hij] at hi
  · simp [hki, hij] at hi

/-- Ordered product-pair finsupps are equal only when both ordered coordinates match. -/
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

/-- Classification of finsupp monomials of total degree at most two. -/
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

/-- The honest tensor proof answers the query for a degree-one monomial. -/
private lemma dotProduct_monomialQuery_single_one {n : ℕ} (a : Fin n → ZMod 2)
    (i : Fin n) :
    TENSORQ.honestProof (a, fun p : Fin n × Fin n => a p.1 * a p.2) ⬝ᵥ
        monomialQuery (CMvMonomial.ofFinsupp (Finsupp.single i 1)) =
      a i := by
  simp only [dotProduct, monomialQuery, TENSORQ.honestProof]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have hfirst : ∑ x : Fin n,
      a x * (if CMvMonomial.ofFinsupp (Finsupp.single i 1) = singleMonomial x 1
        then 1 else 0) = a i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hsing : Finsupp.single i 1 ≠ Finsupp.single j 1 := by
        intro h
        rcases (Finsupp.single_eq_single_iff i j 1 1).mp h with hij | hzero
        · exact hji hij.1.symm
        · norm_num at hzero
      simp [hsing]
    · intro hmem
      simp at hmem
  have hsecond :
      (∑ x : Fin (n * n),
        a (finProdFinEquiv.symm x).1 * a (finProdFinEquiv.symm x).2 *
          (let ij := finProdFinEquiv.symm x
           if CMvMonomial.ofFinsupp (Finsupp.single i 1) = singleMonomial ij.1 2 then
             if ij.1 = ij.2 then 1 else 0
           else if CMvMonomial.ofFinsupp (Finsupp.single i 1) = pairMonomial ij.1 ij.2 then
             if ij.1.val < ij.2.val then 1 else 0
           else 0)) = 0 := by
    rw [← finProdFinEquiv.sum_comp]
    simp only [Equiv.symm_apply_apply]
    apply Finset.sum_eq_zero
    rintro ⟨j, k⟩ _
    simp [finsupp_single_one_ne_single_two, finsupp_single_one_ne_pair]
  rw [hfirst, hsecond, add_zero]

/-- The honest tensor proof answers the query for a squared monomial over `ZMod 2`. -/
private lemma dotProduct_monomialQuery_single_two {n : ℕ} (a : Fin n → ZMod 2)
    (i : Fin n) :
    TENSORQ.honestProof (a, fun p : Fin n × Fin n => a p.1 * a p.2) ⬝ᵥ
        monomialQuery (CMvMonomial.ofFinsupp (Finsupp.single i 2)) =
      a i := by
  simp only [dotProduct, monomialQuery, TENSORQ.honestProof]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have hfirst :
      (∑ x : Fin n,
        a x * (if CMvMonomial.ofFinsupp (Finsupp.single i 2) = singleMonomial x 1
          then 1 else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    simp [finsupp_single_two_ne_single_one]
  rw [hfirst, zero_add]
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
    · have hsing : Finsupp.single i 2 ≠ Finsupp.single j 2 := by
        intro h
        rcases (Finsupp.single_eq_single_iff i j 2 2).mp h with hij | hzero
        · exact hji hij.1.symm
        · norm_num at hzero
      have hpair := finsupp_single_two_ne_pair_of_left_ne (i := i) (j := j) (k := k) hji
      simp [hsing, hpair]
  · intro hmem
    simp at hmem

/-- The honest tensor proof answers the query for a distinct product monomial. -/
private lemma dotProduct_monomialQuery_pair {n : ℕ} (a : Fin n → ZMod 2)
    {i j : Fin n} (hij : i.val < j.val) :
    TENSORQ.honestProof (a, fun p : Fin n × Fin n => a p.1 * a p.2) ⬝ᵥ
        monomialQuery (CMvMonomial.ofFinsupp
          (Finsupp.single i 1 + Finsupp.single j 1)) =
      a i * a j := by
  simp only [dotProduct, monomialQuery, TENSORQ.honestProof]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have hfirst :
      (∑ x : Fin n,
        a x * (if
          CMvMonomial.ofFinsupp (Finsupp.single i 1 + Finsupp.single j 1) =
            singleMonomial x 1 then 1 else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    have hpair_ne_one :
        Finsupp.single i 1 + Finsupp.single j 1 ≠ Finsupp.single x 1 :=
      fun h => finsupp_single_one_ne_pair x i j h.symm
    simp [hpair_ne_one]
  rw [hfirst, zero_add]
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
      · simp [hpair_ne_two, hp]
    · simp [hpair_ne_two, huv]
  · intro hmem
    simp at hmem

/-- Evaluate a monomial query against the honest tensor proof. -/
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

/-- Expanding `linearCoeff` as the sum of monomial-query responses. -/
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

/-- Linearization correctness: the honest tensor proof evaluates a quadratic polynomial. -/
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

/-- The number of equations is bounded by the QESAT size proxy. -/
private lemma length_le_size {n : ℕ} (polys : List (CMvPolynomial n (ZMod 2))) :
    polys.length ≤ QESAT.size polys := by
  unfold QESAT.size
  have hbase : polys.length ≤ polys.length * (n + 1) ^ 2 :=
    Nat.le_mul_of_pos_right _ (by positivity : 0 < (n + 1) ^ 2)
  omega

/-- The QESAT verifier uses at most `size + 2n` randomness queries and four proof queries. -/
private lemma verifier_queryBound {n : ℕ} (polys : List (CMvPolynomial n (ZMod 2))) :
    QueryBound (verifier polys) (QESAT.size polys + 2 * n) 4 := by
  by_cases hdeg : ∀ p ∈ polys, p.totalDegree ≤ 2
  · have hqb :
        QueryBound
          (do
            let hLine ← LINEQ.verifier (F := ZMod 2)
              (linearMatrix polys, linearTarget polys)
            let hTensor ← TENSORQ.selfVerifier (F := ZMod 2) (n := n)
            pure (hLine && hTensor)) (polys.length + 2 * n) 4 := by
      simpa [Nat.add_assoc] using
        queryBound_bind
          (LINEQ.verifier_queryBound (F := ZMod 2)
            (linearMatrix polys, linearTarget polys))
          (fun hLine =>
            queryBound_bind (TENSORQ.selfVerifier_queryBound (F := ZMod 2) (n := n)) fun hTensor => by
              show QueryBound
                (pure (hLine && hTensor) :
                  OracleComp (LPCP.fullSpec (ZMod 2) (n + n * n)) Bool) 0 0
              simp [QueryBound])
    dsimp [verifier]
    rw [if_pos hdeg]
    exact queryBound_mono hqb (by rfl) (Nat.add_le_add_right (length_le_size polys) (2 * n))
  · dsimp [verifier]
    rw [if_neg hdeg]
    simp [QueryBound]

/-- A satisfying QESAT assignment gives a satisfying LINEQ proof for the linearized system. -/
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

/-- Rebuilding a tensor honest proof from the two projections recovers the original proof vector. -/
private lemma tensor_honestProof_proj {n : ℕ}
    (π : Fin (n + n * n) → ZMod 2) :
    TENSORQ.honestProof (TENSORQ.projA π, TENSORQ.projB π) = π := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp [TENSORQ.honestProof, TENSORQ.projA]
  · simp only [TENSORQ.honestProof, TENSORQ.projB, Fin.append_right]
    rw [Equiv.apply_symm_apply]

/-- Tensor consistency plus satisfaction of the linearized system implies QESAT membership. -/
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

/-- Soundness of the LINEQ subcheck when the linearized system is violated. -/
private lemma lineSubcheck_soundness {n : ℕ} (polys : List (CMvPolynomial n (ZMod 2)))
    (π : Fin (n + n * n) → ZMod 2)
    (hd : (linearMatrix polys) *ᵥ π - linearTarget polys ≠ 0) :
    Pr[= true | simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl)
      (LINEQ.verifier (F := ZMod 2) (linearMatrix polys, linearTarget polys))] ≤
        1 / (Fintype.card (ZMod 2) : ENNReal) := by
  simp [LINEQ.verifier]
  rw [← probEvent_eq_eq_probOutput]
  rw [probEvent_map]
  let accept : (Fin polys.length → ZMod 2) → Prop := fun r =>
    decide (π ⬝ᵥ (linearMatrix polys)ᵀ *ᵥ r = linearTarget polys ⬝ᵥ r) = true
  rw [OracleUtil.simulateQ_sampleVector (F := ZMod 2) polys.length (n + n * n)
    (LPCP.proofOracle π).impl]
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

/-- Soundness of the tensor self-check specialized to `ZMod 2`. -/
private lemma tensorSelfCheck_soundness {n : ℕ}
    (π : Fin (n + n * n) → ZMod 2)
    (hπ : (TENSORQ.projA π, TENSORQ.projB π) ∉ TENSORQ (ZMod 2) n) :
    Pr[= true | simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl)
      (TENSORQ.selfVerifier (F := ZMod 2) (n := n))] ≤ 3 / 4 := by
  have h := TENSORQ.selfVerifier_soundness_after_sampling (F := ZMod 2) π hπ
  have hcard :
      (2 * (Fintype.card (ZMod 2) : ENNReal) - 1)
          / (Fintype.card (ZMod 2) : ENNReal) ^ 2 = 3 / 4 := by
    rw [show Fintype.card (ZMod 2) = 2 from ZMod.card 2]
    norm_num [ENNReal.div_eq_inv_mul]
    rw [show (4 : ENNReal) - 1 = 3 by
      exact ENNReal.sub_eq_of_eq_add (by simp : (1 : ENNReal) ≠ ⊤) (by norm_num)]
  rw [hcard] at h
  exact h

/-- Correctness of the QESAT LPCP verifier before conversion to an ordinary PCP. -/
theorem verifier_correct {vars : ℕ} :
    ∀ polys : List (CMvPolynomial vars (ZMod 2)),
      RunsInTime (verifier (n := vars) polys) 0 ∧
      QueryBound (verifier (n := vars) polys) (size polys + 2 * vars) 4 ∧
      (polys ∈ QESAT (ZMod 2) vars → ∃ π : Fin (vars + vars * vars) → ZMod 2,
        Pr[= true | simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl)
          (verifier (n := vars) polys)] ≥ 1 - (0 : ℝ≥0∞)) ∧
      (polys ∉ QESAT (ZMod 2) vars → ∀ π : Fin (vars + vars * vars) → ZMod 2,
        Pr[= true | simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl)
          (verifier (n := vars) polys)] ≤ (3 / 4 : ℝ≥0∞)) := by
  intro polys
  refine ⟨by simp [RunsInTime], ?_, ?_, ?_⟩
  · exact verifier_queryBound (n := vars) polys
  · rintro ⟨hdeg, a, ha⟩
    refine ⟨TENSORQ.honestProof (a, fun q : Fin vars × Fin vars => a q.1 * a q.2), ?_⟩
    have hlin :
        (linearMatrix polys) *ᵥ
            TENSORQ.honestProof (a, fun q : Fin vars × Fin vars => a q.1 * a q.2) =
          linearTarget polys :=
      linearMatrix_mul_honestProof hdeg ha
    have hline_r (r : Fin polys.length → ZMod 2) :
        TENSORQ.honestProof (a, fun q : Fin vars × Fin vars => a q.1 * a q.2) ⬝ᵥ
            (linearMatrix polys)ᵀ *ᵥ r =
          linearTarget polys ⬝ᵥ r :=
      LINEQ.dotProduct_transpose_mulVec_eq (F := ZMod 2) (linearMatrix polys)
        (TENSORQ.honestProof (a, fun q : Fin vars × Fin vars => a q.1 * a q.2))
        (linearTarget polys) r hlin
    simp [verifier, LINEQ.verifier, OracleUtil.sampleVector, OracleUtil.sampleRandomVector, hline_r,
      TENSORQ.selfVerifier, TENSORQ.dotProduct_queryA, TENSORQ.dotProduct_queryB,
      TENSORQ.projA_honestProof, TENSORQ.projB_honestProof,
      TENSORQ.tensor_check_complete]
    rw [if_pos hdeg]
  · intro hx π
    by_cases hdeg : ∀ p ∈ polys, p.totalDegree ≤ 2
    · let impl := (randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl
      let line := LINEQ.verifier (F := ZMod 2) (linearMatrix polys, linearTarget polys)
      let tensor := TENSORQ.selfVerifier (F := ZMod 2) (n := vars)
      by_cases htensor : (TENSORQ.projA π, TENSORQ.projB π) ∈ TENSORQ (ZMod 2) vars
      · have hd :
            (linearMatrix polys) *ᵥ π - linearTarget polys ≠ 0 := by
          intro hzero
          exact hx (mem_of_tensor_linear hdeg htensor (sub_eq_zero.mp hzero))
        have hline := lineSubcheck_soundness (n := vars) polys π hd
        have hmain_le_line :
            Pr[= true | simulateQ impl (verifier (n := vars) polys)] ≤
              Pr[= true | simulateQ impl line] := by
          dsimp [verifier, impl]
          rw [if_pos hdeg]
          change
            Pr[= true | simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl)
              (do
                let hLine ← line
                let hTensor ← tensor
                pure (hLine && hTensor))] ≤
            Pr[= true | simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) line]
          simp only [simulateQ_bind, simulateQ_pure]
          have hle :
              Pr[= true | do
                let hLine ← simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) line
                let hTensor ← simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) tensor
                pure (hLine && hTensor)] ≤
              Pr[= true | do
                let hLine ← simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) line
                pure hLine] := by
            refine probOutput_bind_mono
              (mx := simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) line)
              (my := fun hLine => do
                let hTensor ← simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) tensor
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
      · have htensor_bound := tensorSelfCheck_soundness (n := vars) π htensor
        have hmain_le_tensor :
            Pr[= true | simulateQ impl (verifier (n := vars) polys)] ≤
              Pr[= true | simulateQ impl tensor] := by
          dsimp [verifier, impl]
          rw [if_pos hdeg]
          change
            Pr[= true | simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl)
              (do
                let hLine ← line
                let hTensor ← tensor
                pure (hLine && hTensor))] ≤
            Pr[= true | simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) tensor]
          simp only [simulateQ_bind, simulateQ_pure]
          rw [probOutput_bind_bind_swap
            (mx := simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) line)
            (my := simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) tensor)
            (f := fun hLine hTensor => (pure (hLine && hTensor) : ProbComp Bool))
            (z := true)]
          have hle :
              Pr[= true | do
                let hTensor ← simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) tensor
                let hLine ← simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) line
                pure (hLine && hTensor)] ≤
              Pr[= true | do
                let hTensor ← simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) tensor
                pure hTensor] := by
            refine probOutput_bind_mono
              (mx := simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) tensor)
              (my := fun hTensor => do
                let hLine ← simulateQ ((randOracle (ZMod 2)).impl + (LPCP.proofOracle π).impl) line
                pure (hLine && hTensor))
              (oc := fun hTensor => (pure hTensor : ProbComp Bool))
              (y := true) (z := true) ?_
            intro hTensor _
            cases hTensor <;> simp
          simpa using hle
        exact hmain_le_tensor.trans htensor_bound
    · dsimp [verifier]
      rw [if_neg hdeg]
      simp

/-- If the fixed proof length exceeds the instance size, then the equation list is empty. -/
private lemma length_eq_zero_of_not_size_le {vars : ℕ}
    (x : List (CMvPolynomial vars (ZMod 2)))
    (hlen : ¬vars + vars ^ 2 ≤ QESAT.size x) :
    x.length = 0 := by
  by_contra hx
  have hpos : 0 < x.length := Nat.pos_of_ne_zero hx
  apply hlen
  unfold QESAT.size
  have hbase : vars + vars ^ 2 ≤ x.length * (vars + 1) ^ 2 := by
    nlinarith [sq_nonneg (vars : ℤ), hpos]
  omega

/-- The empty list of equations is trivially satisfiable. -/
private lemma mem_of_length_eq_zero {vars : ℕ} (x : List (CMvPolynomial vars (ZMod 2)))
    (hx : x.length = 0) :
    x ∈ QESAT (ZMod 2) vars := by
  have hxnil : x = [] := List.eq_nil_of_length_eq_zero hx
  subst hxnil
  constructor
  · simp
  · exact ⟨fun _ => 0, by simp⟩

/-- The soundness maximum produced by LPCP-to-PCP conversion simplifies to `7 / 8`. -/
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


end QESAT

namespace PCP

/-- Embed a smaller proof oracle into a larger proof oracle by padding unused entries. -/
private def padImpl (F : Type) {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) :
    QueryImpl (PCP.fullSpec F n₀) (OracleComp (PCP.fullSpec F n₁))
  | .inl () => query (spec := PCP.fullSpec F n₁) (.inl ())
  | .inr i => query (spec := PCP.fullSpec F n₁) (.inr (Fin.castLE h i))

/-- Simulating through `padImpl` preserves query bounds. -/
private lemma queryBound_simulateQ_padImpl {F : Type} {n₀ n₁ : ℕ} (h : n₀ ≤ n₁)
    {α : Type} {oa : OracleComp (PCP.fullSpec F n₀) α} {q r : ℕ}
    (hoa : QueryBound oa r q) :
    QueryBound (simulateQ (padImpl F h) oa) r q := by
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

/-- A padded proof oracle simulates the original oracle when the padded proof extends it. -/
private lemma simulateQ_padImpl_eq {F : Type} [SampleableType F] {n₀ n₁ : ℕ}
    (h : n₀ ≤ n₁) {α : Type} (oa : OracleComp (PCP.fullSpec F n₀) α)
    (π₀ : Fin n₀ → F) (π₁ : Fin n₁ → F)
    (hπ : ∀ i, π₁ (Fin.castLE h i) = π₀ i) :
    simulateQ ((randOracle F).impl + (PCP.proofOracle π₁).impl) (simulateQ (padImpl F h) oa) =
      simulateQ ((randOracle F).impl + (PCP.proofOracle π₀).impl) oa := by
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

/-- Mapping the output of an oracle computation preserves its query bounds. -/
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

/-- Repeating a bounded oracle computation scales both query bounds linearly. -/
private lemma queryBound_replicate {ρ ι α : Type} {randSpec : OracleSpec ρ}
    {proofSpec : OracleSpec ι} {oa : OracleComp (randSpec + proofSpec) α}
    {q r : ℕ} (n : ℕ) (hoa : QueryBound oa r q) :
    QueryBound (OracleComp.replicate n oa) (n * r) (n * q) := by
  induction n with
  | zero =>
      simp [OracleComp.replicate, QueryBound]
  | succ n ih =>
      rw [OracleComp.replicate_succ_bind]
      simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        queryBound_bind hoa fun x => queryBound_map (List.cons x) ih

/-- Simulation commutes with repeated independent runs of the same oracle computation. -/
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

/-- Acceptance probability of accepting all repeated Boolean runs. -/
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

/-- Repetition by conjunction raises an upper acceptance bound to a power. -/
private lemma repeated_accept_le {mx : ProbComp Bool} {ε : ℝ≥0∞} {n : ℕ}
    (hmx : Pr[= true | mx] ≤ ε) :
    Pr[= true | do
      let xs ← OracleComp.replicate n mx
      pure (xs.all id)] ≤ ε ^ n := by
  rw [probOutput_true_all_replicate]
  exact pow_le_pow_left₀ (by simp) hmx n

/-- Repetition preserves perfect completeness. -/
private lemma repeated_accept_ge_one {mx : ProbComp Bool} {n : ℕ}
    (hmx : Pr[= true | mx] ≥ 1) :
    Pr[= true | do
      let xs ← OracleComp.replicate n mx
      pure (xs.all id)] ≥ 1 := by
  rw [probOutput_true_all_replicate]
  exact one_le_pow₀ hmx

/-- Six repetitions reduce soundness `7 / 8` to at most `1 / 2`. -/
private lemma seven_eighths_pow_six_le_half : ((7 / 8 : ℝ≥0∞) ^ 6) ≤ 1 / 2 := by
  refine (ENNReal.toReal_le_toReal ?_ ?_).mp ?_
  · simp [ENNReal.div_ne_top]
  · exact ENNReal.div_ne_top (by simp) (by norm_num)
  · rw [ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_div]
    norm_num

/-- QESAT over `ZMod 2` has an exponential-length LPCP with soundness `3 / 4`. -/
theorem QESAT_poly_LPCP {vars : ℕ} :
    QESAT (ZMod 2) vars ∈
      LPCP (QESAT.size) 0 (3 / 4) (ZMod 2)
        (fun _ => vars + vars ^ 2) (fun _ => 4) (fun n => n + 2 * vars) := by
  have hpoly :
      QESAT (ZMod 2) vars ∈
        LPCP (QESAT.size) 0 (3 / 4) (ZMod 2)
          (fun _ => vars + vars * vars) (fun _ => 4) (fun n => n + 2 * vars) :=
    ⟨QESAT.verifier (n := vars), 0, QESAT.verifier_correct (vars := vars)⟩
  simpa [sq] using hpoly

/-- QESAT has an exponential-length ordinary PCP before final soundness repetition. -/
theorem QESAT_exp_PCP_before_repetition {vars : ℕ} : ∃ (q : ℕ) (r : Polynomial ℕ),
    QESAT (ZMod 2) vars ∈
      PCP (QESAT.size) 0 (7 / 8) (ZMod 2)
        (fun n => 2 ^ n) (fun _ => q) r.eval := by
  let shift := LPCPToPCP.numShifts (fun _ => 4) 0
  let q' := 3 + 2 * shift * 4
  let c := 2 + shift
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
    if hlen : vars + vars ^ 2 ≤ QESAT.size x then
      have hlenPow : 2 ^ (vars + vars ^ 2) ≤ 2 ^ (QESAT.size x) :=
        Nat.pow_le_pow_right (by norm_num) hlen
      simulateQ (PCP.padImpl (ZMod 2) hlenPow) (V₀ x)
    else pure true
  refine ⟨V, t, fun x => ?_⟩
  rcases hV₀ x with ⟨_, hQuery, hComplete, hSound⟩
  refine ⟨by simp [RunsInTime], ?_, ?_, ?_⟩
  · by_cases hlen : vars + vars ^ 2 ≤ QESAT.size x
    · simp only [V, hlen, ↓reduceDIte]
      let hlenPow : 2 ^ (vars + vars ^ 2) ≤ 2 ^ (QESAT.size x) :=
        Nat.pow_le_pow_right (by norm_num) hlen
      have hshift :
          LPCPToPCP.numShifts (fun _ => 4) (QESAT.size x) = shift := by
        simp [shift, LPCPToPCP.numShifts, LPCPToPCP.logFactor]
      simpa [q', r', c, shift, hshift, Polynomial.eval_add, Polynomial.eval_mul] using
        PCP.queryBound_simulateQ_padImpl hlenPow hQuery
    · simp [V, hlen, QueryBound]
  · intro hxL
    by_cases hlen : vars + vars ^ 2 ≤ QESAT.size x
    · rcases hComplete hxL with ⟨π₀, hπ₀⟩
      let hlenPow : 2 ^ (vars + vars ^ 2) ≤ 2 ^ (QESAT.size x) :=
        Nat.pow_le_pow_right (by norm_num) hlen
      let π₁ : Fin (2 ^ QESAT.size x) → ZMod 2 := fun j =>
        if hj : j.val < 2 ^ (vars + vars ^ 2) then π₀ ⟨j.val, hj⟩ else default
      refine ⟨π₁, ?_⟩
      have hπ : ∀ i, π₁ (Fin.castLE hlenPow i) = π₀ i := by
        intro i
        simp [π₁]
      simp only [V, hlen, ↓reduceDIte]
      rw [PCP.simulateQ_padImpl_eq hlenPow (V₀ x) π₀ π₁ hπ]
      exact hπ₀
    · refine ⟨fun _ => default, ?_⟩
      simp [V, hlen]
  · intro hxNot π₁
    by_cases hlen : vars + vars ^ 2 ≤ QESAT.size x
    · let hlenPow : 2 ^ (vars + vars ^ 2) ≤ 2 ^ (QESAT.size x) :=
        Nat.pow_le_pow_right (by norm_num) hlen
      let π₀ : Fin (2 ^ (vars + vars ^ 2)) → ZMod 2 := fun i => π₁ (Fin.castLE hlenPow i)
      have hπ : ∀ i, π₁ (Fin.castLE hlenPow i) = π₀ i := by
        intro i
        rfl
      simp only [V, hlen, ↓reduceDIte]
      rw [PCP.simulateQ_padImpl_eq hlenPow (V₀ x) π₀ π₁ hπ]
      exact hSound hxNot π₀
    · exfalso
      exact hxNot (QESAT.mem_of_length_eq_zero x (QESAT.length_eq_zero_of_not_size_le x hlen))

/-- QESAT has an exponential-length ordinary PCP with soundness `1 / 2`. -/
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
