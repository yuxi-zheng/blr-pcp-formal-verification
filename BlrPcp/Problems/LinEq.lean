import Architect
import BlrPcp.Oracle
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-!
# Linear equations

This file defines the LINEQ language, its executable LPCP verifier, and the
linear PCP theorem for LINEQ.
-/

open OracleComp
open scoped Matrix

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
    [SampleableType F]

abbrev LINEQ (F : Type) (m n : ℕ) [Field F] :
    Set (Matrix (Fin m) (Fin n) F × (Fin m → F)) :=
  { (M, c) | ∃ b, M *ᵥ b = c }

namespace LINEQ

def size {m n : ℕ} (_ : Matrix (Fin m) (Fin n) F × (Fin m → F)) : ℕ :=
  (m * n + m) * Nat.clog 2 (Fintype.card F)

omit [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma dotProduct_transpose_mulVec_eq {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) F) (b : Fin n → F) (c r : Fin m → F)
    (h : M *ᵥ b = c) :
    b ⬝ᵥ (Mᵀ *ᵥ r) = c ⬝ᵥ r := by
  rw [← h, Matrix.mulVec_transpose, dotProduct_comm b (r ᵥ* M),
    ← Matrix.dotProduct_mulVec r M b, dotProduct_comm r (M *ᵥ b)]

omit [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma dotProduct_eq_add_sum_erase {m : ℕ} (a b : Fin m → F) (k : Fin m) :
    a ⬝ᵥ b = a k * b k + ∑ i ∈ (Finset.univ.erase k), a i * b i := by
  rw [dotProduct]
  exact (Finset.add_sum_erase Finset.univ (fun i => a i * b i) (Finset.mem_univ k)).symm

noncomputable def normalizeLinearForm {m : ℕ} (a : Fin m → F) (k : Fin m) :
    (Fin m → F) → (Fin m → F) :=
  fun r i => if i = k then (a ⬝ᵥ r) / a k else r i

noncomputable def normalizeLinearFormInv {m : ℕ} (a : Fin m → F) (k : Fin m) :
    (Fin m → F) → (Fin m → F) :=
  fun r i =>
    if i = k then
      r k - (∑ j ∈ (Finset.univ.erase k), a j * r j) / a k
    else
      r i

omit [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma normalizeLinearForm_left_inv {m : ℕ} {a : Fin m → F} {k : Fin m}
    (hk : a k ≠ 0) :
    Function.LeftInverse (normalizeLinearFormInv (F := F) a k)
      (normalizeLinearForm (F := F) a k) := by
  intro r
  funext i
  by_cases hi : i = k
  · rw [hi]
    have hsum :
        (∑ j ∈ (Finset.univ.erase k),
            a j * normalizeLinearForm (F := F) a k r j) =
          ∑ j ∈ (Finset.univ.erase k), a j * r j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp [normalizeLinearForm, (Finset.mem_erase.mp hj).1]
    simp only [normalizeLinearFormInv]
    rw [hsum]
    simp only [normalizeLinearForm]
    rw [dotProduct_eq_add_sum_erase (a := a) (b := r) (k := k)]
    simp
    field_simp [hk]
    ring_nf
  · simp [normalizeLinearForm, normalizeLinearFormInv, hi]

omit [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma normalizeLinearForm_right_inv {m : ℕ} {a : Fin m → F} {k : Fin m}
    (hk : a k ≠ 0) :
    Function.RightInverse (normalizeLinearFormInv (F := F) a k)
      (normalizeLinearForm (F := F) a k) := by
  intro r
  funext i
  by_cases hi : i = k
  · rw [hi]
    have hsum :
        (∑ j ∈ (Finset.univ.erase k),
            a j * normalizeLinearFormInv (F := F) a k r j) =
          ∑ j ∈ (Finset.univ.erase k), a j * r j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp [normalizeLinearFormInv, (Finset.mem_erase.mp hj).1]
    simp only [normalizeLinearForm]
    rw [dotProduct_eq_add_sum_erase (a := a)
      (b := normalizeLinearFormInv (F := F) a k r) (k := k)]
    rw [hsum]
    simp only [normalizeLinearFormInv]
    simp
    field_simp [hk]
    ring_nf
  · simp [normalizeLinearForm, normalizeLinearFormInv, hi]

omit [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma normalizeLinearForm_bijective {m : ℕ} {a : Fin m → F} {k : Fin m}
    (hk : a k ≠ 0) :
    Function.Bijective (normalizeLinearForm (F := F) a k) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨normalizeLinearFormInv (F := F) a k,
      normalizeLinearForm_left_inv (F := F) hk,
      normalizeLinearForm_right_inv (F := F) hk⟩

omit [Inhabited F] [SampleableType F] in
lemma coordinate_zero_card_div_le {m : ℕ} (k : Fin m) :
    (((Finset.univ.filter fun r : Fin m → F => r k = 0).card : NNReal) /
        (Fintype.card F : NNReal) ^ m) ≤
      1 / (Fintype.card F : NNReal) := by
  have hsz :=
    MvPolynomial.schwartz_zippel_sum_degreeOf
      (R := F) (p := (MvPolynomial.X k : MvPolynomial (Fin m) F))
      (MvPolynomial.X_ne_zero k)
      (fun _ : Fin m => (Finset.univ : Finset F))
  have hsz' :
      (((Finset.univ.filter fun r : Fin m → F => r k = 0).card : ℚ≥0) /
          (Fintype.card F ^ m : ℚ≥0)) ≤
        1 / (Fintype.card F : ℚ≥0) := by
    calc
      (((Finset.univ.filter fun r : Fin m → F => r k = 0).card : ℚ≥0) /
          (Fintype.card F ^ m : ℚ≥0)) ≤
        ∑ i : Fin m, (if i = k then (1 : ℚ≥0) else 0) /
          (Fintype.card F : ℚ≥0) := by
          simpa [MvPolynomial.eval_X, MvPolynomial.degreeOf_X, Fintype.card_piFinset_const]
            using hsz
      _ = 1 / (Fintype.card F : ℚ≥0) := by
        rw [← Finset.sum_div]
        simp
  simpa using (NNRat.cast_mono (K := NNReal) hsz')

lemma uniform_coordinate_zero_prob_mul_card_le_one {m : ℕ} (k : Fin m) :
    Pr[fun r : Fin m → F => r k = 0 |
        ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] *
      (Fintype.card F : ENNReal) ≤ 1 := by
  have hF0 : (Fintype.card F : ENNReal) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := F)).ne'
  have hFtop : (Fintype.card F : ENNReal) ≠ ⊤ := by simp
  have hsz := coordinate_zero_card_div_le (F := F) k
  have hszENN :
      (((Finset.univ.filter fun r : Fin m → F => r k = 0).card : ENNReal) /
          (Fintype.card F : ENNReal) ^ m) ≤
        1 / (Fintype.card F : ENNReal) := by
    have hF0NN : (Fintype.card F : NNReal) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := F)).ne'
    have hpow0NN : (Fintype.card F : NNReal) ^ m ≠ 0 := pow_ne_zero _ hF0NN
    rw [← ENNReal.coe_natCast ((Finset.univ.filter fun r : Fin m → F => r k = 0).card),
      ← ENNReal.coe_natCast (Fintype.card F), ← ENNReal.coe_pow, ← ENNReal.coe_one,
      ← ENNReal.coe_div hpow0NN, ← ENNReal.coe_div hF0NN]
    exact ENNReal.coe_le_coe.mpr hsz
  rw [probEvent_uniformSample]
  rw [Fintype.card_fun, Fintype.card_fin]
  norm_num [Nat.cast_pow]
  calc
    ((Finset.univ.filter fun r : Fin m → F => r k = 0).card : ENNReal) /
          (Fintype.card F : ENNReal) ^ m * (Fintype.card F : ENNReal)
        ≤ (1 / (Fintype.card F : ENNReal)) * (Fintype.card F : ENNReal) := by
          exact mul_le_mul_left hszENN _
    _ = 1 := by
      exact ENNReal.div_mul_cancel hF0 hFtop
    _ ≤ 1 := le_rfl

lemma linear_form_uniform_prob_mul_card_le_one {m : ℕ} {a : Fin m → F}
    (ha : a ≠ 0) :
    Pr[fun r : Fin m → F => a ⬝ᵥ r = 0 |
        ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] *
      (Fintype.card F : ENNReal) ≤ 1 := by
  obtain ⟨k, hk⟩ : ∃ k, a k ≠ 0 := by
    simpa [funext_iff] using ha
  let T : (Fin m → F) → (Fin m → F) := normalizeLinearForm (F := F) a k
  have hprob :
      Pr[fun r : Fin m → F => a ⬝ᵥ r = 0 |
          ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] =
        Pr[fun r : Fin m → F => r k = 0 |
          ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] := by
    calc
      Pr[fun r : Fin m → F => a ⬝ᵥ r = 0 |
          ($ᵗ (Fin m → F) : ProbComp (Fin m → F))]
          = Pr[fun r : Fin m → F => T r k = 0 |
              ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] := by
            apply probEvent_ext
            intro r _hr
            simp [T, normalizeLinearForm, hk]
      _ = Pr[fun r : Fin m → F => r k = 0 |
              T <$> ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] := by
            exact (probEvent_map
              (mx := ($ᵗ (Fin m → F) : ProbComp (Fin m → F)))
              (f := T) (q := fun r : Fin m → F => r k = 0)).symm
      _ = Pr[fun r : Fin m → F => r k = 0 |
              ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] := by
            simp [probEvent_def, evalDist_map_bijective_uniform_cross
                (α := Fin m → F) (β := Fin m → F) T
                (normalizeLinearForm_bijective (F := F) hk)]
  rw [hprob]
  exact uniform_coordinate_zero_prob_mul_card_le_one (F := F) k

def vectorEquiv (F : Type) (m : ℕ) : Vector F m ≃ (Fin m → F) where
  toFun := fun v i => v.get i
  invFun := Vector.ofFn
  left_inv := fun v => by
    ext i
    simp only [Vector.ofFn, Vector.get, Fin.val_cast, Vector.getElem_toArray, Vector.getElem_mk,
      Array.getElem_ofFn]
  right_inv := fun f => by
    funext i
    simp only [Vector.get, Vector.ofFn, Fin.val_cast, Array.getElem_ofFn, Fin.eta]

def sampleRandomVectorAux (F : Type) : (m n : ℕ) →
    OracleComp (LPCP.spec F n) (Vector F m)
  | 0, _ => pure #v[]
  | m + 1, n => Vector.push <$> sampleRandomVectorAux F m n <*>
      query (spec := LPCP.spec F n) (.inl ())

def sampleRandomVector (m n : ℕ) (F : Type) :
    OracleComp (LPCP.spec F n) (Fin m → F) :=
  vectorEquiv F m <$> sampleRandomVectorAux F m n

omit [Field F] [Fintype F] [DecidableEq F] [Inhabited F] in
lemma simulateQ_sampleRandomVectorAux (m n : ℕ)
    (impl : QueryImpl ((Fin n → F) →ₒ F) ProbComp) :
    simulateQ ((rand F).impl + impl) (sampleRandomVectorAux F m n) =
      ($ᵗ Vector F m : ProbComp (Vector F m)) := by
  induction m with
  | zero =>
      rfl
  | succ m ih =>
      simp only [sampleRandomVectorAux, simulateQ_seq, simulateQ_map, simulateQ_query,
        OracleQuery.cont_query, id_map, OracleQuery.input_query]
      change Vector.push <$> simulateQ ((rand F).impl + impl) (sampleRandomVectorAux F m n) <*>
          ($ᵗ F) = (instSampleableTypeVector F (m + 1)).selectElem
      rw [ih]
      rfl

omit [Field F] [Fintype F] [Inhabited F] in
lemma simulateQ_sampleRandomVector (m n : ℕ)
    (impl : QueryImpl ((Fin n → F) →ₒ F) ProbComp) :
    simulateQ ((rand F).impl + impl) (sampleRandomVector m n F) =
      ($ᵗ (Fin m → F) : ProbComp (Fin m → F)) := by
  simp only [sampleRandomVector, simulateQ_map]
  change vectorEquiv F m <$> simulateQ ((rand F).impl + impl) (sampleRandomVectorAux F m n) =
    (instSampleableTypeFinFunc (n := m) (α := F)).selectElem
  rw [simulateQ_sampleRandomVectorAux (F := F) m n impl]
  simp [instSampleableTypeFinFunc, vectorEquiv, SampleableType.ofEquiv, uniformSample]

def verifier {m n : ℕ} :
    LPCPVerifier (Matrix (Fin m) (Fin n) F × (Fin m → F)) size F (fun _ => n) :=
  fun x => do
    let r ← sampleRandomVector m n F
    let u : Fin n → F := x.1ᵀ *ᵥ r
    let y ← query (spec := LPCP.spec F n) (.inr u)
    pure (y = x.2 ⬝ᵥ r)

omit [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma sampleRandomVectorAux_queryBound (m n : ℕ) :
    QueryBound (sampleRandomVectorAux F m n) 0 m := by
  induction m with
  | zero =>
      simp [sampleRandomVectorAux, QueryBound]
  | succ m ih =>
      simpa [sampleRandomVectorAux, seq_eq_bind_map, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using
        queryBound_bind ih fun _ => by
          simp [QueryBound]

omit [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F] in
lemma sampleRandomVector_queryBound (m n : ℕ) :
    QueryBound (sampleRandomVector m n F) 0 m := by
  simpa [sampleRandomVector] using sampleRandomVectorAux_queryBound (F := F) m n

omit [Inhabited F] [SampleableType F] in
lemma verifier_queryBound {m n : ℕ}
    (x : Matrix (Fin m) (Fin n) F × (Fin m → F)) :
    QueryBound (verifier (F := F) x) 1 m := by
  have hQuery : ∀ r : Fin m → F,
      QueryBound
        (do
          let y ←
            (liftM (query (spec := LPCP.spec F n) (.inr (x.1ᵀ *ᵥ r))) :
              OracleComp (LPCP.spec F n) F)
          pure (decide (y = x.2 ⬝ᵥ r))) 1 0 := by
    intro r
    simp only [QueryBound]
    rw [OracleComp.isQueryBound_query_bind_iff]
    exact ⟨by simp, fun _ => trivial⟩
  simpa [verifier] using
    queryBound_bind (sampleRandomVector_queryBound (F := F) m n) hQuery

end LINEQ

theorem LINEQ_LPCP {m n : ℕ} :
    LINEQ m n (F := F) ∈ LPCP (LINEQ.size) 0 (1 / (Fintype.card F)) F
      (fun _ => n) (fun _ => 1) (fun _ => m) := by
  refine ⟨LINEQ.verifier (F := F), 0, ?_⟩
  rintro ⟨M, c⟩
  refine ⟨by simp [RunsInTime],
    LINEQ.verifier_queryBound (F := F) (M, c), ?_, ?_⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, by
      simp [LINEQ.verifier, LINEQ.sampleRandomVector,
        LINEQ.dotProduct_transpose_mulVec_eq, hb]⟩
  · intro hx π
    by_cases hm : m = 0
    · exfalso
      apply hx
      refine ⟨π, ?_⟩
      ext i
      exact Fin.elim0 (hm ▸ i)
    · have hd : M *ᵥ π - c ≠ 0 := fun h => hx ⟨π, sub_eq_zero.mp h⟩
      simp [LINEQ.verifier]
      rw [← probEvent_eq_eq_probOutput]
      rw [probEvent_map]
      let accept : (Fin m → F) → Prop := fun r =>
        decide (π ⬝ᵥ (Mᵀ *ᵥ r) = c ⬝ᵥ r) = true
      rw [LINEQ.simulateQ_sampleRandomVector (F := F) m n (LPCP.proof π).impl]
      change
        Pr[accept | ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] *
          (Fintype.card F : ENNReal) ≤ 1
      rw [show
          Pr[accept |
              ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] =
            Pr[fun r : Fin m → F => (M *ᵥ π - c) ⬝ᵥ r = 0 |
              ($ᵗ (Fin m → F) : ProbComp (Fin m → F))] by
        apply probEvent_ext
        intro r _hr
        dsimp [accept]
        simp [LINEQ.dotProduct_transpose_mulVec_eq (F := F) M π (M *ᵥ π) r rfl,
          sub_eq_zero]]
      exact LINEQ.linear_form_uniform_prob_mul_card_le_one (F := F) hd
