import BlrPcp.FnFiniteFIelds.Linear

open scoped BigOperators

namespace BlrPcp

variable {F Idx : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]

/-- True/False event that the BLR test accepts a function f
when it samples scalars `a`, `b` and points `x`, `y` -/
def BLRAcceptsAt (f : ScalarFn F Idx) (a b : F) (x y : Vec F Idx) : Prop :=
  a * f x + b * f y = f (fun i => a * x i + b * y i)

/-- The uniform acceptance probability of the finite-field BLR test:
`a,b` are sampled uniformly from `F \ {0}` and `x,y` from `F^Idx`. -/
noncomputable def acceptanceProbabilityBLR (f : ScalarFn F Idx) : Real := by
  classical
  exact
    ((nonzeroF (F := F)).card : Real)⁻¹ *
      ((nonzeroF (F := F)).card : Real)⁻¹ *
        (Fintype.card (Vec F Idx) : Real)⁻¹ *
          (Fintype.card (Vec F Idx) : Real)⁻¹ *
            ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
              ∑ x : Vec F Idx, ∑ y : Vec F Idx,
                if BLRAcceptsAt f a b x y then (1 : Real) else 0

section BLRCompleteness

omit [Fintype F] [DecidableEq F] [DecidableEq Idx] [Nonempty Idx] in
/-- A linear function passes the BLR check for every choice of randomness. -/
lemma BLRAcceptsAt_linearFn (α : Vec F Idx) (a b : F) (x y : Vec F Idx) :
    BLRAcceptsAt (linearFn α) a b x y := by
  classical
  simp [BLRAcceptsAt, linearFn, dotProduct, Finset.mul_sum, Finset.sum_add_distrib, mul_add,
    mul_left_comm]

omit [Nonempty Idx] in
/-- Every member of `LinearSet` passes the BLR check pointwise. -/
lemma BLRAcceptsAt_of_mem_linearSet {f : ScalarFn F Idx}
    (hf : f ∈ LinearSet (F := F) (Idx := Idx)) (a b : F) (x y : Vec F Idx) :
    BLRAcceptsAt f a b x y := by
  have hf_linear : IsLinear f := by
    simpa [LinearSet] using hf
  rcases hf_linear with ⟨α, hα⟩
  unfold BLRAcceptsAt
  rw [hα x, hα y, hα (fun i => a * x i + b * y i)]
  exact BLRAcceptsAt_linearFn (F := F) (Idx := Idx) α a b x y


omit [Nonempty Idx] in
/-- Completeness of the finite-field BLR verifier: linear functions are accepted
with probability one. -/
lemma blr_completeness {f : ScalarFn F Idx}
    (hf : f ∈ LinearSet (F := F) (Idx := Idx)) :
    acceptanceProbabilityBLR f = 1 := by
  classical
  have hnz_nonempty : (nonzeroF (F := F)).Nonempty := by
    exact ⟨1, by simp [nonzeroF]⟩
  have hnz_card : ((nonzeroF (F := F)).card : Real) ≠ 0 := by
    exact_mod_cast hnz_nonempty.card_pos.ne'
  have hF_card : (Fintype.card F : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hvec_card_pow : ((Fintype.card F : Real) ^ Fintype.card Idx) ≠ 0 :=
    pow_ne_zero _ hF_card
  simp [acceptanceProbabilityBLR, BLRAcceptsAt_of_mem_linearSet (F := F) (Idx := Idx) hf,
    mul_assoc]
  field_simp [hnz_card, hvec_card_pow]

end BLRCompleteness

section BLRSoundness

private def agreementCount (f : ScalarFn F Idx) (α : Vec F Idx) : ℕ :=
  (Finset.univ.filter fun x : Vec F Idx => f x = linearFn α x).card

omit [Nonempty Idx] in
private lemma sum_agreementCount_eq_sum_dotProduct_fibers (f : ScalarFn F Idx) :
    ∑ α : Vec F Idx, agreementCount f α =
      ∑ x : Vec F Idx,
        (Finset.univ.filter fun α : Vec F Idx => dotProduct α x = f x).card := by
  classical
  unfold agreementCount
  calc
    ∑ α : Vec F Idx, (Finset.univ.filter fun x : Vec F Idx =>
        f x = linearFn α x).card =
      ∑ α : Vec F Idx, ∑ x : Vec F Idx,
        if f x = linearFn α x then (1 : ℕ) else 0 := by
        simp
    _ = ∑ x : Vec F Idx, ∑ α : Vec F Idx,
        if f x = linearFn α x then (1 : ℕ) else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ x : Vec F Idx,
        (Finset.univ.filter fun α : Vec F Idx => dotProduct α x = f x).card := by
        apply Finset.sum_congr rfl
        intro x _
        simp [linearFn, dotProduct, eq_comm]

omit [Nonempty Idx] in
private lemma nonzero_vec_card :
    (Finset.univ.filter fun x : Vec F Idx => x ≠ 0).card =
      Fintype.card (Vec F Idx) - 1 := by
  classical
  have h0 : (0 : Vec F Idx) ∈ (Finset.univ : Finset (Vec F Idx)) := by simp
  change (Finset.univ.filter fun x : Vec F Idx => x ≠ 0).card =
    (Finset.univ : Finset (Vec F Idx)).card - 1
  rw [← Finset.card_erase_of_mem h0]
  congr 1
  ext x
  simp

omit [Nonempty Idx] in
private lemma sum_agreementCount_lower (f : ScalarFn F Idx) :
    (Fintype.card (Vec F Idx) - 1) *
        (Fintype.card (Vec F Idx) / Fintype.card F) ≤
      ∑ α : Vec F Idx, agreementCount f α := by
  classical
  let N := Fintype.card (Vec F Idx)
  let q := Fintype.card F
  let k := N / q
  have hq0 : q ≠ 0 := by
    dsimp [q]
    exact Fintype.card_ne_zero
  have hfiber_ge : ∀ x : Vec F Idx,
      (if x = 0 then 0 else k) ≤
        (Finset.univ.filter fun α : Vec F Idx => dotProduct α x = f x).card := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have hmul :
          ((Finset.univ.filter fun α : Vec F Idx => dotProduct α x = f x).card) *
              Fintype.card F = Fintype.card (Vec F Idx) := by
        simpa [linearFn, dotProduct_comm] using
          linearFn_fiber_card_mul_card (F := F) (Idx := Idx) hx (f x)
      have hfiber :
          (Finset.univ.filter fun α : Vec F Idx => dotProduct α x = f x).card = k := by
        dsimp [k, N, q]
        exact Nat.eq_div_of_mul_eq_right hq0 (by simpa [mul_comm] using hmul)
      simp [hx, hfiber]
  have hsum_nonzero :
      (∑ x : Vec F Idx, if x = 0 then 0 else k) = (N - 1) * k := by
    calc
      (∑ x : Vec F Idx, if x = 0 then 0 else k) =
          ∑ x : Vec F Idx, if x ≠ 0 then k else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = 0 <;> simp [hx]
      _ = ∑ x ∈ (Finset.univ.filter fun x : Vec F Idx => x ≠ 0), k := by
          exact (Finset.sum_filter (s := (Finset.univ : Finset (Vec F Idx)))
            (p := fun x : Vec F Idx => x ≠ 0) (f := fun _ => k)).symm
      _ = (N - 1) * k := by
          simp [N, nonzero_vec_card]
  calc
    (Fintype.card (Vec F Idx) - 1) *
        (Fintype.card (Vec F Idx) / Fintype.card F) =
        (N - 1) * k := rfl
    _ = ∑ x : Vec F Idx, if x = 0 then 0 else k := hsum_nonzero.symm
    _ ≤ ∑ x : Vec F Idx,
        (Finset.univ.filter fun α : Vec F Idx => dotProduct α x = f x).card := by
        exact Finset.sum_le_sum fun x _ => hfiber_ge x
    _ = ∑ α : Vec F Idx, agreementCount f α :=
        (sum_agreementCount_eq_sum_dotProduct_fibers (F := F) (Idx := Idx) f).symm

omit [DecidableEq F] [Nonempty Idx] in
private lemma card_vec_div_card_field_pos [Nonempty Idx] :
    0 < Fintype.card (Vec F Idx) / Fintype.card F := by
  classical
  let q := Fintype.card F
  let m := Fintype.card Idx
  have hq : 1 < q := by
    dsimp [q]
    exact Fintype.one_lt_card
  have hm : 0 < m := by
    dsimp [m]
    exact Fintype.card_pos_iff.mpr inferInstance
  have hcard : Fintype.card (Vec F Idx) = q ^ m := by
    dsimp [q, m]
    simp
  have hdiv : Fintype.card (Vec F Idx) / q = q ^ (m - 1) := by
    calc
      Fintype.card (Vec F Idx) / q = q ^ m / q := by rw [hcard]
      _ = q ^ (m - 1) := by
          rw [← Nat.succ_pred_eq_of_pos hm, pow_succ, Nat.succ_sub_one]
          exact Nat.mul_div_left _ (Nat.zero_lt_of_lt hq)
  rw [hdiv]
  exact pow_pos (Nat.zero_lt_of_lt hq) _

omit [DecidableEq F] [Nonempty Idx] in
private lemma card_vec_div_card_field_lt_card_vec [Nonempty Idx] :
    Fintype.card (Vec F Idx) / Fintype.card F < Fintype.card (Vec F Idx) := by
  classical
  let q := Fintype.card F
  let m := Fintype.card Idx
  have hq : 1 < q := by
    dsimp [q]
    exact Fintype.one_lt_card
  have hm : 0 < m := by
    dsimp [m]
    exact Fintype.card_pos_iff.mpr inferInstance
  have hcard : Fintype.card (Vec F Idx) = q ^ m := by
    dsimp [q, m]
    simp
  have hdiv : q ^ m / q = q ^ (m - 1) := by
    rw [← Nat.succ_pred_eq_of_pos hm, pow_succ, Nat.succ_sub_one]
    exact Nat.mul_div_left _ (Nat.zero_lt_of_lt hq)
  rw [hcard]
  have hqeq : Fintype.card F = q := rfl
  rw [hqeq]
  rw [hdiv]
  exact Nat.pow_lt_pow_right hq (Nat.pred_lt hm.ne')

omit [Nonempty Idx] in
private lemma exists_agreementCount_ge [Nonempty Idx] (f : ScalarFn F Idx) :
    ∃ α : Vec F Idx,
      Fintype.card (Vec F Idx) / Fintype.card F ≤ agreementCount f α := by
  classical
  let N := Fintype.card (Vec F Idx)
  let k := Fintype.card (Vec F Idx) / Fintype.card F
  have hkpos : 0 < k := by
    dsimp [k]
    exact card_vec_div_card_field_pos (F := F) (Idx := Idx)
  have hkltN : k < N := by
    dsimp [k, N]
    exact card_vec_div_card_field_lt_card_vec (F := F) (Idx := Idx)
  have hstrict : (∑ _α : Vec F Idx, (k - 1)) <
      ∑ α : Vec F Idx, agreementCount f α := by
    have hlower := sum_agreementCount_lower (F := F) (Idx := Idx) f
    have hnum :
        (∑ _α : Vec F Idx, (k - 1)) < (N - 1) * k := by
      have hNpos : 0 < N := by
        dsimp [N]
        exact Fintype.card_pos
      have hnum' : N * (k - 1) < (N - 1) * k := by
        have hk1 : 1 ≤ k := Nat.succ_le_of_lt hkpos
        have hN1 : 1 ≤ N := Nat.succ_le_of_lt hNpos
        have hleft :
            ((N * (k - 1) : ℕ) : ℤ) = (N : ℤ) * ((k : ℤ) - 1) := by
          rw [Nat.cast_mul, Nat.cast_sub hk1, Nat.cast_one]
        have hright :
            (((N - 1) * k : ℕ) : ℤ) = ((N : ℤ) - 1) * (k : ℤ) := by
          rw [Nat.cast_mul, Nat.cast_sub hN1, Nat.cast_one]
        have hnum_int :
            ((N * (k - 1) : ℕ) : ℤ) < (((N - 1) * k : ℕ) : ℤ) := by
          rw [hleft, hright]
          have hkltN_int : (k : ℤ) < (N : ℤ) := by exact_mod_cast hkltN
          nlinarith
        exact_mod_cast hnum_int
      simpa [N] using hnum'
    exact hnum.trans_le (by simpa [N, k] using hlower)
  have hstrict' :
      (∑ α ∈ (Finset.univ : Finset (Vec F Idx)), (k - 1)) <
        ∑ α ∈ (Finset.univ : Finset (Vec F Idx)), agreementCount f α := by
    simpa using hstrict
  rcases Finset.exists_lt_of_sum_lt
      (s := (Finset.univ : Finset (Vec F Idx)))
      (f := fun _α : Vec F Idx => k - 1)
      (g := agreementCount f) hstrict' with ⟨α, _, hα⟩
  refine ⟨α, ?_⟩
  exact Nat.le_of_pred_lt (by simpa [Nat.pred_eq_sub_one, k] using hα)

omit [DecidableEq F] [DecidableEq Idx] [Nonempty Idx] in
private lemma charFn_eq_baseChar (α : Vec F Idx) (x : Vec F Idx) :
    charFn α x = baseChar (F := F) ⟪α, x⟫ᵥ := by
  rfl

omit [DecidableEq F] [DecidableEq Idx] [Nonempty Idx] in
private lemma charFn_add_apply (α β : Vec F Idx) (x : Vec F Idx) :
    charFn (α + β) x = charFn α x * charFn β x := by
  classical
  rw [charFn_eq_baseChar, charFn_eq_baseChar, charFn_eq_baseChar]
  rw [dotProduct, dotProduct, dotProduct]
  simp [add_mul, Finset.sum_add_distrib, AddChar.map_add_eq_mul]

omit [DecidableEq F] [DecidableEq Idx] [Nonempty Idx] in
private lemma charFn_zero_apply (x : Vec F Idx) :
    charFn (F := F) (Idx := Idx) 0 x = 1 := by
  simp [charFn_eq_baseChar, dotProduct]

omit [DecidableEq F] [DecidableEq Idx] [Nonempty Idx] in
private lemma charFn_mul_arg_apply (γ : Vec F Idx) (a : F) (x : Vec F Idx) :
    charFn γ (fun i => a * x i) = charFn (fun i => a * γ i) x := by
  classical
  rw [charFn_eq_baseChar, charFn_eq_baseChar]
  congr 1
  simp [dotProduct, mul_left_comm, mul_comm]

omit [DecidableEq F] [DecidableEq Idx] [Nonempty Idx] in
private lemma charFn_add_arg_apply (γ : Vec F Idx) (a b : F) (x y : Vec F Idx) :
    charFn γ (fun i => a * x i + b * y i) =
      charFn (fun i => a * γ i) x * charFn (fun i => b * γ i) y := by
  classical
  rw [charFn_eq_baseChar, charFn_eq_baseChar, charFn_eq_baseChar]
  simp [dotProduct, mul_add, Finset.sum_add_distrib, mul_left_comm, mul_comm,
    AddChar.map_add_eq_mul]

omit [Nonempty Idx] in
private lemma expectation_charFn (α : Vec F Idx) :
    expectation (charFn α) = if α = 0 then 1 else 0 := by
  have h := (characters_orthonormal_basis (F := F) (Idx := Idx)).1 α 0
  simpa [fnInner, expectation, charFn_zero_apply] using h

omit [Nonempty Idx] in
private lemma charFn_mul_expectation (α β : Vec F Idx) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      ∑ x : Vec F Idx, charFn α x * charFn β x =
        if α + β = 0 then 1 else 0 := by
  classical
  calc
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, charFn α x * charFn β x =
      expectation (charFn (α + β)) := by
        simp [expectation, charFn_add_apply]
    _ = if α + β = 0 then 1 else 0 := expectation_charFn (α + β)

omit [Nonempty Idx] in
private lemma fourier_sum_mul_char_average (A : Vec F Idx → ℂ) (β : Vec F Idx) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      ∑ x : Vec F Idx, (∑ α : Vec F Idx, A α * charFn α x) * charFn β x =
        A (-β) := by
  classical
  calc
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, (∑ α : Vec F Idx, A α * charFn α x) * charFn β x =
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, ∑ α : Vec F Idx, (A α * charFn α x) * charFn β x := by
        simp [Finset.sum_mul]
    _ = (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ α : Vec F Idx, ∑ x : Vec F Idx, (A α * charFn α x) * charFn β x := by
        rw [Finset.sum_comm]
    _ = ∑ α : Vec F Idx,
        A α * ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          ∑ x : Vec F Idx, charFn α x * charFn β x) := by
        simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = ∑ α : Vec F Idx, A α * (if α + β = 0 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro α _
        rw [charFn_mul_expectation]
    _ = A (-β) := by
        rw [Finset.sum_eq_single (-β)]
        · simp
        · intro α _ hα
          have hneq : α + β ≠ 0 := by
            intro hzero
            exact hα (add_eq_zero_iff_eq_neg.mp hzero)
          simp [hneq]
        · intro hnot
          simp at hnot

omit [Field F] [DecidableEq F] [Nonempty Idx] in
private lemma double_vec_average_left_factor (A : Vec F Idx → ℂ)
    (K : Vec F Idx → Vec F Idx → ℂ) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, ∑ y : Vec F Idx, A x * K x y =
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx,
          A x * ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            ∑ y : Vec F Idx, K x y) := by
  classical
  calc
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          ∑ x : Vec F Idx, ∑ y : Vec F Idx, A x * K x y =
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx,
          (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            ∑ y : Vec F Idx, A x * K x y := by
        simp [Finset.mul_sum, mul_assoc]
    _ = (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx,
          A x * ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            ∑ y : Vec F Idx, K x y) := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        calc
          (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              ∑ y : Vec F Idx, A x * K x y =
            ∑ y : Vec F Idx,
              (Fintype.card (Vec F Idx) : ℂ)⁻¹ * (A x * K x y) := by
              rw [Finset.mul_sum]
          _ = ∑ y : Vec F Idx,
              A x * ((Fintype.card (Vec F Idx) : ℂ)⁻¹ * K x y) := by
              apply Finset.sum_congr rfl
              intro y _
              ring
          _ = A x * ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              ∑ y : Vec F Idx, K x y) := by
              rw [Finset.mul_sum, Finset.mul_sum]

omit [Nonempty Idx] in
private lemma y_average_fourier_char_product (B C : Vec F Idx → ℂ) (a b : F)
    (x : Vec F Idx) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      ∑ y : Vec F Idx,
        (∑ β : Vec F Idx, B β * charFn β y) *
          (∑ γ : Vec F Idx,
            C γ * charFn (fun i => a * γ i) x *
              charFn (fun i => b * γ i) y) =
      ∑ γ : Vec F Idx,
        C γ * charFn (fun i => a * γ i) x *
          B (fun i => -b * γ i) := by
  classical
  calc
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ y : Vec F Idx,
          (∑ β : Vec F Idx, B β * charFn β y) *
            (∑ γ : Vec F Idx,
              C γ * charFn (fun i => a * γ i) x *
                charFn (fun i => b * γ i) y) =
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ y : Vec F Idx, ∑ γ : Vec F Idx,
          (C γ * charFn (fun i => a * γ i) x) *
            ((∑ β : Vec F Idx, B β * charFn β y) *
              charFn (fun i => b * γ i) y) := by
        congr 1
        apply Finset.sum_congr rfl
        intro y _
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro γ _
        ring
    _ = (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ γ : Vec F Idx, ∑ y : Vec F Idx,
          (C γ * charFn (fun i => a * γ i) x) *
            ((∑ β : Vec F Idx, B β * charFn β y) *
              charFn (fun i => b * γ i) y) := by
        rw [Finset.sum_comm]
    _ = ∑ γ : Vec F Idx,
        (C γ * charFn (fun i => a * γ i) x) *
          ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            ∑ y : Vec F Idx,
              (∑ β : Vec F Idx, B β * charFn β y) *
                charFn (fun i => b * γ i) y) := by
        simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = ∑ γ : Vec F Idx,
        C γ * charFn (fun i => a * γ i) x *
          B (fun i => -b * γ i) := by
        apply Finset.sum_congr rfl
        intro γ _
        rw [fourier_sum_mul_char_average]
        have hγ : -(fun i => b * γ i) = fun i => -b * γ i := by
          ext i
          simp
        rw [hγ]

omit [Nonempty Idx] in
private lemma x_average_fourier_char_product (A B C : Vec F Idx → ℂ) (a b : F) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      ∑ x : Vec F Idx,
        (∑ α : Vec F Idx, A α * charFn α x) *
          (∑ γ : Vec F Idx,
            C γ * charFn (fun i => a * γ i) x *
              B (fun i => -b * γ i)) =
      ∑ γ : Vec F Idx,
        A (fun i => -a * γ i) * B (fun i => -b * γ i) * C γ := by
  classical
  calc
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx,
          (∑ α : Vec F Idx, A α * charFn α x) *
            (∑ γ : Vec F Idx,
              C γ * charFn (fun i => a * γ i) x *
                B (fun i => -b * γ i)) =
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, ∑ γ : Vec F Idx,
          (C γ * B (fun i => -b * γ i)) *
            ((∑ α : Vec F Idx, A α * charFn α x) *
              charFn (fun i => a * γ i) x) := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro γ _
        ring
    _ = (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ γ : Vec F Idx, ∑ x : Vec F Idx,
          (C γ * B (fun i => -b * γ i)) *
            ((∑ α : Vec F Idx, A α * charFn α x) *
              charFn (fun i => a * γ i) x) := by
        rw [Finset.sum_comm]
    _ = ∑ γ : Vec F Idx,
        (C γ * B (fun i => -b * γ i)) *
          ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            ∑ x : Vec F Idx,
              (∑ α : Vec F Idx, A α * charFn α x) *
                charFn (fun i => a * γ i) x) := by
        simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = ∑ γ : Vec F Idx,
        A (fun i => -a * γ i) * B (fun i => -b * γ i) * C γ := by
        apply Finset.sum_congr rfl
        intro γ _
        rw [fourier_sum_mul_char_average]
        have haγ : -(fun i => a * γ i) = fun i => -a * γ i := by
          ext i
          simp
        rw [haγ]
        ring

omit [Nonempty Idx] in
private lemma triple_char_average (A B C : Vec F Idx → ℂ) (a b : F) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, ∑ y : Vec F Idx,
          (∑ α : Vec F Idx, A α * charFn α x) *
            (∑ β : Vec F Idx, B β * charFn β y) *
              (∑ γ : Vec F Idx, C γ * charFn γ (fun i => a * x i + b * y i)) =
      ∑ γ : Vec F Idx, A (fun i => -a * γ i) * B (fun i => -b * γ i) * C γ := by
  classical
  calc
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          ∑ x : Vec F Idx, ∑ y : Vec F Idx,
            (∑ α : Vec F Idx, A α * charFn α x) *
              (∑ β : Vec F Idx, B β * charFn β y) *
                (∑ γ : Vec F Idx, C γ * charFn γ (fun i => a * x i + b * y i)) =
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, (∑ α : Vec F Idx, A α * charFn α x) *
          ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            ∑ y : Vec F Idx,
              (∑ β : Vec F Idx, B β * charFn β y) *
                (∑ γ : Vec F Idx,
                  C γ * charFn (fun i => a * γ i) x *
                    charFn (fun i => b * γ i) y)) := by
        let Ax : Vec F Idx → ℂ := fun x =>
          ∑ α : Vec F Idx, A α * charFn α x
        let K : Vec F Idx → Vec F Idx → ℂ := fun x y =>
          (∑ β : Vec F Idx, B β * charFn β y) *
            (∑ γ : Vec F Idx,
              C γ * charFn (fun i => a * γ i) x *
                charFn (fun i => b * γ i) y)
        have hterm :
            ∀ x y : Vec F Idx,
              (∑ α : Vec F Idx, A α * charFn α x) *
                  (∑ β : Vec F Idx, B β * charFn β y) *
                    (∑ γ : Vec F Idx,
                      C γ * charFn γ (fun i => a * x i + b * y i)) =
                Ax x * K x y := by
          intro x y
          dsimp [Ax, K]
          have hsum :
              (∑ γ : Vec F Idx,
                C γ * charFn γ (fun i => a * x i + b * y i)) =
              ∑ γ : Vec F Idx,
                C γ * charFn (fun i => a * γ i) x *
                  charFn (fun i => b * γ i) y := by
            apply Finset.sum_congr rfl
            intro γ _
            rw [charFn_add_arg_apply]
            ring
          rw [hsum]
          ring
        calc
          (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                ∑ x : Vec F Idx, ∑ y : Vec F Idx,
                  (∑ α : Vec F Idx, A α * charFn α x) *
                    (∑ β : Vec F Idx, B β * charFn β y) *
                      (∑ γ : Vec F Idx,
                        C γ * charFn γ (fun i => a * x i + b * y i)) =
            (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                ∑ x : Vec F Idx, ∑ y : Vec F Idx, Ax x * K x y := by
              have hsum :
                  (∑ x : Vec F Idx, ∑ y : Vec F Idx,
                    (∑ α : Vec F Idx, A α * charFn α x) *
                      (∑ β : Vec F Idx, B β * charFn β y) *
                        (∑ γ : Vec F Idx,
                          C γ * charFn γ (fun i => a * x i + b * y i))) =
                  ∑ x : Vec F Idx, ∑ y : Vec F Idx, Ax x * K x y := by
                apply Finset.sum_congr rfl
                intro x _
                apply Finset.sum_congr rfl
                intro y _
                exact hterm x y
              rw [hsum]
          _ = (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              ∑ x : Vec F Idx, Ax x *
                ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                  ∑ y : Vec F Idx, K x y) := by
              rw [double_vec_average_left_factor]
          _ = (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              ∑ x : Vec F Idx,
                (∑ α : Vec F Idx, A α * charFn α x) *
                  ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                    ∑ y : Vec F Idx,
                      (∑ β : Vec F Idx, B β * charFn β y) *
                        (∑ γ : Vec F Idx,
                          C γ * charFn (fun i => a * γ i) x *
                            charFn (fun i => b * γ i) y)) := by
              rfl
    _ = (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, (∑ α : Vec F Idx, A α * charFn α x) *
          (∑ γ : Vec F Idx, C γ * charFn (fun i => a * γ i) x *
            B (fun i => -b * γ i)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        rw [y_average_fourier_char_product]
    _ = ∑ γ : Vec F Idx, A (fun i => -a * γ i) * B (fun i => -b * γ i) * C γ := by
        rw [x_average_fourier_char_product]

private lemma distance_eq_one_sub_agreement_real (f g : ScalarFn F Idx) :
    distance f g =
      1 - (Fintype.card (Vec F Idx) : Real)⁻¹ *
        ∑ x : Vec F Idx, (if f x = g x then (1 : Real) else 0) := by
  classical
  calc
    distance f g =
      (Fintype.card (Vec F Idx) : Real)⁻¹ *
        ∑ x : Vec F Idx, (if f x ≠ g x then (1 : Real) else 0) := by
        simp [distance]
    _ = (Fintype.card (Vec F Idx) : Real)⁻¹ *
        ∑ x : Vec F Idx, (1 - (if f x = g x then (1 : Real) else 0)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : f x = g x <;> simp [hx]
    _ = 1 - (Fintype.card (Vec F Idx) : Real)⁻¹ *
        ∑ x : Vec F Idx, (if f x = g x then (1 : Real) else 0) := by
        simp [Finset.sum_sub_distrib, mul_sub]

omit [Nonempty Idx] in
private lemma agreement_sum_linearFn_eq_count (f : ScalarFn F Idx) (α : Vec F Idx) :
    (∑ x : Vec F Idx, (if f x = linearFn α x then (1 : Real) else 0)) =
      (agreementCount f α : Real) := by
  classical
  simp [agreementCount]

/-- The `c`-phase encoding of the BLR acceptance equation at `(a, b, x, y)`.
It multiplies the phases of the two left-hand-side terms and the inverse phase
of the right-hand-side term, so it is `1` when the BLR equation holds. -/
private noncomputable def blrAccEventPhase (f : ScalarFn F Idx) (a b c : F)
    (x y : Vec F Idx) : ℂ :=
  phaseLift f (c * a) x * phaseLift f (c * b) y *
    phaseLift f (-c) (fun i => a * x i + b * y i)

omit [DecidableEq F] [Fintype Idx] [DecidableEq Idx] [Nonempty Idx] in
/-- The BLR acceptance phase is exactly the base additive character evaluated
on the BLR equation defect
`a * f x + b * f y - f (a • x + b • y)`, scaled by `c`. -/
private lemma blrAccEventPhase_eq_baseChar (f : ScalarFn F Idx) (a b c : F)
    (x y : Vec F Idx) :
    blrAccEventPhase f a b c x y =
      baseChar (F := F)
        (c * (a * f x + b * f y - f (fun i => a * x i + b * y i))) := by
  classical
  calc
    blrAccEventPhase f a b c x y =
        baseChar (F := F) (c * a * f x) * baseChar (F := F) (c * b * f y) *
          baseChar (F := F) ((-c) * f (fun i => a * x i + b * y i)) := by
          simp [blrAccEventPhase, phaseLift]
    _ = baseChar (F := F) (c * a * f x + c * b * f y + (-c) *
          f (fun i => a * x i + b * y i)) := by
          rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    _ = baseChar (F := F)
        (c * (a * f x + b * f y - f (fun i => a * x i + b * y i))) := by
          ring_nf

omit [Fintype Idx] [DecidableEq Idx] [Nonempty Idx] in
/-- The indicator of the BLR acceptance event is the average of its phase
encodings over all field characters, with the zero character separated from
the nonzero scalar phases. -/
private lemma BLRAcceptsAt_indicator_eq_phase_sum (f : ScalarFn F Idx)
    (a b : F) (x y : Vec F Idx) :
    (if a * f x + b * f y = f (fun i => a * x i + b * y i) then (1 : ℂ) else 0) =
      (Fintype.card F : ℂ)⁻¹ *
        (1 + ∑ c ∈ (nonzeroF (F := F)), blrAccEventPhase f a b c x y) := by
  classical
  rw [character_sum_indicator_eq (a * f x + b * f y)
    (f (fun i => a * x i + b * y i))]
  rw [sum_univ_eq_zero_add_sum_nonzero]
  congr 1
  simp [blrAccEventPhase_eq_baseChar]

private lemma blrAccEventPhase_xy_average (f : ScalarFn F Idx) (a b c : F) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, ∑ y : Vec F Idx, blrAccEventPhase f a b c x y =
      ∑ γ : Vec F Idx,
        fourierCoeff (phaseLift f (c * a)) (fun i => -a * γ i) *
          fourierCoeff (phaseLift f (c * b)) (fun i => -b * γ i) *
            fourierCoeff (phaseLift f (-c)) γ := by
  classical
  let A : Vec F Idx → ℂ := fun α => fourierCoeff (phaseLift f (c * a)) α
  let B : Vec F Idx → ℂ := fun β => fourierCoeff (phaseLift f (c * b)) β
  let C : Vec F Idx → ℂ := fun γ => fourierCoeff (phaseLift f (-c)) γ
  have hsum :
      (∑ x : Vec F Idx, ∑ y : Vec F Idx, blrAccEventPhase f a b c x y) =
      ∑ x : Vec F Idx, ∑ y : Vec F Idx,
        (∑ α : Vec F Idx, A α * charFn α x) *
          (∑ β : Vec F Idx, B β * charFn β y) *
            (∑ γ : Vec F Idx, C γ *
              charFn γ (fun i => a * x i + b * y i)) := by
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    dsimp [blrAccEventPhase, A, B, C]
    rw [fourier_inversion (phaseLift f (c * a)) x]
    rw [fourier_inversion (phaseLift f (c * b)) y]
    rw [fourier_inversion (phaseLift f (-c)) (fun i => a * x i + b * y i)]
  rw [hsum]
  simpa [A, B, C] using
    (triple_char_average (F := F) (Idx := Idx) A B C a b)

private noncomputable def phaseLinearCoeff (f : ScalarFn F Idx) (d : F)
    (η : Vec F Idx) : ℂ :=
  fourierCoeff (phaseLift f d) (fun i => d * η i)

omit [Nonempty Idx] in
private lemma linearFourierScoreC_eq_phaseLinearCoeff (f : ScalarFn F Idx)
    (η : Vec F Idx) :
    linearFourierScoreC f η =
      ∑ d ∈ (nonzeroF (F := F)), phaseLinearCoeff f d η := by
  rfl

omit [Fintype F] [DecidableEq F] [Fintype Idx] [DecidableEq Idx] [Nonempty Idx] in
private lemma vec_mul_left_bijective (d : F) (hd : d ≠ 0) :
    Function.Bijective (fun η : Vec F Idx => fun i => d * η i) := by
  constructor
  · intro η θ hηθ
    ext i
    exact mul_left_cancel₀ hd (congrFun hηθ i)
  · intro η
    refine ⟨fun i => d⁻¹ * η i, ?_⟩
    ext i
    simp [hd]

omit [DecidableEq F] [Nonempty Idx] in
private lemma sum_vec_mul_left (d : F) (hd : d ≠ 0)
    (H : Vec F Idx → ℂ) :
    ∑ η : Vec F Idx, H (fun i => d * η i) =
      ∑ η : Vec F Idx, H η := by
  exact (vec_mul_left_bijective (F := F) (Idx := Idx) d hd).sum_comp H

omit [DecidableEq F] [Nonempty Idx] in
private lemma sum_vec_mul_left_real (d : F) (hd : d ≠ 0)
    (H : Vec F Idx → ℝ) :
    ∑ η : Vec F Idx, H (fun i => d * η i) =
      ∑ η : Vec F Idx, H η := by
  exact (vec_mul_left_bijective (F := F) (Idx := Idx) d hd).sum_comp H

private lemma sum_nonzero_mul_left (d : F) (hd : d ≠ 0) (H : F → ℂ) :
    ∑ a ∈ (nonzeroF (F := F)), H (d * a) =
      ∑ e ∈ (nonzeroF (F := F)), H e := by
  classical
  refine Finset.sum_bijective (s := nonzeroF (F := F))
    (t := nonzeroF (F := F)) (fun a => d * a) (mulLeft_bijective₀ d hd) ?_ ?_
  · intro a
    simp [nonzeroF, hd]
  · intro a _
    rfl

private lemma sum_nonzero_neg (H : F → ℂ) :
    ∑ c ∈ (nonzeroF (F := F)), H (-c) =
      ∑ d ∈ (nonzeroF (F := F)), H d := by
  classical
  have hbij : Function.Bijective (fun c : F => -c) := by
    constructor
    · intro a b hab
      exact neg_inj.mp hab
    · intro a
      exact ⟨-a, by simp⟩
  refine Finset.sum_bijective (s := nonzeroF (F := F))
    (t := nonzeroF (F := F)) (fun c : F => -c) hbij ?_ ?_
  · intro c
    simp [nonzeroF]
  · intro c _
    rfl

omit [DecidableEq F] in
private lemma fnNormSq_phaseLift (f : ScalarFn F Idx) (c : F) :
    fnNormSq (phaseLift f c) = 1 := by
  classical
  have hnorm : ∀ x : Vec F Idx, ‖phaseLift f c x‖ = 1 := by
    intro x
    letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
    letI : NeZero (ringChar F) := ⟨Nat.Prime.ne_zero (CharP.char_is_prime F (ringChar F))⟩
    let ψ : AddChar F ℂ := baseChar (F := F)
    have hphase : phaseLift f c x = ψ (c * f x) := by
      simp [phaseLift, baseChar, ψ]
    rw [hphase]
    exact AddChar.norm_apply ψ (c * f x)
  unfold fnNormSq
  simp [hnorm]

private lemma sum_norm_sq_phaseLinearCoeff (f : ScalarFn F Idx) {c : F}
    (hc : c ≠ 0) :
    ∑ α : Vec F Idx, ‖phaseLinearCoeff f c α‖ ^ 2 = 1 := by
  classical
  calc
    ∑ α : Vec F Idx, ‖phaseLinearCoeff f c α‖ ^ 2 =
        ∑ β : Vec F Idx, ‖fourierCoeff (phaseLift f c) β‖ ^ 2 := by
          dsimp [phaseLinearCoeff]
          rw [sum_vec_mul_left_real (F := F) (Idx := Idx) c hc
            (fun β : Vec F Idx => ‖fourierCoeff (phaseLift f c) β‖ ^ 2)]
    _ = fnNormSq (phaseLift f c) :=
        parseval_identity (F := F) (Idx := Idx) (phaseLift f c)
    _ = 1 := fnNormSq_phaseLift (F := F) (Idx := Idx) f c

omit [Nonempty Idx] in
private lemma norm_sq_linearFourierScoreC_le_card_mul_sum_norm_sq
    (f : ScalarFn F Idx) (α : Vec F Idx) :
    ‖linearFourierScoreC f α‖ ^ 2 ≤
      ((nonzeroF (F := F)).card : ℝ) *
        ∑ c ∈ (nonzeroF (F := F)), ‖phaseLinearCoeff f c α‖ ^ 2 := by
  classical
  let nz := nonzeroF (F := F)
  let A : F → ℂ := fun c => phaseLinearCoeff f c α
  have hnorm :
      ‖linearFourierScoreC f α‖ ≤ ∑ c ∈ nz, ‖A c‖ := by
    rw [linearFourierScoreC_eq_phaseLinearCoeff]
    dsimp [A, nz]
    exact norm_sum_le _ _
  have hsq :
      ‖linearFourierScoreC f α‖ ^ 2 ≤ (∑ c ∈ nz, ‖A c‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (Finset.sum_nonneg fun c _ => norm_nonneg (A c))).2 hnorm
  have hsq_norms :
      (∑ c ∈ nz, ‖A c‖) ^ 2 ≤
        (nz.card : ℝ) * ∑ c ∈ nz, ‖A c‖ ^ 2 := by
    simpa [nz, A] using
      (sq_sum_le_card_mul_sum_sq (s := nz) (f := fun c : F => ‖A c‖))
  exact hsq.trans hsq_norms

/-- The squared complex linear Fourier scores have total mass at most `(q - 1)^2`. -/
private lemma sum_linearFourierScoreC_sq_upperbound (f : ScalarFn F Idx) :
    ∑ α : Vec F Idx, ‖linearFourierScoreC f α‖ ^ 2 ≤
      ((nonzeroF (F := F)).card : ℝ) ^ 2 := by
  classical
  let nz := nonzeroF (F := F)
  calc
    ∑ α : Vec F Idx, ‖linearFourierScoreC f α‖ ^ 2 ≤
        ∑ α : Vec F Idx,
          (nz.card : ℝ) * ∑ c ∈ nz, ‖phaseLinearCoeff f c α‖ ^ 2 := by
          exact Finset.sum_le_sum fun α _ =>
            norm_sq_linearFourierScoreC_le_card_mul_sum_norm_sq
              (F := F) (Idx := Idx) f α
    _ = (nz.card : ℝ) *
        ∑ α : Vec F Idx, ∑ c ∈ nz, ‖phaseLinearCoeff f c α‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = (nz.card : ℝ) *
        ∑ c ∈ nz, ∑ α : Vec F Idx, ‖phaseLinearCoeff f c α‖ ^ 2 := by
        congr 1
        rw [Finset.sum_comm]
    _ = (nz.card : ℝ) * ∑ c ∈ nz, (1 : ℝ) := by
        congr 1
        apply Finset.sum_congr rfl
        intro c hc
        have hc0 : c ≠ 0 := by
          simpa [nz, nonzeroF] using hc
        exact sum_norm_sq_phaseLinearCoeff (F := F) (Idx := Idx) f hc0
    _ = ((nonzeroF (F := F)).card : ℝ) ^ 2 := by
        simp [nz, pow_two]

private lemma blrAccEventPhase_xy_average_reindexed (f : ScalarFn F Idx)
    (a b c : F) (hc : c ≠ 0) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, ∑ y : Vec F Idx, blrAccEventPhase f a b c x y =
      ∑ η : Vec F Idx,
        phaseLinearCoeff f (c * a) η *
          phaseLinearCoeff f (c * b) η *
            phaseLinearCoeff f (-c) η := by
  classical
  rw [blrAccEventPhase_xy_average]
  let P : Vec F Idx → ℂ := fun γ =>
    fourierCoeff (phaseLift f (c * a)) (fun i => -a * γ i) *
      fourierCoeff (phaseLift f (c * b)) (fun i => -b * γ i) *
        fourierCoeff (phaseLift f (-c)) γ
  have hmul :
      ∑ γ : Vec F Idx, P γ =
        ∑ η : Vec F Idx, P (fun i => (-c) * η i) := by
    exact (sum_vec_mul_left (F := F) (Idx := Idx) (-c) (neg_ne_zero.mpr hc) P).symm
  rw [show (∑ γ : Vec F Idx,
        fourierCoeff (phaseLift f (c * a)) (fun i => -a * γ i) *
          fourierCoeff (phaseLift f (c * b)) (fun i => -b * γ i) *
            fourierCoeff (phaseLift f (-c)) γ) = ∑ γ : Vec F Idx, P γ by rfl]
  rw [hmul]
  apply Finset.sum_congr rfl
  intro η _
  dsimp [P, phaseLinearCoeff]
  have hleftA :
      (fun i => -a * ((-c) * η i)) = fun i => (c * a) * η i := by
    ext i
    ring
  have hleftB :
      (fun i => -b * ((-c) * η i)) = fun i => (c * b) * η i := by
    ext i
    ring
  rw [hleftA, hleftB]

private lemma xy_average_one_add_blrAccEventPhase_sum (f : ScalarFn F Idx)
    (a b : F) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ x : Vec F Idx, ∑ y : Vec F Idx,
          (1 + ∑ c ∈ (nonzeroF (F := F)), blrAccEventPhase f a b c x y) =
      1 + ∑ c ∈ (nonzeroF (F := F)), ∑ η : Vec F Idx,
        phaseLinearCoeff f (c * a) η *
          phaseLinearCoeff f (c * b) η *
            phaseLinearCoeff f (-c) η := by
  classical
  have hvec : (Fintype.card (Vec F Idx) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          ∑ x : Vec F Idx, ∑ y : Vec F Idx,
            (1 + ∑ c ∈ (nonzeroF (F := F)), blrAccEventPhase f a b c x y) =
      1 + (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          ∑ x : Vec F Idx, ∑ y : Vec F Idx,
            ∑ c ∈ (nonzeroF (F := F)), blrAccEventPhase f a b c x y := by
        simp [Finset.sum_add_distrib, mul_add, Finset.mul_sum, mul_assoc]
    _ = 1 + ∑ c ∈ (nonzeroF (F := F)),
        ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            ∑ x : Vec F Idx, ∑ y : Vec F Idx, blrAccEventPhase f a b c x y) := by
        congr 1
        calc
          (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                ∑ x : Vec F Idx, ∑ y : Vec F Idx,
                  ∑ c ∈ (nonzeroF (F := F)), blrAccEventPhase f a b c x y =
            (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                ∑ c ∈ (nonzeroF (F := F)), ∑ x : Vec F Idx,
                  ∑ y : Vec F Idx, blrAccEventPhase f a b c x y := by
              have hsum :
                  (∑ x : Vec F Idx, ∑ y : Vec F Idx,
                      ∑ c ∈ (nonzeroF (F := F)), blrAccEventPhase f a b c x y) =
                    ∑ c ∈ (nonzeroF (F := F)), ∑ x : Vec F Idx,
                      ∑ y : Vec F Idx, blrAccEventPhase f a b c x y := by
                calc
                  (∑ x : Vec F Idx, ∑ y : Vec F Idx,
                      ∑ c ∈ (nonzeroF (F := F)), blrAccEventPhase f a b c x y) =
                    ∑ x : Vec F Idx, ∑ c ∈ (nonzeroF (F := F)),
                      ∑ y : Vec F Idx, blrAccEventPhase f a b c x y := by
                      apply Finset.sum_congr rfl
                      intro x _
                      rw [Finset.sum_comm]
                  _ = ∑ c ∈ (nonzeroF (F := F)), ∑ x : Vec F Idx,
                      ∑ y : Vec F Idx, blrAccEventPhase f a b c x y := by
                      rw [Finset.sum_comm]
              rw [hsum]
          _ = ∑ c ∈ (nonzeroF (F := F)),
              ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                  ∑ x : Vec F Idx, ∑ y : Vec F Idx, blrAccEventPhase f a b c x y) := by
              rw [Finset.mul_sum]
    _ = 1 + ∑ c ∈ (nonzeroF (F := F)), ∑ η : Vec F Idx,
        phaseLinearCoeff f (c * a) η *
          phaseLinearCoeff f (c * b) η *
            phaseLinearCoeff f (-c) η := by
        congr 1
        apply Finset.sum_congr rfl
        intro c hc
        have hc0 : c ≠ 0 := by
          simpa [nonzeroF] using hc
        rw [blrAccEventPhase_xy_average_reindexed (F := F) (Idx := Idx) f a b c hc0]

private lemma ab_sum_xy_average_one_add_blrAccEventPhase_sum (f : ScalarFn F Idx) :
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
      (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
          ∑ x : Vec F Idx, ∑ y : Vec F Idx,
            (1 + ∑ c ∈ (nonzeroF (F := F)), blrAccEventPhase f a b c x y) =
      ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
        (1 + ∑ c ∈ (nonzeroF (F := F)), ∑ η : Vec F Idx,
          phaseLinearCoeff f (c * a) η *
            phaseLinearCoeff f (c * b) η *
              phaseLinearCoeff f (-c) η) := by
  classical
  calc
    (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
        (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
            ∑ x : Vec F Idx, ∑ y : Vec F Idx,
              (1 + ∑ c ∈ (nonzeroF (F := F)), blrAccEventPhase f a b c x y) =
      ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
        ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
          (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            ∑ x : Vec F Idx, ∑ y : Vec F Idx,
              (1 + ∑ c ∈ (nonzeroF (F := F)), blrAccEventPhase f a b c x y)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
    _ = ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
        (1 + ∑ c ∈ (nonzeroF (F := F)), ∑ η : Vec F Idx,
          phaseLinearCoeff f (c * a) η *
            phaseLinearCoeff f (c * b) η *
              phaseLinearCoeff f (-c) η) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [xy_average_one_add_blrAccEventPhase_sum]

omit [Nonempty Idx] in
private lemma ab_average_one_add_phase_triple_sum (f : ScalarFn F Idx) :
    ((nonzeroF (F := F)).card : ℂ)⁻¹ *
      ((nonzeroF (F := F)).card : ℂ)⁻¹ *
        ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
          (1 + ∑ c ∈ (nonzeroF (F := F)), ∑ η : Vec F Idx,
            phaseLinearCoeff f (c * a) η *
              phaseLinearCoeff f (c * b) η *
                phaseLinearCoeff f (-c) η) =
      1 + ((nonzeroF (F := F)).card : ℂ)⁻¹ ^ 2 *
        ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
          ∑ c ∈ (nonzeroF (F := F)), ∑ η : Vec F Idx,
            phaseLinearCoeff f (c * a) η *
              phaseLinearCoeff f (c * b) η *
                phaseLinearCoeff f (-c) η := by
  classical
  let nz : Finset F := nonzeroF (F := F)
  let P : F → F → ℂ := fun a b =>
    ∑ c ∈ nz, ∑ η : Vec F Idx,
      phaseLinearCoeff f (c * a) η *
        phaseLinearCoeff f (c * b) η *
          phaseLinearCoeff f (-c) η
  have hnz_nonempty : nz.Nonempty := by
    exact ⟨1, by simp [nz, nonzeroF]⟩
  have hnz : (nz.card : ℂ) ≠ 0 := by
    exact_mod_cast hnz_nonempty.card_pos.ne'
  calc
    ((nonzeroF (F := F)).card : ℂ)⁻¹ *
        ((nonzeroF (F := F)).card : ℂ)⁻¹ *
          ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
            (1 + ∑ c ∈ (nonzeroF (F := F)), ∑ η : Vec F Idx,
              phaseLinearCoeff f (c * a) η *
                phaseLinearCoeff f (c * b) η *
                  phaseLinearCoeff f (-c) η) =
      (nz.card : ℂ)⁻¹ * (nz.card : ℂ)⁻¹ *
        ∑ a ∈ nz, ∑ b ∈ nz, (1 + P a b) := by
        rfl
    _ = 1 + (nz.card : ℂ)⁻¹ ^ 2 *
        ∑ a ∈ nz, ∑ b ∈ nz, P a b := by
        simp [P, Finset.sum_add_distrib, Finset.mul_sum, mul_add, hnz, pow_two,
          mul_assoc, mul_comm]
    _ = 1 + ((nonzeroF (F := F)).card : ℂ)⁻¹ ^ 2 *
        ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
          ∑ c ∈ (nonzeroF (F := F)), ∑ η : Vec F Idx,
            phaseLinearCoeff f (c * a) η *
              phaseLinearCoeff f (c * b) η *
                phaseLinearCoeff f (-c) η := by
        rfl

omit [Nonempty Idx] in
private lemma scalar_phase_triple_sum_fixed_eta (f : ScalarFn F Idx) (η : Vec F Idx) :
    (∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
      ∑ c ∈ (nonzeroF (F := F)),
        phaseLinearCoeff f (c * a) η *
          phaseLinearCoeff f (c * b) η *
            phaseLinearCoeff f (-c) η) =
      (linearFourierScoreC f η) ^ 3 := by
  classical
  let L : F → ℂ := fun d => phaseLinearCoeff f d η
  let nz : Finset F := nonzeroF (F := F)
  have hscore : linearFourierScoreC f η = ∑ d ∈ nz, L d := rfl
  calc
    (∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
      ∑ c ∈ (nonzeroF (F := F)),
        phaseLinearCoeff f (c * a) η *
          phaseLinearCoeff f (c * b) η *
            phaseLinearCoeff f (-c) η) =
      ∑ a ∈ nz, ∑ b ∈ nz, ∑ c ∈ nz, L (c * a) * L (c * b) * L (-c) := by
        rfl
    _ = ∑ c ∈ nz, ∑ a ∈ nz, ∑ b ∈ nz, L (c * a) * L (c * b) * L (-c) := by
        calc
          (∑ a ∈ nz, ∑ b ∈ nz, ∑ c ∈ nz, L (c * a) * L (c * b) * L (-c)) =
            ∑ a ∈ nz, ∑ c ∈ nz, ∑ b ∈ nz, L (c * a) * L (c * b) * L (-c) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.sum_comm]
          _ = ∑ c ∈ nz, ∑ a ∈ nz, ∑ b ∈ nz, L (c * a) * L (c * b) * L (-c) := by
              rw [Finset.sum_comm]
    _ = ∑ c ∈ nz,
        (∑ d ∈ nz, L d) * (∑ e ∈ nz, L e) * L (-c) := by
        apply Finset.sum_congr rfl
        intro c hc
        have hc0 : c ≠ 0 := by
          simpa [nz, nonzeroF] using hc
        calc
          (∑ a ∈ nz, ∑ b ∈ nz, L (c * a) * L (c * b) * L (-c)) =
            (∑ a ∈ nz, L (c * a)) * (∑ b ∈ nz, L (c * b)) * L (-c) := by
              simp [Finset.mul_sum, mul_assoc, mul_comm]
          _ = (∑ d ∈ nz, L d) * (∑ e ∈ nz, L e) * L (-c) := by
              rw [sum_nonzero_mul_left (F := F) c hc0 L]
    _ = (∑ d ∈ nz, L d) ^ 3 := by
        let S : ℂ := ∑ d ∈ nz, L d
        have hneg : (∑ c ∈ nz, L (-c)) = S := by
          dsimp [S]
          rw [sum_nonzero_neg (F := F) L]
        calc
          (∑ c ∈ nz, (∑ d ∈ nz, L d) * (∑ e ∈ nz, L e) * L (-c)) =
            S * S * (∑ c ∈ nz, L (-c)) := by
              rw [Finset.mul_sum]
              rw [Finset.mul_sum]
          _ = S ^ 3 := by
              rw [hneg]
              ring
          _ = (∑ d ∈ nz, L d) ^ 3 := rfl
    _ = (linearFourierScoreC f η) ^ 3 := by
        rw [hscore]

omit [Nonempty Idx] in
private lemma scalar_phase_triple_sum (f : ScalarFn F Idx) :
    (∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
      ∑ c ∈ (nonzeroF (F := F)), ∑ η : Vec F Idx,
        phaseLinearCoeff f (c * a) η *
          phaseLinearCoeff f (c * b) η *
            phaseLinearCoeff f (-c) η) =
      ∑ η : Vec F Idx, (linearFourierScoreC f η) ^ 3 := by
  classical
  calc
    (∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
      ∑ c ∈ (nonzeroF (F := F)), ∑ η : Vec F Idx,
        phaseLinearCoeff f (c * a) η *
          phaseLinearCoeff f (c * b) η *
            phaseLinearCoeff f (-c) η) =
      ∑ η : Vec F Idx, ∑ a ∈ (nonzeroF (F := F)),
        ∑ b ∈ (nonzeroF (F := F)), ∑ c ∈ (nonzeroF (F := F)),
          phaseLinearCoeff f (c * a) η *
            phaseLinearCoeff f (c * b) η *
              phaseLinearCoeff f (-c) η := by
        calc
          (∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
            ∑ c ∈ (nonzeroF (F := F)), ∑ η : Vec F Idx,
              phaseLinearCoeff f (c * a) η *
                phaseLinearCoeff f (c * b) η *
                  phaseLinearCoeff f (-c) η) =
            ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
              ∑ η : Vec F Idx, ∑ c ∈ (nonzeroF (F := F)),
                phaseLinearCoeff f (c * a) η *
                  phaseLinearCoeff f (c * b) η *
                    phaseLinearCoeff f (-c) η := by
              apply Finset.sum_congr rfl
              intro a _
              apply Finset.sum_congr rfl
              intro b _
              rw [Finset.sum_comm]
          _ = ∑ a ∈ (nonzeroF (F := F)), ∑ η : Vec F Idx,
              ∑ b ∈ (nonzeroF (F := F)), ∑ c ∈ (nonzeroF (F := F)),
                phaseLinearCoeff f (c * a) η *
                  phaseLinearCoeff f (c * b) η *
                    phaseLinearCoeff f (-c) η := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.sum_comm]
          _ = ∑ η : Vec F Idx, ∑ a ∈ (nonzeroF (F := F)),
              ∑ b ∈ (nonzeroF (F := F)), ∑ c ∈ (nonzeroF (F := F)),
                phaseLinearCoeff f (c * a) η *
                  phaseLinearCoeff f (c * b) η *
                    phaseLinearCoeff f (-c) η := by
              rw [Finset.sum_comm]
    _ = ∑ η : Vec F Idx, (linearFourierScoreC f η) ^ 3 := by
        apply Finset.sum_congr rfl
        intro η _
        rw [scalar_phase_triple_sum_fixed_eta]

/-- Complex form of the exact BLR acceptance formula in terms of the Fourier scores
`∑ c∈Fˣ, \widehat{f_c}(cα)`. -/
private lemma exact_blr_acceptance_formulaC (f : ScalarFn F Idx) :
    (acceptanceProbabilityBLR f : ℂ) =
      (Fintype.card F : ℂ)⁻¹ *
        (1 + ((nonzeroF (F := F)).card : ℂ)⁻¹ ^ 2 *
          ∑ α : Vec F Idx, (linearFourierScoreC f α) ^ 3) := by
  classical
  let S : Vec F Idx → ℂ := linearFourierScoreC f
  change (acceptanceProbabilityBLR f : ℂ) =
      (Fintype.card F : ℂ)⁻¹ *
        (1 + ((nonzeroF (F := F)).card : ℂ)⁻¹ ^ 2 *
          ∑ α : Vec F Idx, (S α) ^ 3)
  have haccept :
      (acceptanceProbabilityBLR f : ℂ) =
        ((nonzeroF (F := F)).card : ℂ)⁻¹ *
          ((nonzeroF (F := F)).card : ℂ)⁻¹ *
            (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
                  ∑ x : Vec F Idx, ∑ y : Vec F Idx,
                    if BLRAcceptsAt f a b x y then (1 : ℂ) else 0 := by
    simp [acceptanceProbabilityBLR]
  have hindicator :
      (∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
        ∑ x : Vec F Idx, ∑ y : Vec F Idx,
          if BLRAcceptsAt f a b x y then (1 : ℂ) else 0) =
        ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
          ∑ x : Vec F Idx, ∑ y : Vec F Idx,
            (Fintype.card F : ℂ)⁻¹ *
              (1 + ∑ c ∈ (nonzeroF (F := F)), blrAccEventPhase f a b c x y) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [show (if BLRAcceptsAt f a b x y then (1 : ℂ) else 0) =
      (if a * f x + b * f y = f (fun i => a * x i + b * y i) then (1 : ℂ) else 0) by
        simp [BLRAcceptsAt]]
    exact BLRAcceptsAt_indicator_eq_phase_sum (F := F) (Idx := Idx) f a b x y
  calc
    (acceptanceProbabilityBLR f : ℂ) =
      ((nonzeroF (F := F)).card : ℂ)⁻¹ *
        ((nonzeroF (F := F)).card : ℂ)⁻¹ *
          (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
                ∑ x : Vec F Idx, ∑ y : Vec F Idx,
                  if BLRAcceptsAt f a b x y then (1 : ℂ) else 0 := haccept
    _ = ((nonzeroF (F := F)).card : ℂ)⁻¹ *
        ((nonzeroF (F := F)).card : ℂ)⁻¹ *
          (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
            (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
                ∑ x : Vec F Idx, ∑ y : Vec F Idx,
                  (Fintype.card F : ℂ)⁻¹ *
                    (1 + ∑ c ∈ (nonzeroF (F := F)),
                      blrAccEventPhase f a b c x y) := by
        rw [hindicator]
    _ = (Fintype.card F : ℂ)⁻¹ *
        (((nonzeroF (F := F)).card : ℂ)⁻¹ *
          ((nonzeroF (F := F)).card : ℂ)⁻¹ *
            ((Fintype.card (Vec F Idx) : ℂ)⁻¹ *
              (Fintype.card (Vec F Idx) : ℂ)⁻¹ *
                ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
                  ∑ x : Vec F Idx, ∑ y : Vec F Idx,
                    (1 + ∑ c ∈ (nonzeroF (F := F)),
                      blrAccEventPhase f a b c x y))) := by
        simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = (Fintype.card F : ℂ)⁻¹ *
        (((nonzeroF (F := F)).card : ℂ)⁻¹ *
          ((nonzeroF (F := F)).card : ℂ)⁻¹ *
            ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
              (1 + ∑ c ∈ (nonzeroF (F := F)), ∑ η : Vec F Idx,
                phaseLinearCoeff f (c * a) η *
                  phaseLinearCoeff f (c * b) η *
                    phaseLinearCoeff f (-c) η)) := by
        rw [ab_sum_xy_average_one_add_blrAccEventPhase_sum]
    _ = (Fintype.card F : ℂ)⁻¹ *
        (1 + ((nonzeroF (F := F)).card : ℂ)⁻¹ ^ 2 *
          ∑ a ∈ (nonzeroF (F := F)), ∑ b ∈ (nonzeroF (F := F)),
            ∑ c ∈ (nonzeroF (F := F)), ∑ η : Vec F Idx,
              phaseLinearCoeff f (c * a) η *
                phaseLinearCoeff f (c * b) η *
                  phaseLinearCoeff f (-c) η) := by
        rw [ab_average_one_add_phase_triple_sum]
    _ = (Fintype.card F : ℂ)⁻¹ *
        (1 + ((nonzeroF (F := F)).card : ℂ)⁻¹ ^ 2 *
          ∑ α : Vec F Idx, (S α) ^ 3) := by
        rw [scalar_phase_triple_sum]

/-- Exact BLR acceptance formula in terms of the real linear Fourier scores. -/
lemma exact_blr_acceptance_formula (f : ScalarFn F Idx) :
    acceptanceProbabilityBLR f =
      (Fintype.card F : Real)⁻¹ *
        (1 + ((nonzeroF (F := F)).card : Real)⁻¹ ^ 2 *
          ∑ α : Vec F Idx, (linearFourierScore f α) ^ 3) := by
  classical
  apply Complex.ofReal_injective
  have hscore :
      (∑ α : Vec F Idx, (linearFourierScoreC f α) ^ 3) =
        ((∑ α : Vec F Idx, (linearFourierScore f α) ^ 3 : Real) : ℂ) := by
    calc
      (∑ α : Vec F Idx, (linearFourierScoreC f α) ^ 3) =
          ∑ α : Vec F Idx, ((linearFourierScore f α : ℂ) ^ 3) := by
            apply Finset.sum_congr rfl
            intro α _
            rw [linearFourierScoreC_eq_ofReal_score]
      _ = ((∑ α : Vec F Idx, (linearFourierScore f α) ^ 3 : Real) : ℂ) := by
            simp
  simpa [hscore] using exact_blr_acceptance_formulaC (F := F) (Idx := Idx) f

/-- Real form of `sum_linearFourierScoreC_sq_upperbound`. -/
lemma sum_linearFourierScore_sq_upperbound (f : ScalarFn F Idx) :
    ∑ α : Vec F Idx, (linearFourierScore f α) ^ 2 ≤
      ((nonzeroF (F := F)).card : ℝ) ^ 2 := by
  classical
  calc
    ∑ α : Vec F Idx, (linearFourierScore f α) ^ 2 =
        ∑ α : Vec F Idx, ‖linearFourierScoreC f α‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro α _
          rw [linearFourierScoreC_eq_ofReal_score]
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp [pow_two]
    _ ≤ ((nonzeroF (F := F)).card : ℝ) ^ 2 :=
        sum_linearFourierScoreC_sq_upperbound (F := F) (Idx := Idx) f

private lemma linearFourierScore_eq_card_mul_agreement_ratio_sub_one
    (f : ScalarFn F Idx) (α : Vec F Idx) :
    linearFourierScore f α =
      (Fintype.card F : Real) *
        ((Fintype.card (Vec F Idx) : Real)⁻¹ * (agreementCount f α : Real)) - 1 := by
  rw [linearFourierScore_eq_card_mul_one_sub_distance]
  rw [distance_eq_one_sub_agreement_real]
  rw [agreement_sum_linearFn_eq_count]
  ring

/-- The maximum linear Fourier score is nonnegative. This follows by choosing
a linear function whose agreement set with `f` has at least the average fiber
size, so its score is at least zero. -/
private lemma linearFourierScore_sup_nonneg (f : ScalarFn F Idx) :
    0 ≤ (Finset.univ.sup'
      (Finset.univ_nonempty : (Finset.univ : Finset (Vec F Idx)).Nonempty)
      (linearFourierScore f)) := by
  classical
  rcases exists_agreementCount_ge (F := F) (Idx := Idx) f with ⟨α, hα⟩
  have hscore :=
    linearFourierScore_eq_card_mul_agreement_ratio_sub_one
      (F := F) (Idx := Idx) f α
  have hqpos : 0 < (Fintype.card F : Real) := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hNpos : 0 < (Fintype.card (Vec F Idx) : Real) := by
    exact_mod_cast Fintype.card_pos (α := Vec F Idx)
  have hbase :
      (Fintype.card F : Real) *
        ((Fintype.card (Vec F Idx) : Real)⁻¹ *
          ((Fintype.card (Vec F Idx) / Fintype.card F : ℕ) : Real)) = 1 := by
    simp
    field_simp [hqpos.ne']
  have hα_real :
      ((Fintype.card (Vec F Idx) / Fintype.card F : ℕ) : Real) ≤
        (agreementCount f α : Real) := by
    exact_mod_cast hα
  have hagree_ratio :
      1 ≤ (Fintype.card F : Real) *
        ((Fintype.card (Vec F Idx) : Real)⁻¹ * (agreementCount f α : Real)) := by
    calc
      (1 : Real) =
          (Fintype.card F : Real) *
            ((Fintype.card (Vec F Idx) : Real)⁻¹ *
              ((Fintype.card (Vec F Idx) / Fintype.card F : ℕ) : Real)) := hbase.symm
      _ ≤ (Fintype.card F : Real) *
          ((Fintype.card (Vec F Idx) : Real)⁻¹ * (agreementCount f α : Real)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hα_real (inv_nonneg.mpr hNpos.le))
            hqpos.le
  have hαscore_nonneg : 0 ≤ linearFourierScore f α := by
    rw [hscore]
    linarith
  exact hαscore_nonneg.trans
    (Finset.le_sup' (s := (Finset.univ : Finset (Vec F Idx)))
      (f := linearFourierScore f) (by simp))

/-- Soundness of the finite-field BLR test in the Fourier-score form used by
the proof: acceptance is at most `1 - distanceToLinear f`. -/
theorem blr_soundness (f : ScalarFn F Idx) :
    acceptanceProbabilityBLR f ≤ 1 - distanceToLinear f := by
  classical
  let nz : Finset F := nonzeroF (F := F)
  let coeffs : Finset (Vec F Idx) := Finset.univ
  let score : Vec F Idx → Real := linearFourierScore (F := F) (Idx := Idx) f
  let M : Real := coeffs.sup' (Finset.univ_nonempty :
    (Finset.univ : Finset (Vec F Idx)).Nonempty) score
  have hM_nonneg' : 0 ≤ M := by
    simpa [M, coeffs, score] using
      linearFourierScore_sup_nonneg (F := F) (Idx := Idx) f
  have hnz_nonempty : nz.Nonempty := by
    exact ⟨1, by simp [nz, nonzeroF]⟩
  have hnz_pos : 0 < (nz.card : Real) := by
    exact_mod_cast hnz_nonempty.card_pos
  have hnz_sq_ne : (nz.card : Real) ^ 2 ≠ 0 := by
    exact pow_ne_zero _ hnz_pos.ne'
  have hscore_le : ∀ α : Vec F Idx, score α ≤ M := by
    intro α
    exact Finset.le_sup' (s := coeffs) (f := score) (by simp [coeffs])
  have hcube_le :
      ∑ α : Vec F Idx, (score α) ^ 3 ≤
        M * ∑ α : Vec F Idx, (score α) ^ 2 := by
    calc
      ∑ α : Vec F Idx, (score α) ^ 3 ≤
          ∑ α : Vec F Idx, M * (score α) ^ 2 := by
          apply Finset.sum_le_sum
          intro α _
          have hmul :
              score α * (score α) ^ 2 ≤ M * (score α) ^ 2 :=
            mul_le_mul_of_nonneg_right (hscore_le α) (sq_nonneg (score α))
          nlinarith [hmul]
      _ = M * ∑ α : Vec F Idx, (score α) ^ 2 := by
          rw [Finset.mul_sum]
  have hsumsq :
      ∑ α : Vec F Idx, (score α) ^ 2 ≤ (nz.card : Real) ^ 2 := by
    simpa [score, nz] using sum_linearFourierScore_sq_upperbound (F := F) (Idx := Idx) f
  have hcube_le_M :
      ((nz.card : Real)⁻¹ ^ 2) * ∑ α : Vec F Idx, (score α) ^ 3 ≤ M := by
    have hcube_bound :
        ∑ α : Vec F Idx, (score α) ^ 3 ≤ M * (nz.card : Real) ^ 2 :=
      hcube_le.trans (mul_le_mul_of_nonneg_left hsumsq hM_nonneg')
    calc
      ((nz.card : Real)⁻¹ ^ 2) * ∑ α : Vec F Idx, (score α) ^ 3 ≤
          ((nz.card : Real)⁻¹ ^ 2) * (M * (nz.card : Real) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hcube_bound (sq_nonneg _)
      _ = M := by
          field_simp [hnz_sq_ne]
  have hinner :
      1 + ((nz.card : Real)⁻¹ ^ 2) *
          ∑ α : Vec F Idx, (score α) ^ 3 ≤ 1 + M := by
    linarith
  have hq_inv_nonneg : 0 ≤ (Fintype.card F : Real)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  calc
    acceptanceProbabilityBLR f =
        (Fintype.card F : Real)⁻¹ *
          (1 + ((nz.card : Real)⁻¹ ^ 2) *
            ∑ α : Vec F Idx, (score α) ^ 3) := by
          simpa [score, nz] using exact_blr_acceptance_formula (F := F) (Idx := Idx) f
    _ ≤ (Fintype.card F : Real)⁻¹ * (1 + M) := by
          exact mul_le_mul_of_nonneg_left hinner hq_inv_nonneg
    _ = 1 - distanceToLinear f := by
          rw [distanceToLinear_fourier (F := F) (Idx := Idx) f]
          simp [M, coeffs, score]

end BLRSoundness

section FinalStatement

omit [Nonempty Idx] in
/-- The acceptance probability of the BLR test is non-negative. -/
private lemma acceptanceProbabilityBLR_nonneg (f : ScalarFn F Idx) :
    0 ≤ acceptanceProbabilityBLR f := by
  classical
  unfold acceptanceProbabilityBLR
  positivity

/-- The finite-field BLR acceptance probability is sandwiched between
completeness for linear functions and the soundness bound from distance to linearity. -/
theorem blr (f : ScalarFn F Idx) :
    (if f ∈ LinearSet (F := F) (Idx := Idx) then 1 else 0) ≤ acceptanceProbabilityBLR f ∧
      acceptanceProbabilityBLR f ≤ 1 - distanceToLinear f := by
  constructor
  · by_cases hf : f ∈ LinearSet (F := F) (Idx := Idx)
    · rw [if_pos hf, blr_completeness (F := F) (Idx := Idx) hf]
    · rw [if_neg hf]
      exact acceptanceProbabilityBLR_nonneg (F := F) (Idx := Idx) f
  · exact blr_soundness (F := F) (Idx := Idx) f

end FinalStatement

end BlrPcp
