import Mathlib

noncomputable def qPochhammerInf {R : Type*} [TopologicalSpace R] [CommRing R] (a q : R) : R :=
  ∏'[SummationFilter.conditional ℕ] i, (1 - a * q ^ i)

abbrev R := PowerSeries (LaurentPolynomial ℤ)

noncomputable abbrev a : R := .C (.T 1)
noncomputable abbrev aI : R := .C (.T (-1))
noncomputable abbrev q : R := .X

instance : UniformSpace (LaurentPolynomial ℤ) := ⊥

open scoped PowerSeries.WithPiTopology in
noncomputable def lhs : R :=
  qPochhammerInf (q ^ 2) (q ^ 2) * qPochhammerInf (-q * a) (q ^ 2) *
    qPochhammerInf (-q * aI) (q ^ 2)

open scoped PowerSeries.WithPiTopology in
noncomputable def rhs : R :=
  ∑' m : ℤ, .C (.T m) * q ^ m.natAbs ^ 2

noncomputable abbrev ι : R →+* HahnSeries ℤ (LaurentPolynomial ℤ) :=
  HahnSeries.ofPowerSeries ℤ (LaurentPolynomial ℤ)

noncomputable def qPoch {R' : Type*} [CommRing R'] (A Q : R') (n : ℕ) : R' :=
  ∏ i ∈ Finset.range n, (1 - A * Q ^ i)

noncomputable def piTop : TopologicalSpace R :=
  PowerSeries.WithPiTopology.instTopologicalSpace (LaurentPolynomial ℤ)

open PowerSeries

noncomputable def qBinom (Q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinom Q n k + Q ^ (k + 1) * qBinom Q n (k + 1)

lemma qBinom_eq_zero_of_lt (Q : R) : ∀ {n k : ℕ}, n < k → qBinom Q n k = 0
  | 0, _ + 1, _ => by simp [qBinom]
  | _ + 1, 0, h => by omega
  | n + 1, k + 1, h => by
    rw [qBinom, qBinom_eq_zero_of_lt Q (by omega : n < k),
        qBinom_eq_zero_of_lt Q (by omega : n < k + 1)]
    simp

@[simp] lemma qBinom_self (Q : R) : ∀ n, qBinom Q n n = 1
  | 0 => rfl
  | n + 1 => by
    rw [qBinom, qBinom_self Q n, qBinom_eq_zero_of_lt Q (by omega)]
    simp

lemma qPoch_succ {R' : Type*} [CommRing R'] (A Q : R') (n : ℕ) :
    qPoch A Q (n + 1) = (1 - A) * qPoch (A * Q) Q n := by
  simp only [qPoch]
  rw [Finset.prod_range_succ']
  simp only [pow_zero, mul_one]
  rw [mul_comm]
  exact congr_arg ((1 - A) * ·) (Finset.prod_congr rfl fun i _ => by ring)

lemma distribute_one_sub_A (A Q : R) (n : ℕ) :
    (1 - A) * ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ k * Q ^ k * Q ^ k.choose 2 =
    ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ k * Q ^ k * Q ^ k.choose 2 +
    ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 := by
  rw [show (1 - A) = 1 + (-A) by ring, add_mul, one_mul]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by
    rw [show (k + 1).choose 2 = k + k.choose 2 by simp [Nat.choose_succ_succ],
        pow_add, ← pow_add, pow_succ']
    ring

lemma split_S1 (A Q : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ k * Q ^ k * Q ^ k.choose 2 =
    1 + ∑ k ∈ Finset.range n,
      qBinom Q n (k + 1) * (-A) ^ (k + 1) * Q ^ (k + 1) * Q ^ (k + 1).choose 2 := by
  rw [Finset.sum_range_succ', show qBinom Q n 0 * (-A) ^ 0 * Q ^ 0 * Q ^ (0 : ℕ).choose 2 = 1
    by simp [qBinom], add_comm]

lemma split_S2 (A Q : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 =
    (∑ k ∈ Finset.range n,
      qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2) +
    (-A) ^ (n + 1) * Q ^ (n + 1).choose 2 := by
  rw [Finset.sum_range_succ]
  simp [qBinom_self]

lemma combine_summand (A Q : R) (n k : ℕ) :
    qBinom Q n (k + 1) * (-A) ^ (k + 1) * Q ^ (k + 1) * Q ^ (k + 1).choose 2 +
    qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 =
    qBinom Q (n + 1) (k + 1) * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 := by
  show _ = (qBinom Q n k + Q ^ (k + 1) * qBinom Q n (k + 1)) * _ * _
  ring

lemma combine_inner_sums (A Q : R) (n : ℕ) :
    (∑ k ∈ Finset.range n,
      qBinom Q n (k + 1) * (-A) ^ (k + 1) * Q ^ (k + 1) * Q ^ (k + 1).choose 2) +
    (∑ k ∈ Finset.range n,
      qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2) =
    ∑ k ∈ Finset.range n,
      qBinom Q (n + 1) (k + 1) * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => combine_summand A Q n k

lemma reassemble_sum (A Q : R) (n : ℕ) :
    1 + ∑ k ∈ Finset.range n,
      qBinom Q (n + 1) (k + 1) * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 +
    (-A) ^ (n + 1) * Q ^ (n + 1).choose 2 =
    ∑ k ∈ Finset.range (n + 2), qBinom Q (n + 1) k * (-A) ^ k * Q ^ k.choose 2 := by
  rw [Finset.sum_range_succ]
  simp only [qBinom_self, one_mul]
  rw [Finset.sum_range_succ']
  simp only [qBinom, pow_zero, one_mul]
  norm_num
  ring

lemma combine_sums (A Q : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ k * Q ^ k * Q ^ k.choose 2 +
    ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 =
    ∑ k ∈ Finset.range (n + 2), qBinom Q (n + 1) k * (-A) ^ k * Q ^ k.choose 2 := by
  rw [split_S1, split_S2]
  set S1' := ∑ k ∈ Finset.range n,
    qBinom Q n (k + 1) * (-A) ^ (k + 1) * Q ^ (k + 1) * Q ^ (k + 1).choose 2
  set S2' := ∑ k ∈ Finset.range n,
    qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2
  set last := (-A) ^ (n + 1) * Q ^ (n + 1).choose 2
  rw [show 1 + S1' + (S2' + last) = 1 + (S1' + S2') + last by ring, combine_inner_sums]
  exact reassemble_sum A Q n

lemma qBinom_theorem_succ (A Q : R) (n : ℕ)
    (ih : ∀ (A' : R), qPoch A' Q n =
      ∑ k ∈ Finset.range (n + 1), qBinom Q n k * (-A') ^ k * Q ^ k.choose 2) :
    qPoch A Q (n + 1) =
    ∑ k ∈ Finset.range (n + 2), qBinom Q (n + 1) k * (-A) ^ k * Q ^ k.choose 2 := by
  rw [qPoch_succ, ih (A * Q)]
  have key : ∀ k, qBinom Q n k * (-(A * Q)) ^ k * Q ^ k.choose 2 =
      qBinom Q n k * (-A) ^ k * Q ^ k * Q ^ k.choose 2 := by
    intro k
    rw [show -(A * Q) = -A * Q from (neg_mul A Q).symm, mul_pow]
    ring
  simp_rw [key]
  rw [distribute_one_sub_A, combine_sums]

lemma qBinom_theorem (A Q : R) (n : ℕ) :
    qPoch A Q n =
    ∑ k ∈ Finset.range (n + 1), qBinom Q n k * (-A) ^ k * Q ^ k.choose 2 := by
  induction n generalizing A with
  | zero => simp [qPoch, qBinom]
  | succ n ih => exact qBinom_theorem_succ A Q n ih

lemma order_q_pow_ge (m : ℕ) : (m : ℕ∞) ≤ (q ^ m : R).order := by simp

lemma order_lower_bound (x : R) (i : ℕ) :
    (-x * q).order + 2 * i ≤ ((-x * q) * (q ^ 2) ^ i).order :=
  calc (-x * q).order + 2 * (i : ℕ∞)
      _ ≤ (-x * q).order + (q ^ (2 * i) : R).order := by
          gcongr
          exact order_q_pow_ge (2 * i)
      _ ≤ (-x * q).order + ((q ^ 2) ^ i : R).order := by rw [pow_mul]
      _ ≤ _ := PowerSeries.order_mul_ge _ _

lemma enat_two_mul_tendsto_top :
    Filter.Tendsto (fun i : ℕ => 2 * (i : ℕ∞)) Filter.atTop (nhds ⊤) := by
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro n
  filter_upwards [Filter.eventually_ge_atTop (n + 1)] with i hi
  exact ENat.coe_lt_coe.mpr (by nlinarith)

lemma enat_add_two_mul_tendsto_top (c : ℕ∞) :
    Filter.Tendsto (fun i : ℕ => c + 2 * (i : ℕ∞)) Filter.atTop (nhds ⊤) :=
  tendsto_nhds_top_mono' enat_two_mul_tendsto_top
    (fun _ => le_add_of_nonneg_left (zero_le c))

lemma order_neg_factor_tendsto_top (x : R) : letI := piTop;
    Filter.Tendsto (fun i => ((-x * q) * (q ^ 2) ^ i).order) Filter.atTop (nhds ⊤) :=
  tendsto_nhds_top_mono' (enat_add_two_mul_tendsto_top (-x * q).order)
    (fun i => order_lower_bound x i)

lemma order_neg_q_aI_tendsto_top :
    Filter.Tendsto (fun n => ((-q * aI) * (q ^ 2) ^ n).order) Filter.atTop (nhds ⊤) := by
  simp_rw [show (-q * aI : R) = -aI * q by ring]
  exact tendsto_nhds_top_mono'
    (enat_add_two_mul_tendsto_top ((-aI * q).order)) (fun i => order_lower_bound aI i)

lemma factors_multipliable (x : R) : letI := piTop;
    Multipliable (fun i => 1 - (-x * q) * (q ^ 2) ^ i : ℕ → R) := by
  letI := piTop
  rw [show (fun i => 1 - (-x * q) * (q ^ 2) ^ i : ℕ → R) =
      (fun i => 1 + (-((-x * q) * (q ^ 2) ^ i))) from funext fun i => by ring_nf]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  simp_rw [PowerSeries.order_neg]
  exact order_neg_factor_tendsto_top x

lemma qPochhammerInf_eq_tprod (a Q : R)
    (hm : letI := piTop; Multipliable (fun n ↦ 1 - a * Q ^ n)) : letI := piTop;
    qPochhammerInf a Q = ∏' n, (1 - a * Q ^ n) := by
  letI := piTop
  haveI : T2Space R := PowerSeries.WithPiTopology.instT2Space _
  exact tprod_eq_of_multipliable_unconditional hm

lemma qPoch_split (A Q : R) (n k : ℕ) :
    qPoch A Q (n + k) = qPoch A Q n * qPoch (A * Q ^ n) Q k := by
  rw [qPoch, qPoch, qPoch, Finset.prod_range_add]
  simp [pow_add, mul_assoc]

lemma factor_coeff_eq_ite (x : R) (j i : ℕ) (hji : j < 1 + 2 * i) :
    (1 - (-x * q) * (q ^ 2) ^ i : R).coeff j = if j = 0 then 1 else 0 := by
  have h_key : ∀ (x : R) (k : ℕ), j < k → (x * q ^ k).coeff j = 0 :=
    fun _ _ h => by grind only [coeff_mul_X_pow']
  have h_expr : (-x * q : R) * (q ^ 2 : R) ^ i = -x * (q : R) ^ (2 * i + 1 : ℕ) := by ring
  simp_all [show j < 2 * i + 1 by nlinarith]

lemma antidiag_sum_eq (f g : R) (m : ℕ)
    (hg : ∀ j ≤ m, g.coeff j = if j = 0 then 1 else 0) :
    ∑ p ∈ Finset.antidiagonal m, f.coeff p.1 * g.coeff p.2 = f.coeff m := by
  rw [Finset.sum_eq_single_of_mem (m, 0)
    (Finset.mem_antidiagonal.mpr (add_zero m))
    (fun b hb hne => ?_)]
  · simp [hg 0 (Nat.zero_le m)]
  · have hb_sum := Finset.mem_antidiagonal.mp hb
    rw [hg b.2 (by omega), if_neg (fun h => hne (by ext <;> simp_all)), mul_zero]

lemma tail_factor_delta (x : R) (m n : ℕ) (hmn : m < n) (i : ℕ)
    (j : ℕ) (hj : j ≤ m) :
    ((1 - ((-x * q) * (q ^ 2) ^ n) * (q ^ 2) ^ i : R)).coeff j =
    if j = 0 then 1 else 0 := by
  rw [show ((-x * q) * (q ^ 2) ^ n) * (q ^ 2) ^ i = (-x * q) * (q ^ 2) ^ (n + i) by ring]
  exact factor_coeff_eq_ite x j (n + i) (by omega)

lemma coeff_mul_of_trunc_one (f g : R) (m : ℕ)
    (hg : ∀ j ≤ m, g.coeff j = if j = 0 then 1 else 0) :
    (f * g).coeff m = f.coeff m := by
  rw [PowerSeries.coeff_mul]
  exact antidiag_sum_eq f g m hg

lemma prod_coeff_delta (m : ℕ) (f : ℕ → R) (k : ℕ)
    (hf : ∀ i < k, ∀ j ≤ m, (f i).coeff j = if j = 0 then 1 else 0)
    (j : ℕ) (hj : j ≤ m) :
    (∏ i ∈ Finset.range k, f i).coeff j = if j = 0 then 1 else 0 := by
  induction k with
  | zero => simp [PowerSeries.coeff_one]
  | succ k ih =>
    rw [Finset.prod_range_succ,
      coeff_mul_of_trunc_one _ _ j (fun j' hj' => hf k (Nat.lt_succ_self k) j' (le_trans hj' hj))]
    exact ih (fun i hi j' hj' => hf i (Nat.lt_succ_of_lt hi) j' hj')

lemma tail_coeff_eq_ite (x : R) (m n k : ℕ) (hmn : m < n) (j : ℕ) (hj : j ≤ m) :
    (qPoch ((-x * q) * (q ^ 2) ^ n) (q ^ 2) k : R).coeff j =
    if j = 0 then 1 else 0 := by
  unfold qPoch
  exact prod_coeff_delta m (fun i => 1 - ((-x * q) * (q ^ 2) ^ n) * (q ^ 2) ^ i) k
    (fun i _hi j hj => tail_factor_delta x m n hmn i j hj) j hj

lemma partial_prods_coeff_stable (x : R) (m n n' : ℕ) (hmn : m < n) (hnn' : n ≤ n') :
    (qPoch (-x * q) (q ^ 2) n' : R).coeff m =
    (qPoch (-x * q) (q ^ 2) n : R).coeff m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnn'
  rw [qPoch_split]
  exact coeff_mul_of_trunc_one _ _ m (tail_coeff_eq_ite x m n k hmn)

lemma coeff_tprod_eq_coeff_qPoch (x : R) (m n : ℕ) (hmn : m < n) :
    letI := piTop
    ((∏' i, (1 - (-x * q) * (q ^ 2) ^ i : R)) : R).coeff m =
    (qPoch (-x * q) (q ^ 2) n : R).coeff m := by
  letI := piTop
  exact tendsto_nhds_unique
    ((PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto
      (LaurentPolynomial ℤ) _ _ _).mp (factors_multipliable x).tendsto_prod_tprod_nat m)
    (tendsto_atTop_of_eventually_const (i₀ := n) (fun k hk =>
      partial_prods_coeff_stable x m n k hmn hk))

lemma lhs_coeff_stable (x : R) (m n : ℕ) (hmn : m < n) :
    letI := piTop
    (qPochhammerInf (-x * q) (q ^ 2) : R).coeff m =
    (qPoch (-x * q) (q ^ 2) n : R).coeff m := by
  rw [qPochhammerInf_eq_tprod (-x * q) (q ^ 2) (factors_multipliable x)]
  exact coeff_tprod_eq_coeff_qPoch x m n hmn

lemma exponent_simp (x : R) (k : ℕ) :
    (-(-x * q)) ^ k * (q ^ 2) ^ k.choose 2 = q ^ (k ^ 2) * x ^ k := by
  have h1 : k + 2 * k.choose 2 = k ^ 2 := by
    have : 2 ∣ k * (k - 1) := by
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩ <;> simp [hm] <;> ring_nf <;> omega
    rw [Nat.choose_two_right, Nat.mul_div_cancel' this]
    rcases k with _ | n
    · simp [sq]
    · simp [sq]
      ring
  rw [show (-(-x * q)) ^ k = (x * q) ^ k by simp [neg_neg], mul_pow,
      show (q ^ 2) ^ k.choose 2 = q ^ (2 * k.choose 2) by rw [← pow_mul],
      mul_assoc, ← pow_add, h1]
  ring

lemma qbinom_sum_rewrite (x : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      qBinom (q ^ 2) n k * (-(-x * q)) ^ k * (q ^ 2) ^ k.choose 2 =
    ∑ k ∈ Finset.range (n + 1),
      qBinom (q ^ 2) n k * (q ^ (k ^ 2) * x ^ k) := by
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_assoc, exponent_simp]

lemma constantCoeff_qPoch_eq_one (k : ℕ) :
    PowerSeries.constantCoeff (qPoch (q ^ 2) (q ^ 2) k : R) = 1 := by
  simp [qPoch, map_prod, map_sub, map_one, map_mul, map_pow, PowerSeries.constantCoeff_X]

lemma order_product_ge (x : R) (k : ℕ) :
    (k ^ 2 : ℕ∞) ≤ (q ^ (k ^ 2) * x ^ k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).order := by
  rw [mul_assoc]
  calc (k ^ 2 : ℕ∞) ≤ (q ^ (k ^ 2) : R).order := order_q_pow_ge _
    _ ≤ (q ^ (k ^ 2) : R).order + ((x ^ k : R).order +
        (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).order) :=
        le_add_of_nonneg_right (by positivity)
    _ ≤ _ := le_trans (by
        gcongr
        exact PowerSeries.le_order_mul ..) (PowerSeries.le_order_mul ..)

lemma tendsto_sq_enat_atTop :
    Filter.Tendsto (fun k : ℕ => (↑(k ^ 2) : ℕ∞)) Filter.atTop (nhds ⊤) := by
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro n
  filter_upwards [Filter.eventually_ge_atTop (n + 1)] with k hk
  exact_mod_cast show (n : ℕ) < k ^ 2 by nlinarith

lemma series_summable (x : R) : letI := piTop;
    Summable fun k : ℕ => q ^ (k ^ 2) * x ^ k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 :=
  PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top _
    (tendsto_nhds_top_mono' tendsto_sq_enat_atTop (fun k => order_product_ge x k))

lemma rhs_coeff_finite (x : R) (m : ℕ) : letI := piTop;
    (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m =
    ∑ k ∈ Finset.range (m + 1),
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m := by
  letI := piTop
  rw [(series_summable x).map_tsum (PowerSeries.coeff m)
    (PowerSeries.WithPiTopology.continuous_coeff _ m)]
  exact tsum_eq_sum fun k hk => by
    simp only [Finset.mem_range, not_lt] at hk
    exact PowerSeries.coeff_of_lt_order _
      (lt_of_lt_of_le (by exact_mod_cast show m < k ^ 2 by nlinarith) (order_product_ge x k))

lemma qPoch_succ' {R' : Type*} [CommRing R'] (A Q : R') (n : ℕ) :
    qPoch A Q (n + 1) = qPoch A Q n * (1 - A * Q ^ n) := by
  simp [qPoch, Finset.prod_range_succ, mul_comm]

lemma algebraic_identity (Q : R) (n k : ℕ) (hk : k < n) :
    (1 - Q * Q ^ k) + Q ^ (k + 1) * (1 - Q * Q ^ (n - (k + 1))) = 1 - Q * Q ^ n := by
  have h1 : Q ^ (k + 1) * (Q * Q ^ (n - (k + 1))) = Q ^ (n + 1) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  rw [show Q * Q ^ k = Q ^ (k + 1) by rw [← pow_succ'],
    show Q * Q ^ n = Q ^ (n + 1) by rw [← pow_succ'],
    show Q ^ (k + 1) * (1 - Q * Q ^ (n - (k + 1))) = Q ^ (k + 1) - Q ^ (n + 1) by
      rw [mul_sub, mul_one, h1]]
  ring

lemma ring_rearrangement (Q : R) (n k : ℕ)
    (P_n P_k P_nk1 a b : R)
    (ih1 : a * P_k * (P_nk1 * (1 - Q * Q ^ (n - (k + 1)))) = P_n)
    (ih2 : b * (P_k * (1 - Q * Q ^ k)) * P_nk1 = P_n)
    (h_alg : (1 - Q * Q ^ k) + Q ^ (k + 1) * (1 - Q * Q ^ (n - (k + 1))) = 1 - Q * Q ^ n) :
    (a + Q ^ (k + 1) * b) *
      (P_k * (1 - Q * Q ^ k)) *
      (P_nk1 * (1 - Q * Q ^ (n - (k + 1)))) =
    P_n * (1 - Q * Q ^ n) := by
  grind

lemma qBinom_mul_qPoch_core (Q : R) (n k : ℕ) (hk : k < n)
    (ih1 : qBinom Q n k * qPoch Q Q k * qPoch Q Q (n - k) = qPoch Q Q n)
    (ih2 : qBinom Q n (k + 1) * qPoch Q Q (k + 1) * qPoch Q Q (n - (k + 1)) = qPoch Q Q n) :
    (qBinom Q n k + Q ^ (k + 1) * qBinom Q n (k + 1)) *
      (qPoch Q Q k * (1 - Q * Q ^ k)) *
      (qPoch Q Q (n - (k + 1)) * (1 - Q * Q ^ (n - (k + 1)))) =
    qPoch Q Q n * (1 - Q * Q ^ n) := by
  have h_unfold_nk : qPoch Q Q (n - k) =
      qPoch Q Q (n - (k + 1)) * (1 - Q * Q ^ (n - (k + 1))) := by
    rw [show n - k = (n - (k + 1)) + 1 by omega]
    exact qPoch_succ' Q Q (n - (k + 1))
  rw [h_unfold_nk] at ih1
  rw [qPoch_succ' Q Q k] at ih2
  exact ring_rearrangement Q n k (qPoch Q Q n) (qPoch Q Q k) (qPoch Q Q (n - (k + 1)))
    (qBinom Q n k) (qBinom Q n (k + 1)) ih1 ih2 (algebraic_identity Q n k hk)

lemma qBinom_mul_qPoch_inductive_step (Q : R) (n k : ℕ) (hk : k < n)
    (ih1 : qBinom Q n k * qPoch Q Q k * qPoch Q Q (n - k) = qPoch Q Q n)
    (ih2 : qBinom Q n (k + 1) * qPoch Q Q (k + 1) * qPoch Q Q (n - (k + 1)) = qPoch Q Q n) :
    qBinom Q (n + 1) (k + 1) * qPoch Q Q (k + 1) * qPoch Q Q (n - k) = qPoch Q Q (n + 1) := by
  show (qBinom Q n k + Q ^ (k + 1) * qBinom Q n (k + 1)) *
    qPoch Q Q (k + 1) * qPoch Q Q (n - k) = qPoch Q Q (n + 1)
  rw [qPoch_succ' Q Q n, qPoch_succ' Q Q k,
      show n - k = (n - (k + 1)) + 1 by omega, qPoch_succ' Q Q (n - (k + 1))]
  exact qBinom_mul_qPoch_core Q n k hk ih1 ih2

lemma qBinom_mul_qPoch (Q : R) (n k : ℕ) (hkn : k ≤ n) :
    qBinom Q n k * qPoch Q Q k * qPoch Q Q (n - k) = qPoch Q Q n := by
  induction n generalizing k with
  | zero =>
    obtain rfl := Nat.le_zero.mp hkn
    simp [qPoch, qBinom]
  | succ n ih =>
    match k, hkn with
    | 0, _ => simp [qBinom, qPoch]
    | k + 1, hkn =>
      have hkn' := Nat.succ_le_succ_iff.mp hkn
      obtain rfl | hk := eq_or_lt_of_le hkn'
      · simp [qBinom_self, qPoch]
      · rw [Nat.succ_sub_succ]
        exact qBinom_mul_qPoch_inductive_step Q n k hk (ih k hk.le) (ih (k + 1) hk)

lemma factor_coeff_eq_delta (m d : ℕ) (hd : m + 2 ≤ d) (j : ℕ) (hj : j ≤ m) :
    ((1 - (q : R) ^ (2 * d)) : R).coeff j = if j = 0 then 1 else 0 := by
  have h1 : ((q : R) ^ (2 * d)).coeff j = 0 := by
    have : j < 2 * d := by nlinarith
    grind only [coeff_X_pow]
  simp_all

lemma tail_qPoch_coeff_eq_ite (m k n : ℕ) (hn : m + k + 1 ≤ n) (j : ℕ) (hj : j ≤ m) :
    (qPoch (q ^ 2 * (q ^ 2) ^ (n - k)) (q ^ 2) k : R).coeff j =
    if j = 0 then 1 else 0 := by
  apply prod_coeff_delta m (fun i => 1 - q ^ 2 * (q ^ 2) ^ (n - k) * (q ^ 2) ^ i) k _ j hj
  intro i hi j' hj'
  show ((1 - q ^ 2 * (q ^ 2) ^ (n - k) * (q ^ 2) ^ i : R)).coeff j' = _
  rw [show q ^ 2 * (q ^ 2) ^ (n - k) * (q ^ 2) ^ i = (q : R) ^ (2 * (n - k + 1 + i)) by
    rw [← pow_mul q 2, ← pow_add, ← pow_mul q 2, ← pow_add]
    congr 1
    omega]
  exact factor_coeff_eq_delta m (n - k + 1 + i) (by omega) j' hj'

lemma coeff_tail_mul_inv (m k n : ℕ) (hn : m + k + 1 ≤ n) :
    (qPoch (q ^ 2 * (q ^ 2) ^ (n - k)) (q ^ 2) k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m =
    (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m := by
  rw [mul_comm]
  exact coeff_mul_of_trunc_one _ _ _ (tail_qPoch_coeff_eq_ite m k n hn)

lemma order_qpow_mul_xpow_ge (x : R) (k : ℕ) :
    (k ^ 2 : ℕ∞) ≤ (q ^ (k ^ 2) * x ^ k : R).order :=
  le_trans (le_trans (order_q_pow_ge _) (le_add_of_nonneg_right (zero_le _))) (PowerSeries.order_mul_ge _ _)

lemma lhs_term_vanishes_of_gt (x : R) (m k : ℕ) (hk : m < k) :
    (qBinom (q ^ 2) (2 * m + 1) k * (q ^ (k ^ 2) * x ^ k) : R).coeff m = 0 := by
  apply PowerSeries.coeff_of_lt_order
  calc (m : ℕ∞) < k ^ 2 := by exact_mod_cast (show m < k ^ 2 by nlinarith)
    _ ≤ 0 + (k ^ 2 : ℕ∞) := by simp
    _ ≤ (qBinom (q ^ 2) (2 * m + 1) k).order + (q ^ (k ^ 2) * x ^ k : R).order :=
        add_le_add bot_le (order_qpow_mul_xpow_ge x k)
    _ ≤ _ := PowerSeries.order_mul_ge _ _

lemma qPoch_mul_invOfUnit_cancel (k : ℕ) :
    qPoch (q ^ 2) (q ^ 2) k * PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 = 1 :=
  PowerSeries.mul_invOfUnit _ 1 (by simp [constantCoeff_qPoch_eq_one])

lemma isUnit_qPoch (m : ℕ) : IsUnit (qPoch (q ^ 2) (q ^ 2) m : R) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_qPoch_eq_one]
  exact isUnit_one

lemma qBinom_mul_qPoch_k (n k : ℕ) (hkn : k ≤ n) :
    qBinom (q ^ 2) n k * qPoch (q ^ 2) (q ^ 2) k =
    qPoch (q ^ 2 * (q ^ 2) ^ (n - k)) (q ^ 2) k := by
  have h1 := qBinom_mul_qPoch (q ^ 2) n k hkn
  have h2 := qPoch_split (q ^ 2) (q ^ 2) (n - k) k
  rw [Nat.sub_add_cancel hkn] at h2
  rw [h2] at h1
  exact (isUnit_qPoch (n - k)).mul_right_cancel (by linear_combination h1)

lemma qBinom_eq_tail_mul_inv (n k : ℕ) (hkn : k ≤ n) :
    qBinom (q ^ 2) n k =
    qPoch (q ^ 2 * (q ^ 2) ^ (n - k)) (q ^ 2) k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 := by
  have h := qBinom_mul_qPoch_k n k hkn
  rw [show qBinom (q ^ 2) n k = qBinom (q ^ 2) n k * qPoch (q ^ 2) (q ^ 2) k *
    PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 by
    rw [mul_assoc, qPoch_mul_invOfUnit_cancel, mul_one], h]

lemma qBinom_coeff_eq_invOfUnit (m k n : ℕ) (_ : k ≤ m) (hn : m + k + 1 ≤ n) :
    (qBinom (q ^ 2) n k : R).coeff m =
    (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m := by
  rw [qBinom_eq_tail_mul_inv n k (by omega)]
  exact coeff_tail_mul_inv m k n hn

lemma qBinom_coeff_eq_invOfUnit_small (m k i : ℕ) (hk : k ≤ m) (hi : i < k)
    (_him : i ≤ m) :
    (qBinom (q ^ 2) (2 * m + 1) k : R).coeff i =
    (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff i := by
  rw [qBinom_eq_tail_mul_inv (2 * m + 1) k (by omega)]
  exact coeff_tail_mul_inv i k (2 * m + 1) (by omega)

lemma coeff_qBinom_eq_coeff_inv_on_antidiag (m k i j : ℕ) (hk : k ≤ m)
    (hij : i + j = m) (_hj : k ^ 2 ≤ j) :
    (qBinom (q ^ 2) (2 * m + 1) k : R).coeff i =
    (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff i := by
  by_cases hki : k ≤ i
  · exact qBinom_coeff_eq_invOfUnit i k (2 * m + 1) hki (by omega)
  · push_neg at hki
    exact qBinom_coeff_eq_invOfUnit_small m k i hk hki (by omega)

lemma conv_sum_eq (x : R) (m k : ℕ) (hk : k ≤ m) :
    ∑ p ∈ Finset.antidiagonal m,
      (qBinom (q ^ 2) (2 * m + 1) k : R).coeff p.1 * (q ^ (k ^ 2) * x ^ k).coeff p.2 =
    ∑ p ∈ Finset.antidiagonal m,
      (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff p.1 *
      (q ^ (k ^ 2) * x ^ k).coeff p.2 := by
  apply Finset.sum_congr rfl
  intro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  by_cases hj : k ^ 2 ≤ j
  · congr 1
    exact coeff_qBinom_eq_coeff_inv_on_antidiag m k i j hk hij hj
  · push_neg at hj
    rw [PowerSeries.coeff_of_lt_order j (lt_of_lt_of_le (by exact_mod_cast hj)
      (order_qpow_mul_xpow_ge x k)), mul_zero, mul_zero]

lemma termwise_coeff_eq (x : R) (m k : ℕ) (hk : k ≤ m) :
    (qBinom (q ^ 2) (2 * m + 1) k * (q ^ (k ^ 2) * x ^ k) : R).coeff m =
    (q ^ (k ^ 2) * x ^ k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m := by
  rw [mul_comm (q ^ (k ^ 2) * x ^ k), PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  exact conv_sum_eq x m k hk

lemma finite_sums_agree (x : R) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 1 + 1),
      (qBinom (q ^ 2) (2 * m + 1) k * (q ^ (k ^ 2) * x ^ k) : R).coeff m =
    ∑ k ∈ Finset.range (m + 1),
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m := by
  rw [show 2 * m + 1 + 1 = (m + 1) + (m + 1) by omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero fun k _ => lhs_term_vanishes_of_gt x m ((m + 1) + k) (by omega), add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  exact termwise_coeff_eq x m k (by omega)

lemma euler_product_coeff (x : R) (m : ℕ) :
    letI := piTop
    (qPochhammerInf (-x * q) (q ^ 2) : R).coeff m =
    (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m := by
  letI := piTop
  rw [lhs_coeff_stable x m (2 * m + 1) (by omega), rhs_coeff_finite,
    qBinom_theorem (-x * q) (q ^ 2) (2 * m + 1), qbinom_sum_rewrite, map_sum]
  exact finite_sums_agree x m

lemma euler_product (x : R) : letI := piTop;
    qPochhammerInf (-x * q) (q ^ 2) =
    ∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 :=
  PowerSeries.ext fun m => euler_product_coeff x m

abbrev S := PowerSeries R
noncomputable abbrev t : S := PowerSeries.X
noncomputable abbrev CS : R →+* S := PowerSeries.C (R := R)
noncomputable abbrev P (m : ℕ) : R := qPoch (q ^ 2) (q ^ 2) m

noncomputable def aCoeff (ℓ : ℕ) : R :=
  (-1) ^ ℓ * PowerSeries.invOfUnit (P ℓ) 1

noncomputable def bCoeff (k : ℕ) : R :=
  (q ^ 2) ^ k.choose 2 * PowerSeries.invOfUnit (P k) 1

noncomputable def piTopS : TopologicalSpace S :=
  @PowerSeries.WithPiTopology.instTopologicalSpace R piTop

noncomputable def A_S : S := letI := piTopS; ∑' ℓ, CS (aCoeff ℓ) * t ^ ℓ

noncomputable def B_S : S := letI := piTopS; ∑' k, CS (bCoeff k) * t ^ k

lemma hasSum_CS_mul_t_pow (c : ℕ → R) :
    letI := piTopS
    HasSum (fun k => CS (c k) * t ^ k) (PowerSeries.mk c) := by
  letI : TopologicalSpace R := piTop
  letI : TopologicalSpace S := piTopS
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  simp only [PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_mk]
  convert hasSum_ite_eq d (c d) using 1
  ext k
  split_ifs <;> simp_all

lemma coeff_tsum_CS_mul_t_pow (c : ℕ → R) (n : ℕ) :
    @PowerSeries.coeff R _ n (letI := piTopS; ∑' k, CS (c k) * t ^ k) = c n := by
  letI := piTopS
  haveI : T2Space S := @PowerSeries.WithPiTopology.instT2Space R piTop
    (@PowerSeries.WithPiTopology.instT2Space (LaurentPolynomial ℤ) ⊥ inferInstance)
  rw [(hasSum_CS_mul_t_pow c).tsum_eq, PowerSeries.coeff_mk]

lemma qPoch_one_eq_zero (Q : R) {n : ℕ} (hn : 0 < n) : qPoch 1 Q n = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.mpr hn) (by simp)

lemma constantCoeff_P_eq_one (k : ℕ) :
    PowerSeries.constantCoeff (P k) = 1 :=
  by simp [P, qPoch, map_prod, map_sub, map_mul, map_pow, PowerSeries.constantCoeff_X]

lemma inv_product_eq_qBinom_mul_inv {n k : ℕ} (hkn : k ≤ n) :
    PowerSeries.invOfUnit (P (n - k)) 1 * PowerSeries.invOfUnit (P k) 1 =
    qBinom (q ^ 2) n k * PowerSeries.invOfUnit (P n) 1 := by
  have hP_unit : ∀ m, IsUnit (P m) :=
    fun m ↦ PowerSeries.isUnit_iff_constantCoeff.mpr
      (by rw [constantCoeff_P_eq_one]; exact isUnit_one)
  have hcancel : ∀ m, PowerSeries.invOfUnit (P m) 1 * P m = 1 :=
    fun m ↦ PowerSeries.invOfUnit_mul _ _ (by rw [constantCoeff_P_eq_one]; rfl)
  apply (hP_unit k).mul (hP_unit (n - k)) |>.mul_right_cancel
  calc PowerSeries.invOfUnit (P (n - k)) 1 * PowerSeries.invOfUnit (P k) 1 *
      (P k * P (n - k))
      = PowerSeries.invOfUnit (P (n - k)) 1 * (PowerSeries.invOfUnit (P k) 1 * P k) *
          P (n - k) := by ring
    _ = 1 := by rw [hcancel k, mul_one, hcancel (n - k)]
    _ = qBinom (q ^ 2) n k * P k * P (n - k) * PowerSeries.invOfUnit (P n) 1 := by
          rw [qBinom_mul_qPoch _ _ _ hkn, qPoch_mul_invOfUnit_cancel n]
    _ = qBinom (q ^ 2) n k * PowerSeries.invOfUnit (P n) 1 *
          (P k * P (n - k)) := by ring

lemma summand_eq {n k : ℕ} (hkn : k ≤ n) :
    aCoeff (n - k) * bCoeff k =
    (-1) ^ n * PowerSeries.invOfUnit (P n) 1 *
      (qBinom (q ^ 2) n k * (-(1 : R)) ^ k * (q ^ 2) ^ k.choose 2) := by
  simp only [aCoeff, bCoeff]
  rw [show (-(1 : R)) ^ k = (-1 : R) ^ k by ring]
  conv_lhs => rw [show (-1 : R) ^ (n - k) * PowerSeries.invOfUnit (P (n - k)) 1 *
      ((q ^ 2) ^ k.choose 2 * PowerSeries.invOfUnit (P k) 1) =
      (-1) ^ (n - k) * (q ^ 2) ^ k.choose 2 *
        (PowerSeries.invOfUnit (P (n - k)) 1 * PowerSeries.invOfUnit (P k) 1) by ring]
  rw [inv_product_eq_qBinom_mul_inv hkn]
  have hkk : (-1 : R) ^ k * (-1) ^ k = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨k, rfl⟩
  rw [show (-1 : R) ^ (n - k) = (-1) ^ n * (-1) ^ k by
    calc (-1 : R) ^ (n - k) = (-1) ^ (n - k) * ((-1) ^ k * (-1) ^ k) := by rw [hkk, mul_one]
      _ = _ := by rw [← mul_assoc,
          show (-1 : R) ^ (n - k) * (-1) ^ k = (-1) ^ n from
            (pow_add (-1 : R) (n - k) k).symm ▸ congrArg ((-1 : R) ^ ·) (by omega)]]
  ring

lemma antidiag_to_range_sum {n : ℕ} :
    ∑ p ∈ Finset.antidiagonal n, aCoeff p.1 * bCoeff p.2 =
    ∑ k ∈ Finset.range (n + 1), aCoeff (n - k) * bCoeff k := by
  have h1 : ∑ p ∈ Finset.antidiagonal n, aCoeff p.1 * bCoeff p.2 =
      ∑ p ∈ Finset.antidiagonal n, aCoeff p.2 * bCoeff p.1 :=
    Finset.Nat.sum_antidiagonal_swap (f := fun p => aCoeff p.2 * bCoeff p.1)
  rw [h1]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => aCoeff b * bCoeff a) n

lemma sum_eq_factored {n : ℕ} :
    ∑ p ∈ Finset.antidiagonal n, aCoeff p.1 * bCoeff p.2 =
    (-1) ^ n * PowerSeries.invOfUnit (P n) 1 *
    ∑ k ∈ Finset.range (n + 1),
      qBinom (q ^ 2) n k * (-(1 : R)) ^ k * (q ^ 2) ^ k.choose 2 := by
  rw [antidiag_to_range_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  exact summand_eq (by simp only [Finset.mem_range] at hk; omega)

lemma convolution_eq_zero {n : ℕ} (hn : 0 < n) :
    ∑ p ∈ Finset.antidiagonal n,
      aCoeff p.1 * bCoeff p.2 = 0 := by
  rw [sum_eq_factored, show ∑ k ∈ Finset.range (n + 1),
      qBinom (q ^ 2) n k * (-(1 : R)) ^ k * (q ^ 2) ^ k.choose 2 = qPoch 1 (q ^ 2) n
      from (qBinom_theorem 1 (q ^ 2) n).symm,
    qPoch_one_eq_zero _ hn, mul_zero]

lemma AB_eq_one_in_S : A_S * B_S = 1 := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one]
  simp_rw [show ∀ n, @PowerSeries.coeff R _ n A_S = aCoeff n from coeff_tsum_CS_mul_t_pow aCoeff,
    show ∀ n, @PowerSeries.coeff R _ n B_S = bCoeff n from coeff_tsum_CS_mul_t_pow bCoeff]
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp [Finset.antidiagonal_zero, aCoeff, bCoeff, P, qPoch,
      show PowerSeries.invOfUnit (1 : R) 1 = 1 by
        have := PowerSeries.invOfUnit_mul (1 : R) 1 (by simp)
        rwa [mul_one] at this]
  · rw [if_neg (by omega), convolution_eq_zero hn]

noncomputable def eval_x_fun (x : R) : S → R :=
  fun p => letI := piTop; ∑' n, p.coeff n * x ^ n

lemma instIsTopologicalSemiringPiTop : @IsTopologicalSemiring R piTop _ :=
  WithPiTopology.instIsTopologicalSemiring (LaurentPolynomial ℤ)

lemma order_coeff_mul_pow_ge {x : R} (hx : x.constantCoeff = 0) (p : S) (n : ℕ) :
    (n : ℕ∞) ≤ ((p.coeff n) * x ^ n).order := by
  have h1 : (1 : ℕ∞) ≤ x.order :=
    ENat.one_le_iff_ne_zero.mpr (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mpr hx)
  calc (n : ℕ∞) = n • (1 : ℕ∞) := by simp
    _ ≤ n • x.order := nsmul_le_nsmul_right h1 n
    _ ≤ (x ^ n).order := PowerSeries.le_order_pow x n
    _ ≤ _ := le_trans le_add_self (PowerSeries.order_mul_ge _ _)

lemma order_tendsto_top {x : R} (hx : x.constantCoeff = 0) (p : S) :
    Filter.Tendsto (fun n : ℕ => ((p.coeff n) * x ^ n).order) Filter.atTop (nhds ⊤) := by
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro k
  rw [Filter.eventually_atTop]
  exact ⟨k + 1, fun m hm => lt_of_lt_of_le
    (by exact_mod_cast (by omega : k < m)) (order_coeff_mul_pow_ge hx p m)⟩

lemma summable_eval_series {x : R} (hx : x.constantCoeff = 0) (p : S) :
    letI := piTop; Summable (fun n => p.coeff n * x ^ n) :=
  PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top _
    (order_tendsto_top hx p)

lemma laurentPoly_T3 :
    @T3Space (LaurentPolynomial ℤ) ((⊥ : UniformSpace (LaurentPolynomial ℤ)).toTopologicalSpace) :=
  { toT0Space := T4Space.instT35Space.toT0Space,
    toRegularSpace := CompletelyRegularSpace.instRegularSpace }

lemma piTop_T3 : @T3Space R piTop :=
  @instT3SpaceForall (Unit →₀ ℕ) (fun _ => LaurentPolynomial ℤ)
    (fun _ => (⊥ : UniformSpace (LaurentPolynomial ℤ)).toTopologicalSpace) (fun _ => laurentPoly_T3)

lemma tendsto_natCast_enat_atTop :
    Filter.Tendsto (fun n : ℕ => (n : ℕ∞)) Filter.atTop (nhds ⊤) := by
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro n
  filter_upwards [Filter.eventually_ge_atTop (n + 1)] with b hb
  exact ENat.coe_lt_coe.mpr (by omega)

lemma exists_bound_for_order
    {f : ℕ → ℕ∞} (hf : Filter.Tendsto f Filter.atTop (nhds ⊤)) (d : ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n → (d : ℕ∞) < f n :=
  (ENat.tendsto_nhds_top_iff_natCast_lt.mp hf d).exists_forall_of_atTop

lemma coeff_mul_eq_zero_of_order_gt {d : ℕ} {φ ψ : R}
    (h : (d : ℕ∞) < φ.order ∨ (d : ℕ∞) < ψ.order) :
    (PowerSeries.coeff d) (φ * ψ) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  calc (d : ℕ∞) < φ.order + ψ.order := by
        rcases h with h | h
        · exact lt_of_lt_of_le h (le_add_of_nonneg_right (zero_le _))
        · exact lt_of_lt_of_le h (le_add_of_nonneg_left (zero_le _))
    _ ≤ (φ * ψ).order := PowerSeries.order_mul_ge φ ψ

lemma summable_coeff_product_term {x : R} (hx : x.constantCoeff = 0)
    (p q : S) (d : ℕ) :
    Summable (fun (kl : ℕ × ℕ) =>
      (PowerSeries.coeff d)
        ((p.coeff kl.1 * x ^ kl.1) * (q.coeff kl.2 * x ^ kl.2))) := by
  have hp := order_tendsto_top hx p
  have hq := order_tendsto_top hx q
  obtain ⟨Np, hNp⟩ := exists_bound_for_order hp d
  obtain ⟨Nq, hNq⟩ := exists_bound_for_order hq d
  apply summable_of_ne_finset_zero (s := Finset.range Np ×ˢ Finset.range Nq)
  intro ⟨k, l⟩ hkl
  simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hkl
  apply coeff_mul_eq_zero_of_order_gt
  rcases hkl with hk | hl
  · exact Or.inl (hNp k hk)
  · exact Or.inr (hNq l hl)

lemma summable_product_term {x : R} (hx : x.constantCoeff = 0) (p q : S) :
    letI := piTop;
    Summable (fun (kl : ℕ × ℕ) => (p.coeff kl.1 * x ^ kl.1) * (q.coeff kl.2 * x ^ kl.2)) := by
  letI := piTop
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  exact summable_coeff_product_term hx p q d

lemma eval_x_mul (x : R) (hx : x.constantCoeff = 0) (p q : S) :
    eval_x_fun x (p * q) = eval_x_fun x p * eval_x_fun x q := by
  show (letI := piTop; ∑' n, (p * q).coeff n * x ^ n) =
    (letI := piTop; ∑' n, p.coeff n * x ^ n) * (letI := piTop; ∑' n, q.coeff n * x ^ n)
  letI : TopologicalSpace R := piTop
  haveI : T3Space R := piTop_T3
  haveI : IsTopologicalSemiring R := instIsTopologicalSemiringPiTop
  rw [(summable_eval_series hx p).tsum_mul_tsum_eq_tsum_sum_antidiagonal
    (summable_eval_series hx q) (summable_product_term hx p q)]
  apply tsum_congr
  intro n
  have hsimpl : ∀ kl ∈ Finset.antidiagonal n,
      (p.coeff kl.1 * x ^ kl.1) * (q.coeff kl.2 * x ^ kl.2) =
      (p.coeff kl.1 * q.coeff kl.2) * x ^ n := fun kl hkl => by
    rw [Finset.mem_antidiagonal] at hkl
    subst hkl
    rw [pow_add]
    ring
  rw [Finset.sum_congr rfl hsimpl, ← Finset.sum_mul, PowerSeries.coeff_mul]

lemma eval_x_one (x : R) (_hx : x.constantCoeff = 0) :
    eval_x_fun x 1 = 1 := by
  show letI := piTop; ∑' n, (1 : S).coeff n * x ^ n = 1
  letI := piTop
  rw [tsum_eq_single 0 (fun n hn => by rw [PowerSeries.coeff_one, if_neg hn, zero_mul])]
  simp [PowerSeries.coeff_one]

lemma eval_x_tsum_coeff (x : R) (_hx : x.constantCoeff = 0) (c : ℕ → R) :
    eval_x_fun x (letI := piTopS; ∑' n, CS (c n) * t ^ n) =
    (letI := piTop; ∑' n, c n * x ^ n) := by
  show letI := piTop; ∑' d, (letI := piTopS; ∑' n, CS (c n) * t ^ n).coeff d * x ^ d =
    ∑' n, c n * x ^ n
  letI := piTop
  congr 1
  funext d
  rw [coeff_tsum_CS_mul_t_pow c d]

lemma eval_A (x : R) (hx : x.constantCoeff = 0) : letI := piTop;
    eval_x_fun x A_S =
    ∑' ℓ, (-x) ^ ℓ * PowerSeries.invOfUnit (P ℓ) 1 := by
  show letI := piTop; eval_x_fun x A_S = ∑' ℓ, (-x) ^ ℓ * PowerSeries.invOfUnit (P ℓ) 1
  rw [show A_S = (letI := piTopS; ∑' ℓ, CS (aCoeff ℓ) * t ^ ℓ) from rfl,
      eval_x_tsum_coeff x hx aCoeff]
  letI := piTop
  refine tsum_congr fun ℓ => ?_
  simp only [aCoeff]
  set_option maxRecDepth 1024 in
  rw [show (-x) ^ ℓ = (-1 : R) ^ ℓ * x ^ ℓ from neg_one_mul x ▸ mul_pow (-1) x ℓ]
  ring

lemma eval_B (x : R) (hx : x.constantCoeff = 0) : letI := piTop;
    eval_x_fun x B_S = qPochhammerInf (-x) (q ^ 2) := by
  rw [show B_S = (letI := piTopS; ∑' k, CS (bCoeff k) * t ^ k) from rfl,
      eval_x_tsum_coeff x hx bCoeff]
  obtain ⟨y, hxy⟩ := PowerSeries.X_dvd_iff.mpr hx
  show letI := piTop; (∑' k, bCoeff k * x ^ k) = qPochhammerInf (-x) (q ^ 2)
  conv_rhs => rw [show (-x : R) = -y * q by rw [hxy]; ring]
  rw [euler_product y]
  letI := piTop
  refine tsum_congr fun k => ?_
  simp only [bCoeff]
  rw [hxy]
  have h := exponent_simp y k
  set_option maxRecDepth 1024 in
  rw [show (-(-y * q)) ^ k = (y * q) ^ k by simp [neg_neg]] at h
  rw [show (PowerSeries.X * y) ^ k = (y * q) ^ k by show (q * y) ^ k = _; rw [mul_comm],
      show (q ^ 2) ^ k.choose 2 * PowerSeries.invOfUnit (P k) 1 * (y * q) ^ k =
        (y * q) ^ k * (q ^ 2) ^ k.choose 2 * PowerSeries.invOfUnit (P k) 1 by ring, h]

lemma euler_inverse (x : R) (hx : x.constantCoeff = 0) : letI := piTop;
    (∑' ℓ : ℕ, (-x) ^ ℓ *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) *
    qPochhammerInf (-x) (q ^ 2) = 1 := by
  have h := eval_x_mul x hx A_S B_S
  rw [AB_eq_one_in_S, eval_x_one x hx] at h
  rw [← eval_A x hx, ← eval_B x hx]
  exact h.symm

lemma factor_shift_eq (n k : ℕ) :
    (1 : R) - q ^ 2 * (q ^ 2) ^ (n + k) = 1 - (q ^ 2 * (q ^ 2) ^ k) * (q ^ 2) ^ n := by ring

lemma multipliable_factors : letI := piTop;
    Multipliable (fun n ↦ 1 - q ^ 2 * (q ^ 2) ^ n) := by
  letI := piTop
  exact (factors_multipliable (-q) |>.congr (fun n => by simp [neg_neg]; ring))

lemma order_shifted_tendsto_top (k : ℕ) :
    Filter.Tendsto (fun n ↦ (q ^ 2 * (q ^ 2) ^ k * (q ^ 2) ^ n).order)
      Filter.atTop (nhds ⊤) := by
  apply tendsto_nhds_top_mono' (f := fun n => ((2 + 2 * k + 2 * n : ℕ) : ℕ∞))
  · exact (enat_add_two_mul_tendsto_top ((2 + 2 * k : ℕ) : ℕ∞)).congr
      (fun n => by push_cast; ring)
  · intro n
    show ((2 + 2 * k + 2 * n : ℕ) : ℕ∞) ≤ (q ^ 2 * (q ^ 2) ^ k * (q ^ 2) ^ n).order
    rw [show q ^ 2 * (q ^ 2) ^ k * (q ^ 2) ^ n = q ^ (2 + 2 * k + 2 * n) by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]]
    exact order_q_pow_ge _

lemma multipliable_shifted (k : ℕ) : letI := piTop;
    Multipliable (fun n ↦ 1 - (q ^ 2 * (q ^ 2) ^ k) * (q ^ 2) ^ n) := by
  letI := piTop
  have key : Filter.Tendsto
      (fun n ↦ (-(q ^ 2 * (q ^ 2) ^ k * (q ^ 2) ^ n)).order) Filter.atTop (nhds ⊤) := by
    simp only [PowerSeries.order_neg]
    exact order_shifted_tendsto_top k
  convert PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
    (R := LaurentPolynomial ℤ) key using 1
  ext n
  simp [sub_eq_add_neg, mul_assoc]

lemma tprod_split_eq (k : ℕ) : letI := piTop;
    (∏' n, (1 - q ^ 2 * (q ^ 2) ^ n)) =
    (∏ i ∈ Finset.range k, (1 - q ^ 2 * (q ^ 2) ^ i)) *
    (∏' n, (1 - (q ^ 2 * (q ^ 2) ^ k) * (q ^ 2) ^ n)) := by
  letI := piTop
  have hT2 : T2Space R := PowerSeries.WithPiTopology.instT2Space _
  have hCM : ContinuousMul R := instIsTopologicalSemiringPiTop.toContinuousMul
  have hshift : Multipliable (fun n ↦ (1 : R) - q ^ 2 * (q ^ 2) ^ (n + k)) :=
    (multipliable_shifted k).congr (fun n ↦ (factor_shift_eq n k).symm)
  have key := @Multipliable.prod_mul_tprod_nat_mul' R _ _ hT2 hCM
    (f := fun n ↦ 1 - q ^ 2 * (q ^ 2) ^ n) (k := k) hshift
  rw [← key]
  congr 1
  exact tprod_congr (fun n ↦ factor_shift_eq n k)

lemma qPochhammerInf_split (k : ℕ) : letI := piTop;
    qPochhammerInf (q ^ 2) (q ^ 2) =
    qPoch (q ^ 2) (q ^ 2) k *
    qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) := by
  letI := piTop
  rw [qPochhammerInf_eq_tprod _ _ multipliable_factors, tprod_split_eq k,
      qPochhammerInf_eq_tprod _ _ (multipliable_shifted k)]
  rfl

lemma per_term_simplify (x : R) (k : ℕ) : letI := piTop;
    qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) =
    q ^ (k ^ 2) * x ^ k *
      qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) := by
  letI := piTop
  rw [qPochhammerInf_split k]
  calc qPoch (q ^ 2) (q ^ 2) k * qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) *
        (q ^ k ^ 2 * x ^ k * (qPoch (q ^ 2) (q ^ 2) k).invOfUnit 1)
      = q ^ k ^ 2 * x ^ k * qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) *
        (qPoch (q ^ 2) (q ^ 2) k * (qPoch (q ^ 2) (q ^ 2) k).invOfUnit 1) := by ring
    _ = _ := by rw [qPoch_mul_invOfUnit_cancel, mul_one]

lemma product_term_coeff_vanishes (x : R) (m k : ℕ) (hk : m < k) : letI := piTop;
    (qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m = 0 := by
  apply coeff_mul_eq_zero_of_order_gt
  right
  calc (m : ℕ∞) < k := by exact_mod_cast hk
    _ ≤ k ^ 2 := by exact_mod_cast Nat.le_self_pow (by omega) k
    _ ≤ _ := order_product_ge x k

lemma summable_mul_series (x : R) : letI := piTop;
    Summable fun k : ℕ => qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) := by
  letI := piTop
  haveI := instIsTopologicalSemiringPiTop
  exact (series_summable x).mul_left _

lemma mul_tsum_eq_tsum_mul (x : R) : letI := piTop;
    (qPochhammerInf (q ^ 2) (q ^ 2) *
      (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R) =
    (∑' k : ℕ, qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R) := by
  letI := piTop
  haveI := instIsTopologicalSemiringPiTop
  haveI : @T2Space R piTop := PowerSeries.WithPiTopology.instT2Space _
  exact ((series_summable x).tsum_mul_left _).symm

lemma rhs_eq_finite_sum (x : R) (m : ℕ) : letI := piTop;
    (∑' k : ℕ, qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m =
    ∑ k ∈ Finset.range (m + 1),
      (qPochhammerInf (q ^ 2) (q ^ 2) *
        (q ^ (k ^ 2) * x ^ k *
          PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m := by
  letI := piTop
  have hcomm := (summable_mul_series x).map_tsum
    (PowerSeries.coeff m : R →ₗ[_] _).toAddMonoidHom
    (PowerSeries.WithPiTopology.continuous_coeff _ m)
  simp only [LinearMap.toAddMonoidHom_coe] at hcomm
  rw [hcomm]
  exact tsum_eq_sum (fun k hk => product_term_coeff_vanishes x m k
    (by simp only [Finset.mem_range, not_lt] at hk; omega))

lemma lhs_eq_finite_sum (x : R) (m : ℕ) : letI := piTop;
    (qPochhammerInf (q ^ 2) (q ^ 2) *
      (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m =
    ∑ k ∈ Finset.range (m + 1),
      (qPochhammerInf (q ^ 2) (q ^ 2) *
        (q ^ (k ^ 2) * x ^ k *
          PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m := by
  rw [mul_tsum_eq_tsum_mul x]
  exact rhs_eq_finite_sum x m

lemma distribute_mul_tsum_coeff (x : R) (m : ℕ) : letI := piTop;
    (qPochhammerInf (q ^ 2) (q ^ 2) *
      (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m =
    (∑' k : ℕ, qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m := by
  rw [lhs_eq_finite_sum, rhs_eq_finite_sum]

lemma tsum_coeff_congr_of_per_term (x : R) (m : ℕ) : letI := piTop;
    (∑' k : ℕ, qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m =
    (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
      qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) : R).coeff m := by
  letI := piTop
  congr 1
  exact tsum_congr (fun k => per_term_simplify x k)

lemma product_sum_expansion_coeff (x : R) (m : ℕ) : letI := piTop;
    (qPochhammerInf (q ^ 2) (q ^ 2) * qPochhammerInf (-x * q) (q ^ 2) : R).coeff m =
    (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
      qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) : R).coeff m := by
  letI := piTop
  rw [euler_product x, distribute_mul_tsum_coeff x m]
  exact tsum_coeff_congr_of_per_term x m

lemma product_sum_expansion (x : R) : letI := piTop;
    qPochhammerInf (q ^ 2) (q ^ 2) * qPochhammerInf (-x * q) (q ^ 2) =
    ∑' k : ℕ, q ^ (k ^ 2) * x ^ k * qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) :=
  PowerSeries.ext fun m => product_sum_expansion_coeff x m

lemma extract_sign (k ℓ : ℕ) :
    (-q ^ (2 * k + 1)) ^ ℓ = (-1) ^ ℓ * q ^ (ℓ * (2 * k + 1)) := by
  rw [show (-q ^ (2 * k + 1) : R) = (-1 : R) * q ^ (2 * k + 1) by ring_nf, mul_pow,
      show (q ^ (2 * k + 1)) ^ ℓ = q ^ (ℓ * (2 * k + 1)) by rw [← pow_mul]; ring_nf]

lemma expand_shifted_product (k : ℕ) : letI := piTop;
    qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) =
    ∑' ℓ : ℕ, (-1) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 := by
  letI := piTop
  rw [show q ^ 2 * (q ^ 2) ^ k = q ^ (2 + 2 * k) by ring,
      show q ^ (2 + 2 * k) = -(-q ^ (2 * k + 1)) * q by
        simp only [neg_neg]; rw [show (2 + 2 * k : ℕ) = 2 * k + 1 + 1 by omega, pow_succ],
      euler_product (-q ^ (2 * k + 1))]
  exact tsum_congr fun ℓ => by
    rw [extract_sign, show q ^ (ℓ ^ 2) * ((-1 : R) ^ ℓ * q ^ (ℓ * (2 * k + 1))) =
        (-1) ^ ℓ * (q ^ (ℓ ^ 2) * q ^ (ℓ * (2 * k + 1))) by ring, ← pow_add]
    congr 1
    ring

lemma a_pow_eq_C_T (k : ℕ) :
    (a : R) ^ k = PowerSeries.C (LaurentPolynomial.T (k : ℤ)) := by
  calc (a : R) ^ k
      = (PowerSeries.C (LaurentPolynomial.T 1) : R) ^ k := rfl
    _ = PowerSeries.C ((LaurentPolynomial.T 1) ^ k) := by rw [map_pow]
    _ = _ := by rw [LaurentPolynomial.T_pow]; simp

lemma summand_term_eq (k ℓ : ℕ) :
    q ^ (k ^ 2) * PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      ((-1 : R) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      ((-1 : R) ^ ℓ * q ^ ((k + ℓ) ^ 2 + ℓ)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 := by
  rw [show q ^ (k ^ 2) * PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      ((-1 : R) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
      PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      ((-1 : R) ^ ℓ * (q ^ (k ^ 2) * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ))) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 by ring_nf,
    show q ^ (k ^ 2) * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) = q ^ ((k + ℓ) ^ 2 + ℓ) by
      rw [← pow_add]
      congr 1
      ring]

lemma term_eq (k ℓ : ℕ) :
    (-1 : R) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 =
    q ^ (ℓ ^ 2) * (-(q ^ (1 + 2 * k))) ^ ℓ *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 := by
  have : ℓ ^ 2 + (1 + 2 * k) * ℓ = ℓ ^ 2 + ℓ + 2 * k * ℓ := by nlinarith
  have : (q : R) ^ (ℓ ^ 2) * (-(q : R) ^ (1 + 2 * k)) ^ ℓ =
      (-1 : R) ^ ℓ * (q : R) ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) := by rw [← this]; ring
  simp_all

lemma inner_series_summable (k : ℕ) :
    letI := piTop
    Summable fun ℓ : ℕ => (-1 : R) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 := by
  letI := piTop
  exact (series_summable (-(q ^ (1 + 2 * k))) |>.congr (fun ℓ => (term_eq k ℓ).symm))

noncomputable def piUnif : UniformSpace R :=
  PowerSeries.WithPiTopology.instUniformSpace (LaurentPolynomial ℤ)

lemma distribute_into_tsum (k : ℕ) : letI := piTop;
    q ^ (k ^ 2) * PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      (∑' ℓ : ℕ, (-1 : R) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    ∑' ℓ : ℕ,
      q ^ (k ^ 2) * PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      ((-1 : R) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) := by
  letI := piTop
  haveI : T3Space R := piTop_T3
  haveI : IsTopologicalSemiring R := instIsTopologicalSemiringPiTop
  rw [(inner_series_summable k).tsum_mul_left]

lemma summand_rewrite (k : ℕ) : letI := piTop;
    q ^ (k ^ 2) * a ^ k *
      (∑' ℓ : ℕ, (-1) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    ∑' ℓ : ℕ,
      PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      ((-1 : R) ^ ℓ * q ^ ((k + ℓ) ^ 2 + ℓ)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 := by
  letI := piTop
  rw [a_pow_eq_C_T, distribute_into_tsum]
  exact tsum_congr fun ℓ => summand_term_eq k ℓ

lemma support_finset_bound (d : ℕ) :
    ∃ (S : Finset (ℕ × ℕ)), ∀ (k ℓ : ℕ),
      ((k + ℓ) ^ 2 + ℓ : ℕ) ≤ d → (k, ℓ) ∈ S :=
  ⟨Finset.range (d + 1) ×ˢ Finset.range (d + 1), fun k ℓ h => by
    simp only [Finset.mem_product, Finset.mem_range]
    constructor <;> nlinarith [Nat.zero_le k, Nat.zero_le ℓ]⟩

lemma isUnit_C_T (k : ℤ) : IsUnit (PowerSeries.C (LaurentPolynomial.T k) : R) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C]
  exact LaurentPolynomial.isUnit_T k

lemma order_summand_ge (k ℓ : ℕ) :
    ((k + ℓ) ^ 2 + ℓ : ℕ∞) ≤
      (PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
       ((-1 : R) ^ ℓ * q ^ ((k + ℓ) ^ 2 + ℓ)) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1).order := by
  calc ((k + ℓ) ^ 2 + ℓ : ℕ∞)
      ≤ 0 + (0 + (q ^ ((k + ℓ) ^ 2 + ℓ) : R).order) := by simp
    _ ≤ (PowerSeries.C (LaurentPolynomial.T (k : ℤ)) : R).order +
        (((-1 : R) ^ ℓ).order + (q ^ ((k + ℓ) ^ 2 + ℓ) : R).order) := by
          rw [PowerSeries.order_zero_of_unit (isUnit_C_T k),
              PowerSeries.order_zero_of_unit (IsUnit.pow ℓ isUnit_one.neg)]
    _ ≤ _ := le_trans (by gcongr; exact PowerSeries.order_mul_ge _ _)
        (le_trans (PowerSeries.order_mul_ge _ _)
          (le_trans (le_add_of_nonneg_right (zero_le _)) (PowerSeries.le_order_mul ..)))

lemma coeff_summand_vanishes (k ℓ d : ℕ) (h : d < (k + ℓ) ^ 2 + ℓ) :
    (PowerSeries.coeff d)
      (PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
       ((-1 : R) ^ ℓ * q ^ ((k + ℓ) ^ 2 + ℓ)) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  exact Nat.cast_lt.mpr h |>.trans_le (order_summand_ge k ℓ)

lemma coeff_function_summable (d : ℕ) :
    Summable (fun (p : ℕ × ℕ) =>
      (PowerSeries.coeff d)
        (PowerSeries.C (LaurentPolynomial.T (p.1 : ℤ)) *
         ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
         PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1)) := by
  obtain ⟨S, hS⟩ := support_finset_bound d
  exact summable_of_ne_finset_zero (s := S) fun ⟨k, ℓ⟩ hkl =>
    coeff_summand_vanishes k ℓ d (by contrapose! hkl; exact hS k ℓ hkl)

lemma summable_F : letI := piUnif;
    Summable (fun p : ℕ × ℕ =>
      PowerSeries.C (LaurentPolynomial.T (p.1 : ℤ)) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℤ)]
  exact coeff_function_summable

lemma sum_interchange : letI := piTop;
    (∑' k : ℕ, ∑' ℓ : ℕ,
      PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      ((-1 : R) ^ ℓ * q ^ ((k + ℓ) ^ 2 + ℓ)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    ∑' p : ℕ × ℕ,
      PowerSeries.C (LaurentPolynomial.T (p.1 : ℤ)) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1 := by
  letI : UniformSpace R := piUnif
  haveI : IsUniformAddGroup R := PowerSeries.WithPiTopology.instIsUniformAddGroup _
  haveI : CompleteSpace R := PowerSeries.WithPiTopology.instCompleteSpace _
  haveI : T0Space R := PowerSeries.WithPiTopology.instT0Space _
  exact summable_F.tsum_prod.symm

lemma double_sum_expansion : letI := piTop;
    qPochhammerInf (q ^ 2) (q ^ 2) * qPochhammerInf (-q * a) (q ^ 2) =
    ∑' p : ℕ × ℕ,
      PowerSeries.C (LaurentPolynomial.T (p.1 : ℤ)) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1 := by
  rw [show (-q * a : R) = -a * q by ring, product_sum_expansion a]
  simp_rw [expand_shifted_product]
  letI := piTop
  rw [tsum_congr (fun k => summand_rewrite k), sum_interchange]

lemma constantCoeff_q_mul_aI : (q * aI : R).constantCoeff = 0 := by
  rw [map_mul, show (q : R).constantCoeff = 0 from PowerSeries.constantCoeff_X, zero_mul]

noncomputable def F (p : ℤ × ℕ) : R :=
  PowerSeries.C (LaurentPolynomial.T p.1) *
  ((-1 : R) ^ p.2 * q ^ ((p.1 + ↑p.2).natAbs ^ 2 + p.2)) *
  PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1

noncomputable def G (p : ℕ × ℕ) : R :=
  PowerSeries.C (LaurentPolynomial.T (↑p.1)) *
  ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
  PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1

private abbrev N_exp (j ℓ : ℕ) : ℕ := (-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ
private noncomputable abbrev S_hahn := HahnSeries ℤ (LaurentPolynomial ℤ)
private noncomputable def ι_hahn : R →+* S_hahn := HahnSeries.ofPowerSeries ℤ (LaurentPolynomial ℤ)
private noncomputable def Q₀ : S_hahn := HahnSeries.single (2 : ℤ) (1 : LaurentPolynomial ℤ)
private noncomputable def A_hahn (j : ℕ) : S_hahn :=
  HahnSeries.single ((-2 * ↑j : ℤ)) (1 : LaurentPolynomial ℤ)
private noncomputable def V (ℓ : ℕ) : S_hahn :=
  ι_hahn (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1)
private noncomputable def E_coeff (A : S_hahn) (b : ℤ) : LaurentPolynomial ℤ :=
  ∑ᶠ ℓ : ℕ, ((-A) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff b

noncomputable def negReindex : ℕ × ℕ ≃ {p : ℤ × ℕ // ¬(0 ≤ p.1)} where
  toFun p := ⟨(-(↑p.1 + 1), p.2), by omega⟩
  invFun p := ((-(p.1.1 : ℤ) - 1).toNat, p.1.2)
  left_inv := by
    intro ⟨j, ℓ⟩
    simp [Int.toNat_natCast]
  right_inv := by
    intro ⟨⟨z, ℓ⟩, hz⟩
    push_neg at hz
    simp only [Subtype.mk.injEq, Prod.mk.injEq]
    exact ⟨by omega, trivial⟩

lemma order_first_factor_ge (m : ℤ) :
    (m.natAbs ^ 2 : ℕ∞) ≤
      (PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2 : R).order := by
  calc (m.natAbs ^ 2 : ℕ∞)
      ≤ 0 + (q ^ m.natAbs ^ 2 : R).order := by simp
    _ ≤ _ := by
      rw [← PowerSeries.order_zero_of_unit (isUnit_C_T m)]
      exact PowerSeries.le_order_mul ..

lemma coeff_C_T_mul_q_pow_eq_zero (d : ℕ) (m : ℤ) (hm : d < m.natAbs ^ 2) :
    (PowerSeries.coeff d) (PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  calc (↑d : ℕ∞) < ↑(m.natAbs ^ 2) := by exact_mod_cast hm
    _ ≤ (PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2 : R).order :=
        order_first_factor_ge m

lemma finite_natAbs_sq_le (d : ℕ) :
    {m : ℤ | m.natAbs ^ 2 ≤ d}.Finite :=
  (Set.finite_Icc (-(d : ℤ)) (d : ℤ)).subset fun m (hm : m.natAbs ^ 2 ≤ d) => by
    have habs : m.natAbs ≤ d := by nlinarith [Nat.le_self_pow (n := 2) (by omega) m.natAbs]
    constructor <;> (rcases abs_cases m with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

lemma coeff_rhs_finite_support (d : ℕ) :
    (Function.support (fun m : ℤ =>
      (PowerSeries.coeff d) (PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2))).Finite :=
  (finite_natAbs_sq_le d).subset fun m hm => by
    simp only [Set.mem_setOf_eq]
    by_contra h
    push_neg at h
    exact hm (coeff_C_T_mul_q_pow_eq_zero d m h)

lemma summable_rhs_terms : letI := piTop;
    Summable (fun m : ℤ => PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2) := by
  letI := piTop
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  exact fun d => summable_of_finite_support (coeff_rhs_finite_support d)

lemma order_neg_q_aI_pow_ge (ℓ : ℕ) :
    (ℓ : ℕ∞) ≤ ((-(q * aI)) ^ ℓ : R).order := by
  calc (ℓ : ℕ∞) = ℓ • (1 : ℕ∞) := (nsmul_one ℓ).symm
    _ ≤ ℓ • ((-(q * aI) : R).order) := by
        apply nsmul_le_nsmul_right
        rw [ENat.one_le_iff_ne_zero, PowerSeries.order_neg,
            PowerSeries.order_ne_zero_iff_constCoeff_eq_zero]
        exact constantCoeff_q_mul_aI
    _ ≤ ((-(q * aI)) ^ ℓ : R).order := PowerSeries.le_order_pow _ _

lemma order_E_term_ge_1 (ℓ : ℕ) :
    (ℓ : ℕ∞) ≤ ((-(q * aI)) ^ ℓ *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1).order :=
  le_trans
    (le_trans (by rw [add_zero]) (add_le_add (order_neg_q_aI_pow_ge ℓ) (zero_le _)))
    (PowerSeries.order_mul_ge _ _)

lemma summable_E_terms : letI := piTop;
    Summable (fun ℓ : ℕ => (-(q * aI)) ^ ℓ *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) :=
  PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top _
    (tendsto_nhds_top_mono' tendsto_natCast_enat_atTop order_E_term_ge_1)

lemma order_product_term_ge (m : ℤ) (ℓ : ℕ) :
    (m.natAbs ^ 2 + ℓ : ℕ∞) ≤
      ((PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2) *
       ((-(q * aI)) ^ ℓ * PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1)).order := by
  calc (m.natAbs ^ 2 + ℓ : ℕ∞)
      = (m.natAbs ^ 2 : ℕ∞) + (ℓ : ℕ∞) := by norm_cast
    _ ≤ (PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2 : R).order +
        ((-(q * aI)) ^ ℓ * PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 : R).order :=
        add_le_add (order_first_factor_ge m) (order_E_term_ge_1 ℓ)
    _ ≤ _ := PowerSeries.order_mul_ge _ _

lemma finite_support_set (d : ℕ) :
    Set.Finite {p : ℤ × ℕ | p.1.natAbs ^ 2 + p.2 ≤ d} := by
  apply ((Set.finite_Icc (-d : ℤ) d).prod (by simpa using Set.finite_Iic d)).subset
  rintro ⟨m, ℓ⟩ (h : m.natAbs ^ 2 + ℓ ≤ d)
  simp only [Set.mem_prod, Set.mem_Icc, Set.mem_Iic]
  have habs : m.natAbs ≤ d := by nlinarith
  exact ⟨⟨by rcases abs_cases m with ⟨_, _⟩ | ⟨_, _⟩ <;> omega,
          by rcases abs_cases m with ⟨_, _⟩ | ⟨_, _⟩ <;> omega⟩, by omega⟩

lemma summable_product_terms : letI := piTop;
    Summable (fun p : ℤ × ℕ =>
      (PowerSeries.C (LaurentPolynomial.T p.1) * q ^ p.1.natAbs ^ 2) *
      ((-(q * aI)) ^ p.2 *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1)) := by
  change @Summable R (ℤ × ℕ) _ piTop _ _
  rw [show piTop = PowerSeries.WithPiTopology.instTopologicalSpace (LaurentPolynomial ℤ) from rfl,
    PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  apply summable_of_finite_support
  exact (finite_support_set d).subset (fun ⟨m, ℓ⟩ hmem => by
    simp only [Function.mem_support, Set.mem_setOf_eq] at hmem ⊢
    by_contra h
    push_neg at h
    exact hmem (PowerSeries.coeff_of_lt_order _ (lt_of_lt_of_le (by exact_mod_cast h) (order_product_term_ge m ℓ))))

lemma summand_rhs_E_eq (m : ℤ) (ℓ : ℕ) :
    (PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2) *
    ((-(q * aI)) ^ ℓ * PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    PowerSeries.C (LaurentPolynomial.T (m - ↑ℓ)) *
    ((-1 : R) ^ ℓ * q ^ (m.natAbs ^ 2 + ℓ)) *
    PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 := by
  have h1 : (-(q * aI)) ^ ℓ = (-1 : R) ^ ℓ * q ^ ℓ *
      PowerSeries.C (LaurentPolynomial.T (-(ℓ : ℤ))) := by
    calc (-(q * aI)) ^ ℓ
        = (-1) ^ ℓ * (q ^ ℓ * aI ^ ℓ) := by rw [neg_pow, mul_pow]
      _ = (-1) ^ ℓ * (q ^ ℓ * PowerSeries.C (LaurentPolynomial.T (-1) ^ ℓ)) := by rw [map_pow]
      _ = _ := by rw [LaurentPolynomial.T_pow]; ring_nf
  have h2 : (PowerSeries.C (R := LaurentPolynomial ℤ)) (LaurentPolynomial.T m) *
      (PowerSeries.C (R := LaurentPolynomial ℤ)) (LaurentPolynomial.T (-(ℓ : ℤ))) =
      (PowerSeries.C (R := LaurentPolynomial ℤ)) (LaurentPolynomial.T (m - ↑ℓ)) := by
    rw [← map_mul, ← LaurentPolynomial.T_add]
    ring_nf
  rw [h1, pow_add, ← h2]
  ring

lemma rhs_product_eq_double_sum_over_Z : letI := piTop;
    rhs * (∑' ℓ : ℕ, (-(q * aI)) ^ ℓ *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    (∑' p : ℤ × ℕ,
      PowerSeries.C (LaurentPolynomial.T (p.1 - ↑p.2)) *
      ((-1 : R) ^ p.2 * q ^ (p.1.natAbs ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) := by
  letI := piTop
  haveI := piTop_T3
  haveI := instIsTopologicalSemiringPiTop
  show rhs * _ = _
  unfold rhs
  rw [summable_rhs_terms.tsum_mul_tsum summable_E_terms summable_product_terms]
  exact tsum_congr (fun p => summand_rhs_E_eq p.1 p.2)

noncomputable def reindexEquiv : ℤ × ℕ ≃ ℤ × ℕ where
  toFun p := (p.1 - ↑p.2, p.2)
  invFun p := (p.1 + ↑p.2, p.2)
  left_inv p := by simp [sub_add_cancel]
  right_inv p := by simp [add_sub_cancel_right]

private noncomputable def g : letI := piTop; ℤ × ℕ → R := fun p =>
  PowerSeries.C (LaurentPolynomial.T p.1) *
    ((-1 : R) ^ p.2 * q ^ ((p.1 + ↑p.2).natAbs ^ 2 + p.2)) *
    PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1

lemma lhs_eq_g_comp_reindex (p : ℤ × ℕ) :
    letI := piTop;
    (PowerSeries.C (LaurentPolynomial.T (p.1 - ↑p.2)) *
      ((-1 : R) ^ p.2 * q ^ (p.1.natAbs ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) =
    g (reindexEquiv p) := by
  grind only [= g.eq_def, = reindexEquiv.eq_def, = Equiv.coe_fn_mk]

lemma reindex_Z_sum : letI := piTop;
    (∑' p : ℤ × ℕ,
      PowerSeries.C (LaurentPolynomial.T (p.1 - ↑p.2)) *
      ((-1 : R) ^ p.2 * q ^ (p.1.natAbs ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) =
    (∑' p : ℤ × ℕ,
      PowerSeries.C (LaurentPolynomial.T p.1) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + ↑p.2).natAbs ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) := by
  simp_rw [lhs_eq_g_comp_reindex]
  have := @Equiv.tsum_eq R _ _ _ piTop reindexEquiv g
  convert this using 1

lemma order_F_ge (z : ℤ) (ℓ : ℕ) :
    ((z + ↑ℓ).natAbs ^ 2 + ℓ : ℕ∞) ≤ (F (z, ℓ)).order := by
  set m := (z + ↑ℓ).natAbs ^ 2 + ℓ
  calc (m : ℕ∞) ≤ (q ^ m : R).order := order_q_pow_ge m
    _ ≤ ((-1 : R) ^ ℓ * q ^ m).order := le_trans le_add_self (PowerSeries.order_mul_ge _ _)
    _ ≤ (PowerSeries.C (LaurentPolynomial.T z) *
        ((-1 : R) ^ ℓ * q ^ m)).order := le_trans le_add_self (PowerSeries.order_mul_ge _ _)
    _ ≤ _ := le_trans (le_add_of_nonneg_right (zero_le _)) (PowerSeries.order_mul_ge _ _)

lemma natAbs_sq_add_tendsto_top (j : ℕ) :
    Filter.Tendsto (fun ℓ : ℕ => ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ : ℕ∞))
      Filter.atTop (nhds ⊤) :=
  tendsto_nhds_top_mono' tendsto_natCast_enat_atTop fun ℓ =>
    show (ℓ : ℕ∞) ≤ _ by exact_mod_cast show ℓ ≤ (-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ by omega

lemma order_F_neg_tendsto_top (j : ℕ) :
    Filter.Tendsto (fun ℓ : ℕ => (F (-(↑j + 1), ℓ)).order)
      Filter.atTop (nhds ⊤) :=
  tendsto_nhds_top_mono' (natAbs_sq_add_tendsto_top j) fun ℓ =>
    by dsimp only; exact_mod_cast order_F_ge (-(↑j + 1)) ℓ

lemma inner_sum_summable (j : ℕ) : letI := piTop;
    Summable (fun ℓ : ℕ => F (-(↑j + 1), ℓ)) :=
  PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top _
    (order_F_neg_tendsto_top j)

lemma finite_neg_support_set (d : ℕ) :
    Set.Finite {p : ℕ × ℕ | (-(↑p.1 + 1 : ℤ) + ↑p.2).natAbs ^ 2 + p.2 ≤ d} := by
  rw [show {p : ℕ × ℕ | (-(↑p.1 + 1 : ℤ) + ↑p.2).natAbs ^ 2 + p.2 ≤ d} =
      (fun p : ℕ × ℕ => (-(↑p.1 + 1 : ℤ) + ↑p.2, p.2)) ⁻¹'
        {p : ℤ × ℕ | p.1.natAbs ^ 2 + p.2 ≤ d} by ext ⟨j, ℓ⟩; simp]
  exact (finite_support_set d).preimage (fun ⟨j₁, ℓ₁⟩ _ ⟨j₂, ℓ₂⟩ _ h => by
    simp at h; ext <;> omega)

lemma order_G_term_ge (j ℓ : ℕ) :
    (N_exp j ℓ : ℕ∞) ≤
    ((-1 : R) ^ ℓ * q ^ N_exp j ℓ *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1).order := by
  calc (N_exp j ℓ : ℕ∞)
      = 0 + ↑(N_exp j ℓ) := by simp
    _ ≤ ((-1 : R) ^ ℓ).order + (q ^ N_exp j ℓ).order := by
        gcongr
        · exact le_of_eq (PowerSeries.order_zero_of_unit (isUnit_neg_one.pow ℓ)).symm
        · exact order_q_pow_ge _
    _ ≤ ((-1 : R) ^ ℓ * q ^ N_exp j ℓ).order := PowerSeries.le_order_mul _ _
    _ ≤ _ := le_trans (le_add_of_nonneg_right (zero_le _)) (PowerSeries.le_order_mul _ _)

lemma G_summable (j : ℕ) : letI := piTop;
    Summable (fun ℓ : ℕ =>
      (-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) := by
  letI := piTop
  exact PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top _
    (tendsto_nhds_top_mono' (natAbs_sq_add_tendsto_top j) (order_G_term_ge j))

lemma coeff_G_vanishes_of_lt (j ℓ d : ℕ) (h : d < N_exp j ℓ) :
    (PowerSeries.coeff d)
      ((-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) = 0 :=
  PowerSeries.coeff_of_lt_order d (lt_of_lt_of_le (by exact_mod_cast h) (order_G_term_ge j ℓ))

lemma coeff_G_support_finite (j d : ℕ) :
    (Function.support fun ℓ : ℕ =>
      (PowerSeries.coeff d)
        ((-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
         PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1)).Finite := by
  apply (Set.finite_Iio (d + 1)).subset
  intro ℓ hℓ
  simp only [Set.mem_Iio]
  by_contra h_le
  push_neg at h_le
  exact hℓ (coeff_G_vanishes_of_lt j ℓ d
    (lt_of_lt_of_le d.lt_succ_self (le_trans h_le (Nat.le_add_left ℓ _))))

lemma coeff_tsum_G_eq_finsum (j d : ℕ) : letI := piTop;
    (PowerSeries.coeff d) (∑' ℓ : ℕ,
      (-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    ∑ᶠ ℓ : ℕ, (PowerSeries.coeff d)
      ((-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) := by
  letI := piTop
  rw [Summable.map_tsum (G_summable j) (PowerSeries.coeff d)
    (PowerSeries.WithPiTopology.continuous_coeff (LaurentPolynomial ℤ) d)]
  exact tsum_eq_finsum (coeff_G_support_finite j d)

lemma ι_neg_one_pow (ℓ : ℕ) :
    ι_hahn ((-1 : R) ^ ℓ) = HahnSeries.single (0 : ℤ) ((-1 : LaurentPolynomial ℤ) ^ ℓ) := by
  rw [map_pow, map_neg, map_one]
  change (-1) ^ ℓ = _
  rw [show (-1 : S_hahn) = HahnSeries.single (0 : ℤ) (-1 : LaurentPolynomial ℤ) by
    rw [← HahnSeries.C_apply]
    simp]
  rw [HahnSeries.single_pow, smul_zero]

lemma qPoch_last_factor_eq (ℓ : ℕ) :
    (1 : R) - q ^ 2 * (q ^ 2) ^ ℓ = 1 - q ^ (2 * (↑ℓ + 1)) := by
  congr 1
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

lemma invOfUnit_factor (ℓ : ℕ) :
    PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 =
    PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) (ℓ + 1)) 1 *
      (1 - q ^ (2 * (↑ℓ + 1))) := by
  have hcc : ∀ m, PowerSeries.constantCoeff (qPoch (q ^ 2) (q ^ 2) m : R) =
      ↑(1 : (LaurentPolynomial ℤ)ˣ) := fun m => by simp [constantCoeff_qPoch_eq_one]
  apply (isUnit_qPoch ℓ).mul_right_cancel
  rw [mul_comm (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) _,
      PowerSeries.mul_invOfUnit _ _ (hcc ℓ), mul_assoc]
  conv_rhs => rw [← qPoch_last_factor_eq]
  rw [mul_comm (1 - q ^ 2 * (q ^ 2) ^ ℓ) _, ← qPoch_succ', PowerSeries.invOfUnit_mul _ _ (hcc (ℓ + 1))]

lemma ι_factor_eq (ℓ : ℕ) :
    ι_hahn (1 - q ^ (2 * (↑ℓ + 1))) = 1 - Q₀ ^ (ℓ + 1) := by
  rw [map_sub, map_one]
  congr 1
  show (HahnSeries.ofPowerSeries ℤ (LaurentPolynomial ℤ)) (PowerSeries.X ^ (2 * (↑ℓ + 1))) = _
  rw [HahnSeries.ofPowerSeries_X_pow, show Q₀ = HahnSeries.single (2 : ℤ) 1 from rfl,
    HahnSeries.single_pow]
  simp [add_mul, mul_comm]

lemma V_recurrence (ℓ : ℕ) :
    V ℓ = V (ℓ + 1) * (1 - Q₀ ^ (ℓ + 1)) := by
  show ι_hahn (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    ι_hahn (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) (ℓ + 1)) 1) * (1 - Q₀ ^ (ℓ + 1))
  rw [invOfUnit_factor ℓ, map_mul, ι_factor_eq]

theorem neg_A_Q₀_pow (j ℓ : ℕ) :
    (-(A_hahn j * Q₀)) ^ ℓ = (-A_hahn j) ^ ℓ * Q₀ ^ ℓ := by ring

lemma coeff_A_hahn_mul (j : ℕ) (F_arg : S_hahn) (b : ℤ) :
    (A_hahn j * F_arg).coeff b = F_arg.coeff (b + 2 * ↑j) := by
  unfold A_hahn
  conv_lhs => rw [show b = (b + 2 * ↑j) + (-2 * ↑j) by ring]
  rw [HahnSeries.coeff_single_mul_add]
  simp

lemma neg_A_pow_mul_Q₀_pow_eq_single (j ℓ : ℕ) :
    (-A_hahn j) ^ ℓ * Q₀ ^ (ℓ.choose 2) =
    HahnSeries.single (-2 * ↑j * ↑ℓ + 2 * ↑(ℓ.choose 2) : ℤ) ((-1 : LaurentPolynomial ℤ) ^ ℓ) := by
  simp only [A_hahn, Q₀, ← HahnSeries.single_neg]
  rw [HahnSeries.single_pow, HahnSeries.single_pow, HahnSeries.single_mul_single]
  simp [mul_comm, mul_left_comm]

lemma pointwise_telescope (j ℓ : ℕ) :
    (-A_hahn j) ^ (ℓ + 1) * Q₀ ^ ((ℓ + 1).choose 2) * V (ℓ + 1) =
    (-(A_hahn j * Q₀)) ^ (ℓ + 1) * Q₀ ^ ((ℓ + 1).choose 2) * V (ℓ + 1) -
    A_hahn j * ((-(A_hahn j * Q₀)) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ) := by
  rw [neg_A_Q₀_pow j (ℓ + 1), neg_A_Q₀_pow j ℓ,
    show (ℓ + 1).choose 2 = ℓ.choose 2 + ℓ from by simp [Nat.choose_succ_succ, add_comm],
    pow_add, V_recurrence ℓ]
  ring

lemma V_coeff_neg_eq_zero (ℓ : ℕ) (d : ℤ) (hd : d < 0) :
    (V ℓ).coeff d = 0 := by
  simp only [V, ι_hahn, HahnSeries.ofPowerSeries_apply]
  exact HahnSeries.embDomain_notin_range (by simp_all)

lemma expr_ge_ell_of_large (j ℓ : ℕ) (hℓ : 2 * j + 2 ≤ ℓ) :
    (ℓ : ℤ) ≤ -2 * ↑j * ↑ℓ + 2 * ↑(ℓ.choose 2) := by
  have hge : 1 ≤ ℓ := by omega
  have hdvd : 2 ∣ ℓ * (ℓ - 1) := by
    rcases Nat.even_or_odd ℓ with ⟨k, hk⟩ | ⟨k, hk⟩ <;> simp [hk] <;> ring_nf <;> omega
  have h₂ : 2 * ℓ.choose 2 = ℓ * (ℓ - 1) := by
    have := Nat.choose_two_right ℓ
    omega
  zify [hge] at h₂
  nlinarith

lemma finite_exponent_le (j : ℕ) (b : ℤ) :
    {ℓ : ℕ | -2 * ↑j * ↑ℓ + 2 * ↑(ℓ.choose 2) ≤ b}.Finite := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ ℓ : ℕ, N ≤ ℓ → b < -2 * ↑j * ↑ℓ + 2 * ↑(ℓ.choose 2) :=
    ⟨(b.toNat + 1) + (2 * j + 2), fun ℓ hℓ =>
      lt_of_lt_of_le (by omega) (expr_ge_ell_of_large j ℓ (by omega))⟩
  exact (Set.finite_lt_nat N).subset fun ℓ hℓ => by
    simp only [Set.mem_setOf_eq] at hℓ ⊢; by_contra h; push_neg at h
    exact not_lt.mpr hℓ (hN ℓ h)

lemma coeff_monomial_mul_V (j ℓ : ℕ) (b : ℤ) :
    ((-A_hahn j) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff b =
    (-1 : LaurentPolynomial ℤ) ^ ℓ * (V ℓ).coeff (b - (-2 * ↑j * ↑ℓ + 2 * ↑(ℓ.choose 2))) := by
  set e := -2 * (j : ℤ) * ↑ℓ + 2 * ↑(ℓ.choose 2)
  rw [neg_A_pow_mul_Q₀_pow_eq_single]
  conv_lhs => rw [show b = (b - e) + e by ring]
  exact HahnSeries.coeff_single_mul_add

lemma T_finite_support (j : ℕ) (b : ℤ) :
    (Function.support (fun ℓ : ℕ ↦ ((-A_hahn j) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff b)).Finite :=
  (finite_exponent_le j b).subset fun ℓ hℓ => by
    simp only [Function.mem_support, ne_eq, Set.mem_setOf_eq] at hℓ ⊢; by_contra h; push_neg at h
    exact hℓ (by rw [coeff_monomial_mul_V, V_coeff_neg_eq_zero ℓ _ (by omega), mul_zero])

lemma neg_A_pow_mul_Q₀_pow_eq_single_general (j ℓ n : ℕ) :
    (-A_hahn j) ^ ℓ * Q₀ ^ n =
    HahnSeries.single (-2 * ↑j * ↑ℓ + 2 * ↑n : ℤ) ((-1 : LaurentPolynomial ℤ) ^ ℓ) := by
  simp only [A_hahn, Q₀, ← HahnSeries.single_neg]
  rw [HahnSeries.single_pow, HahnSeries.single_pow, HahnSeries.single_mul_single]
  simp [mul_comm, mul_left_comm]

lemma coeff_single_mul_general (e : ℤ) (c : LaurentPolynomial ℤ) (f : S_hahn) (b : ℤ) :
    (HahnSeries.single e c * f).coeff b = c * f.coeff (b - e) := by
  simpa using @HahnSeries.coeff_single_mul_add ℤ (LaurentPolynomial ℤ) _ _ _ _ c f (b - e) e

lemma W_term_coeff_eq (j ℓ : ℕ) (b : ℤ) :
    ((-(A_hahn j * Q₀)) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff b =
    (-1 : LaurentPolynomial ℤ) ^ ℓ *
      (V ℓ).coeff (b - (-2 * ↑j * ↑ℓ + 2 * ↑(ℓ + ℓ.choose 2))) := by
  rw [neg_A_Q₀_pow, mul_assoc ((-A_hahn j) ^ ℓ), ← pow_add,
    neg_A_pow_mul_Q₀_pow_eq_single_general, coeff_single_mul_general]

lemma W_finite_support (j : ℕ) (b : ℤ) :
    (Function.support (fun ℓ : ℕ ↦ ((-(A_hahn j * Q₀)) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff b)).Finite :=
  (finite_exponent_le j b).subset fun ℓ hℓ => by
    simp only [Function.mem_support, ne_eq, Set.mem_setOf_eq] at hℓ ⊢; by_contra h; push_neg at h
    exact hℓ (by rw [W_term_coeff_eq, V_coeff_neg_eq_zero ℓ _ (by
      have : (ℓ.choose 2 : ℤ) ≤ ↑(ℓ + ℓ.choose 2) := by exact_mod_cast Nat.le_add_left _ _
      linarith), mul_zero])

lemma AW_finite_support (j : ℕ) (b : ℤ) :
    (Function.support (fun ℓ : ℕ ↦ (A_hahn j * ((-(A_hahn j * Q₀)) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ)).coeff b)).Finite :=
  (W_finite_support j (b + 2 * ↑j)).subset fun ℓ hℓ => by
    simp only [Function.mem_support] at hℓ ⊢; rwa [coeff_A_hahn_mul] at hℓ

lemma telescope_rewrite {G_type : Type*} [AddCommGroup G_type]
    {t w u : ℕ → G_type}
    (N_val : ℕ)
    (h_zero : t 0 = w 0)
    (h_succ : ∀ ℓ, t (ℓ + 1) = w (ℓ + 1) - u ℓ) :
    ∑ i ∈ Finset.range (N_val + 1), t i =
    ∑ i ∈ Finset.range (N_val + 1), w i - ∑ i ∈ Finset.range N_val, u i := by
  induction N_val with
  | zero => simp [h_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp_all [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
    abel

lemma finset_range_telescope {G_type : Type*} [AddCommGroup G_type]
    {t w u : ℕ → G_type}
    (N_val : ℕ)
    (ht_van : t (N_val + 1) = 0)
    (hw_van : w (N_val + 1) = 0)
    (h_zero : t 0 = w 0)
    (h_succ : ∀ ℓ, t (ℓ + 1) = w (ℓ + 1) - u ℓ) :
    ∑ i ∈ Finset.range (N_val + 1), t i =
    ∑ i ∈ Finset.range (N_val + 1), w i - ∑ i ∈ Finset.range (N_val + 1), u i := by
  rw [telescope_rewrite N_val h_zero h_succ]
  congr 1
  rw [Finset.sum_range_succ, show u N_val = 0 by
    have := h_succ N_val
    rw [ht_van, hw_van, zero_sub] at this
    exact neg_eq_zero.mp this.symm, add_zero]

lemma finite_support_vanishing_bound {G_type : Type*} [AddCommGroup G_type]
    {f : ℕ → G_type} (hf : (Function.support f).Finite) :
    ∃ N, ∀ i, N < i → f i = 0 :=
  (Set.exists_upper_bound_image _ id hf).imp fun _ hN i hi =>
    Function.notMem_support.mp (fun hmem => Nat.not_lt.mpr (hN i hmem) hi)

lemma exists_common_vanishing_bound {G_type : Type*} [AddCommGroup G_type]
    {t w u : ℕ → G_type}
    (ht : (Function.support t).Finite)
    (hw : (Function.support w).Finite)
    (hu : (Function.support u).Finite) :
    ∃ N, ∀ i, N < i → t i = 0 ∧ w i = 0 ∧ u i = 0 :=
  (finite_support_vanishing_bound ht).elim fun Nt hNt =>
    (finite_support_vanishing_bound hw).elim fun Nw hNw =>
    (finite_support_vanishing_bound hu).elim fun Nu hNu =>
    ⟨max Nt (max Nw Nu), fun i hi =>
      ⟨hNt i (by omega), hNw i (by omega), hNu i (by omega)⟩⟩

lemma finsum_telescope {G_type : Type*} [AddCommGroup G_type]
    {t w u : ℕ → G_type}
    (ht : (Function.support t).Finite)
    (hw : (Function.support w).Finite)
    (hu : (Function.support u).Finite)
    (h_zero : t 0 = w 0)
    (h_succ : ∀ ℓ, t (ℓ + 1) = w (ℓ + 1) - u ℓ) :
    ∑ᶠ ℓ, t ℓ = ∑ᶠ ℓ, w ℓ - ∑ᶠ ℓ, u ℓ := by
  obtain ⟨N, hN⟩ := exists_common_vanishing_bound ht hw hu
  have mk_sub : ∀ (f : ℕ → G_type), (∀ i, N < i → f i = 0) →
      Function.support f ⊆ ↑(Finset.range (N + 1)) :=
    fun f hf x hx => by
      simp
      by_contra h
      exact hx (hf x (by omega))
  rw [finsum_eq_sum_of_support_subset t (mk_sub t (fun i hi => (hN i hi).1)),
      finsum_eq_sum_of_support_subset w (mk_sub w (fun i hi => (hN i hi).2.1)),
      finsum_eq_sum_of_support_subset u (mk_sub u (fun i hi => (hN i hi).2.2))]
  exact finset_range_telescope N ((hN (N + 1) (by omega)).1) ((hN (N + 1) (by omega)).2.1) h_zero h_succ

lemma E_coeff_eq_telescope (j : ℕ) (b : ℤ) :
    E_coeff (A_hahn j) b =
    ∑ᶠ ℓ : ℕ, ((-(A_hahn j * Q₀)) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff b -
    ∑ᶠ ℓ : ℕ, (A_hahn j * ((-(A_hahn j * Q₀)) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ)).coeff b := by
  apply finsum_telescope (T_finite_support j b) (W_finite_support j b) (AW_finite_support j b)
  · simp
  · intro ℓ
    simpa only [HahnSeries.coeff_sub] using congr_arg (·.coeff b) (pointwise_telescope j ℓ)

lemma functional_equation (j : ℕ) (b : ℤ) :
    E_coeff (A_hahn j) b =
    E_coeff (A_hahn j * Q₀) b - E_coeff (A_hahn j * Q₀) (b + (2 * ↑j)) := by
  rw [E_coeff_eq_telescope]
  congr 1
  show ∑ᶠ ℓ : ℕ, (A_hahn j * ((-(A_hahn j * Q₀)) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ)).coeff b =
    E_coeff (A_hahn j * Q₀) (b + (2 * ↑j))
  simp_rw [coeff_A_hahn_mul]
  rfl

lemma A_hahn_succ_mul_Q₀ (j : ℕ) : A_hahn (j + 1) * Q₀ = A_hahn j := by
  simp only [A_hahn, Q₀]
  rw [HahnSeries.single_mul_single]
  exact congr_arg₂ _ (by push_cast; ring_nf) (one_mul 1)

private lemma E_coeff_A_hahn_eq_zero (j : ℕ) (b : ℤ) : E_coeff (A_hahn j) b = 0 := by
  induction j generalizing b with
  | zero => rw [functional_equation 0 b]; simp [show A_hahn 0 = 1 from by simp [A_hahn]]
  | succ j ih =>
    rw [functional_equation (j + 1) b, A_hahn_succ_mul_Q₀]
    simp [ih]

lemma exponent_identity_algebraic (j ℓ : ℕ) :
    (↑ℓ - (↑j + 1 : ℤ)) ^ 2 + ↑ℓ =
    (↑j + 1) ^ 2 + 2 * ↑(ℓ.choose 2) - 2 * ↑j * ↑ℓ := by
  rcases eq_or_lt_of_le (Nat.zero_le ℓ) with rfl | hge
  · simp [Nat.choose_two_right]
    ring
  · have h : ℓ * (ℓ - 1) = 2 * ℓ.choose 2 := by
      have := Nat.choose_two_right ℓ
      have : 2 ∣ ℓ * (ℓ - 1) := by
        rcases Nat.even_or_odd ℓ with ⟨k, hk⟩ | ⟨k, hk⟩ <;> simp [hk] <;> ring_nf <;> omega
      omega
    zify [hge] at h
    nlinarith

lemma exponent_identity (j ℓ : ℕ) :
    ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ : ℤ) =
    (↑j + 1) ^ 2 + 2 * ↑(ℓ.choose 2) - 2 * ↑j * ↑ℓ := by
  linarith [Int.natAbs_sq (-(↑j + 1 : ℤ) + ↑ℓ), exponent_identity_algebraic j ℓ]

lemma ι_expression_eq_single_mul_V (j ℓ : ℕ) :
    let N_val := (-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ
    ι_hahn ((-1 : R) ^ ℓ * q ^ N_val * PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    HahnSeries.single (↑N_val : ℤ) ((-1 : LaurentPolynomial ℤ) ^ ℓ) * V ℓ := by
  intro N_val
  rw [map_mul, map_mul, ι_neg_one_pow]
  have hq : ι_hahn (q ^ N_val) = HahnSeries.single (↑N_val : ℤ) 1 :=
    HahnSeries.ofPowerSeries_X_pow N_val
  rw [hq, HahnSeries.single_mul_single, zero_add, mul_one]
  rfl

lemma coeff_single_mul (j d : ℕ) (tail : S_hahn) :
    (HahnSeries.single ((j + 1 : ℤ) ^ 2) (1 : LaurentPolynomial ℤ) * tail).coeff (↑d) =
    tail.coeff ((d : ℤ) - (j + 1 : ℤ) ^ 2) := by
  conv_lhs => rw [show (d : ℤ) = ((d : ℤ) - (j + 1 : ℤ) ^ 2) + (j + 1 : ℤ) ^ 2 by ring]
  rw [HahnSeries.coeff_single_mul_add, one_mul]

lemma per_term_coeff_eq (j d ℓ : ℕ) :
    (PowerSeries.coeff d)
      ((-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    ((-A_hahn j) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff
      ((d : ℤ) - ((j + 1 : ℤ)) ^ 2) := by
  set N_val := (-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ with hN_def
  rw [show (PowerSeries.coeff d)
      ((-1 : R) ^ ℓ * q ^ N_val * PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    (ι_hahn ((-1 : R) ^ ℓ * q ^ N_val * PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1)).coeff (d : ℤ)
    from (HahnSeries.ofPowerSeries_apply_coeff _ _).symm]
  rw [ι_expression_eq_single_mul_V j ℓ]
  have hN_eq : (↑N_val : ℤ) = (↑j + 1) ^ 2 + (-2 * ↑j * ↑ℓ + 2 * ↑(ℓ.choose 2)) := by
    rw [hN_def]
    push_cast
    have h := exponent_identity j ℓ
    rw [Int.natAbs_sq] at h
    rw [sq_abs]
    linarith
  rw [show HahnSeries.single (↑N_val : ℤ) ((-1 : LaurentPolynomial ℤ) ^ ℓ) =
    HahnSeries.single ((j + 1 : ℤ) ^ 2) (1 : LaurentPolynomial ℤ) *
    HahnSeries.single (-2 * ↑j * ↑ℓ + 2 * ↑(ℓ.choose 2) : ℤ) ((-1 : LaurentPolynomial ℤ) ^ ℓ) by
      rw [HahnSeries.single_mul_single, one_mul, hN_eq]]
  rw [mul_assoc, coeff_single_mul, neg_A_pow_mul_Q₀_pow_eq_single]

lemma coeff_tsum_G_eq_zero (j d : ℕ) : letI := piTop;
    (PowerSeries.coeff d) (∑' ℓ : ℕ,
      (-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) = 0 := by
  rw [coeff_tsum_G_eq_finsum j d, finsum_congr fun ℓ => per_term_coeff_eq j d ℓ]
  exact E_coeff_A_hahn_eq_zero j _

lemma tsum_G_eq_zero (j : ℕ) : letI := piTop;
    ∑' ℓ : ℕ, ((-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) = 0 :=
  PowerSeries.ext fun d => coeff_tsum_G_eq_zero j d

lemma inner_sum_neg_vanishes (j : ℕ) : letI := piTop;
    ∑' ℓ : ℕ, F (-(↑j + 1), ℓ) = 0 := by
  letI : TopologicalSpace R := piTop
  haveI : T2Space R := PowerSeries.WithPiTopology.instT2Space _
  haveI := instIsTopologicalSemiringPiTop
  have heq : (fun ℓ : ℕ => F (-(↑j + 1), ℓ)) = (fun ℓ : ℕ =>
      PowerSeries.C (LaurentPolynomial.T (-(↑j + 1))) *
      ((-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1)) := by
    ext ℓ
    simp only [F, mul_assoc]
  rw [heq, (G_summable j).tsum_mul_left, tsum_G_eq_zero j, mul_zero]

set_option maxHeartbeats 800000 in

lemma support_finset_Z_nat (d : ℕ) :
    ∃ (S_fin : Finset (ℤ × ℕ)), ∀ (z : ℤ) (ℓ : ℕ),
      (z + ↑ℓ).natAbs ^ 2 + ℓ ≤ d → (z, ℓ) ∈ S_fin := by
  use (Finset.Icc (-2 * (d : ℤ)) (d : ℤ)) ×ˢ (Finset.Icc 0 d)
  intro z ℓ h
  have h₁ : ℓ ≤ d := by nlinarith
  have h₂ : (z + ℓ).natAbs ≤ d := by nlinarith
  have h₃ : (z : ℤ) ≥ -2 * (d : ℤ) := by
    have h₅ : -(z + ↑ℓ) ≤ ↑(z + ↑ℓ).natAbs := by
      rw [← Int.natAbs_neg]
      exact Int.le_natAbs
    linarith [Int.ofNat_le.mpr h₁, Int.ofNat_le.mpr h₂]
  have h₄ : (z : ℤ) ≤ (d : ℤ) := by
    have := Int.le_natAbs (a := z + ↑ℓ)
    nlinarith [Int.ofNat_le.mpr h₂]
  simp_all

lemma coeff_F_vanishes (z : ℤ) (ℓ : ℕ) (d : ℕ) (h : d < (z + ↑ℓ).natAbs ^ 2 + ℓ) :
    (PowerSeries.coeff d) (F (z, ℓ)) = 0 :=
  PowerSeries.coeff_of_lt_order _ (Nat.cast_lt.mpr h |>.trans_le (order_F_ge z ℓ))

lemma coeff_F_summable (d : ℕ) : letI := piTop;
    Summable (fun (p : ℤ × ℕ) => (PowerSeries.coeff d) (F p)) := by
  letI := piTop; obtain ⟨S_fin, hS⟩ := support_finset_Z_nat d
  exact summable_of_ne_finset_zero (s := S_fin) fun ⟨z, ℓ⟩ hzl =>
    coeff_F_vanishes z ℓ d (by contrapose! hzl; exact hS z ℓ hzl)

lemma tsum_F_nonneg_eq_tsum_G : letI := piTop;
    (∑' (p : {p : ℤ × ℕ // 0 ≤ p.1}), F p.val) =
    (∑' (p : ℕ × ℕ), G p) := by
  letI := piTop
  have : (∑' (p : {p : ℤ × ℕ // 0 ≤ p.1}), F p.val) =
         (∑' (p : ℕ × ℕ), F ((↑p.1 : ℤ), p.2)) := by
    let e : ℕ × ℕ ≃ {p : ℤ × ℕ // 0 ≤ p.1} :=
      { toFun := fun p => ⟨(↑p.1, p.2), Int.natCast_nonneg p.1⟩
        invFun := fun p => (p.1.1.toNat, p.1.2)
        left_inv := fun p => by simp [Int.toNat_natCast]
        right_inv := fun ⟨⟨z, n⟩, hz⟩ => by
          simp only
          exact Subtype.ext (Prod.ext (by simp [Int.toNat_of_nonneg hz]) rfl) }
    rw [← Equiv.tsum_eq e]; congr 1
  rw [this]
  exact tsum_congr fun ⟨k, ℓ⟩ => by simp only [F, G, show (↑k + ↑ℓ : ℤ).natAbs = k + ℓ by omega]

lemma coeff_F_neg_finite_support (d : ℕ) :
    ∃ (S_fin : Finset (ℕ × ℕ)), ∀ p : ℕ × ℕ, p ∉ S_fin →
      (PowerSeries.coeff d) (F (-(↑p.1 + 1), p.2)) = 0 := by
  obtain ⟨S_fin, hS⟩ := (finite_neg_support_set d).exists_finset
  exact ⟨S_fin, fun p hp ↦ coeff_F_vanishes _ _ d (by
    simp only [hS, Set.mem_setOf_eq] at hp
    omega)⟩

lemma summable_F_neg_reindexed : letI := piTop;
    Summable (fun p : ℕ × ℕ => F (-(↑p.1 + 1), p.2)) := by
  letI := piTop; rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]; intro d
  exact (coeff_F_neg_finite_support d).elim fun S_fin hS =>
    summable_of_ne_finset_zero (s := S_fin) fun p hp => hS p hp

lemma tsum_F_neg_NxN_eq_zero : letI := piTop;
    (∑' (c : ℕ × ℕ), F (-(↑c.1 + 1), c.2)) = 0 := by
  letI := piTop
  haveI := instIsTopologicalSemiringPiTop
  haveI := piTop_T3
  rw [show (fun c : ℕ × ℕ => F (-(↑c.1 + 1), c.2)) = fun c =>
      F (-(↑c.1 + 1 : ℤ), c.2) from rfl,
    @Summable.tsum_prod' R ℕ ℕ _ piTop _ _ _ summable_F_neg_reindexed inner_sum_summable]
  simp only [inner_sum_neg_vanishes, tsum_zero]

lemma tsum_F_neg_eq_zero : letI := piTop;
    (∑' (p : {p : ℤ × ℕ // ¬(0 ≤ p.1)}), F p.val) = 0 := by
  letI := piTop
  rw [← Equiv.tsum_eq negReindex]
  simp only [negReindex, Equiv.coe_fn_mk]
  exact tsum_F_neg_NxN_eq_zero

lemma tsum_F_split : letI := piTop;
    (∑' (p : ℤ × ℕ), F p) =
    (∑' (p : {p : ℤ × ℕ // 0 ≤ p.1}), F p.val) +
    (∑' (p : {p : ℤ × ℕ // ¬(0 ≤ p.1)}), F p.val) := by
  letI : UniformSpace R := piUnif
  haveI : IsUniformAddGroup R := PowerSeries.WithPiTopology.instIsUniformAddGroup _
  haveI : CompleteSpace R := PowerSeries.WithPiTopology.instCompleteSpace _
  haveI : T2Space R := PowerSeries.WithPiTopology.instT2Space _
  have hsumm : Summable (fun p : ℤ × ℕ ↦ F p) := by
    rw [show piUnif.toTopologicalSpace = piTop from rfl,
      PowerSeries.WithPiTopology.summable_iff_summable_coeff]
    exact coeff_F_summable
  exact (hsumm.tsum_subtype_add_tsum_subtype_compl {p | 0 ≤ p.1}).symm

theorem tsum_F_eq_tsum_G : letI := piTop;
    (∑' p : ℤ × ℕ, F p) = (∑' p : ℕ × ℕ, G p) := by
  letI := piTop
  rw [tsum_F_split, tsum_F_nonneg_eq_tsum_G, tsum_F_neg_eq_zero]
  ring

lemma restrict_Z_to_N : letI := piTop;
    (∑' p : ℤ × ℕ, PowerSeries.C (LaurentPolynomial.T p.1) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + ↑p.2).natAbs ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) =
    (∑' p : ℕ × ℕ, PowerSeries.C (LaurentPolynomial.T (↑p.1)) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) := tsum_F_eq_tsum_G

lemma double_sum_factors : letI := piTop;
    (∑' p : ℕ × ℕ,
      PowerSeries.C (LaurentPolynomial.T (p.1 : ℤ)) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) =
    rhs * (∑' ℓ : ℕ, (-(q * aI)) ^ ℓ *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) := by
  letI := piTop
  rw [rhs_product_eq_double_sum_over_Z, reindex_Z_sum, restrict_Z_to_N]

lemma triple_product_eq_rhs : letI := piTop;
    qPochhammerInf (q ^ 2) (q ^ 2) * qPochhammerInf (-q * a) (q ^ 2) *
    qPochhammerInf (-q * aI) (q ^ 2) = rhs := by
  letI := piTop
  rw [double_sum_expansion, double_sum_factors, mul_assoc]
  conv_lhs => rw [show -q * aI = -(q * aI) by ring]
  rw [euler_inverse (q * aI) constantCoeff_q_mul_aI, mul_one]

lemma multipliable_P3_factors : letI := piTop;
    Multipliable (fun n : ℕ => 1 - (-q * aI) * (q ^ 2) ^ n : ℕ → R) := by
  letI := piTop
  have key : Filter.Tendsto (fun n => (-((-q * aI) * (q ^ 2) ^ n)).order) Filter.atTop (nhds ⊤) := by
    simp only [PowerSeries.order_neg]
    exact order_neg_q_aI_tendsto_top
  convert PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
    (R := LaurentPolynomial ℤ) key using 1
  ext n
  ring_nf

lemma constantCoeff_P3 : letI := piTop;
    (qPochhammerInf (-q * aI) (q ^ 2) : R).constantCoeff = 1 := by
  letI := piTop
  haveI : T2Space R := PowerSeries.WithPiTopology.instT2Space _
  unfold qPochhammerInf
  rw [tprod_eq_of_multipliable_unconditional multipliable_P3_factors]
  have := multipliable_P3_factors.map_tprod
    (PowerSeries.constantCoeff (R := LaurentPolynomial ℤ)).toMonoidHom
    (PowerSeries.WithPiTopology.continuous_constantCoeff _)
  simp only [MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe] at this
  rw [this]
  simp only [map_sub, map_one, map_mul, map_neg, map_pow,
    PowerSeries.constantCoeff_X, neg_zero, zero_mul, sub_zero]
  exact tprod_one

lemma double_sum_eq_rhs_mul_inv : letI := piTop;
    (∑' p : ℕ × ℕ,
      PowerSeries.C (LaurentPolynomial.T (p.1 : ℤ)) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) =
    rhs * PowerSeries.invOfUnit (qPochhammerInf (-q * aI) (q ^ 2)) 1 := by
  letI := piTop; rw [← double_sum_expansion]
  calc qPochhammerInf (q ^ 2) (q ^ 2) * qPochhammerInf (-q * a) (q ^ 2)
      = _ * qPochhammerInf (-q * aI) (q ^ 2) *
          PowerSeries.invOfUnit (qPochhammerInf (-q * aI) (q ^ 2)) 1 := by
        rw [mul_assoc, PowerSeries.mul_invOfUnit _ _ constantCoeff_P3, mul_one]
    _ = _ := by rw [triple_product_eq_rhs]

theorem jacobi_triple_product : lhs = rhs := by
  unfold lhs
  rw [double_sum_expansion, double_sum_eq_rhs_mul_inv, mul_assoc,
      PowerSeries.invOfUnit_mul _ _ (by rw [constantCoeff_P3]; rfl), mul_one]
