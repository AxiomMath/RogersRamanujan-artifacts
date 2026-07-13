import Mathlib
import RogersRamanujan

section additions

open Finset Filter Topology

namespace PowerSeries

variable {R : Type*} [CommRing R] {ι : Type*} (k : ℕ) (s : Finset ι) (p : R⟦X⟧) (f : ι → R⟦X⟧)

theorem coeff_mul_prod_of_lt_order_sub_one (H : ∀ i ∈ s, k < (f i - 1).order) :
  (p * ∏ i ∈ s, f i).coeff k = p.coeff k := by
  convert coeff_mul_prod_one_sub_of_lt_order k s p (fun i ↦ 1 - f i)
    (by simpa [show ∀ i, 1 - f i = -(f i - 1) by intro; ring, -neg_sub])
  simp

variable {f}

lemma coeff_finset_prod_eq
    [LinearOrder ι] [LocallyFiniteOrderBot ι]
    {N : ι} {i : ℕ} (hi : ∀ m ≥ N, i < (f m - 1).order) {S : Finset ι} (hS : Finset.Iio N ⊆ S) :
    (∏ m ∈ S, f m).coeff i = (∏ j ∈ Finset.Iio N, f j).coeff i := by
  rw [← prod_sdiff hS, mul_comm, coeff_mul_prod_of_lt_order_sub_one _ _ _ _ (by grind)]

lemma eventually_coeff_eq
    [LinearOrder ι] [LocallyFiniteOrderBot ι]
    {N : ι} {i : ℕ} (hi : ∀ m ≥ N, i < (f m - 1).order) :
    ∀ᶠ S in atTop, (∏ m ∈ S, f m).coeff i = (∏ j ∈ Finset.Iio N, f j).coeff i := by
  rw [Filter.eventually_atTop]
  exact ⟨Finset.Iio N, fun S hS ↦ coeff_finset_prod_eq hi hS⟩

namespace WithPiTopology

section CommSemiring

variable {R : Type*} [TopologicalSpace R] [CommSemiring R]
  {ι : Type*} {a : ι → R⟦X⟧} {L : SummationFilter ι}

theorem coeff_tsum [T2Space R] [L.NeBot] (ha : Summable a L) (n : ℕ) :
    (∑'[L] i, a i).coeff n = ∑'[L] i, (a i).coeff n :=
  ha.map_tsum _ <| continuous_coeff _ _

theorem tendsto_coeff_prod_coeff_tprod (ha : Multipliable a L) (n : ℕ) :
    Tendsto (∏ i ∈ ·, a i |>.coeff n) L.filter (𝓝 <| (∏'[L] i, a i).coeff n) :=
  .comp ((continuous_coeff _ _).tendsto _) ha.hasProd

end CommSemiring

section CommRing

variable {R : Type*} [TopologicalSpace R] [CommRing R]
  {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] {a : ι → R⟦X⟧}
  {L : SummationFilter ι}

lemma multipliable_of_tendsto_order_sub_one
    (h : Tendsto (fun m ↦ (a m - 1).order) atTop (𝓝 ⊤)) : Multipliable a := by
  convert multipliable_one_add_of_tendsto_order_atTop_nhds_top _ h
  all_goals first | rfl | ring

lemma multipliable_one_sub_of_tendsto_order
    (h : Tendsto (fun m ↦ (a m).order) atTop (𝓝 ⊤)) : Multipliable (1 - a ·) :=
  multipliable_of_tendsto_order_sub_one <| by simpa

theorem coeff_tprod_of_lt_order_sub_one
    [T2Space R] [L.NeBot] [hl : L.LeAtTop] (h : Multipliable a L)
    {N : ι} {i : ℕ} (hi : ∀ m ≥ N, i < (a m - 1).order) :
    (∏'[L] m, a m).coeff i = (∏ j ∈ Finset.Iio N, a j).coeff i :=
  tendsto_nhds_unique_of_eventuallyEq ((continuous_coeff R i).continuousAt.tendsto.comp
    h.hasProd) tendsto_const_nhds <| (eventually_coeff_eq hi).filter_mono hl.le_atTop

theorem coeff_tprod_one_sub_of_lt_order
    [T2Space R] [L.NeBot] [hl : L.LeAtTop] (h : Multipliable (1 - a ·) L)
    {N : ι} {i : ℕ} (hi : ∀ m ≥ N, i < (a m).order) :
    (∏'[L] m, (1 - a m)).coeff i = (∏ j ∈ Finset.Iio N, (1 - a j)).coeff i :=
  coeff_tprod_of_lt_order_sub_one h <| by simpa

end CommRing

end PowerSeries.WithPiTopology

end additions

open PowerSeries PowerSeries.WithPiTopology

-- Main Definition(s)

/-- The cube of Euler's function as a formal power series:
`∏_{n=1}^{∞} (1 - q^n)^3`, reindexed over all `n : ℕ` as `∏_{n} (1 - X^(n+1))^3`. -/
noncomputable def eulerCube : PowerSeries ℤ :=
  ∏' n : ℕ, (1 - (X : PowerSeries ℤ) ^ (n + 1)) ^ 3

/-- The right-hand side lacunary series:
`∑_{k=0}^{∞} (-1)^k (2k+1) q^{(k^2+k)/2}`. -/
noncomputable def jacobiSeries : PowerSeries ℤ :=
  ∑' k : ℕ, (C ((-1 : ℤ) ^ k * (2 * (k : ℤ) + 1))) * (X : PowerSeries ℤ) ^ ((k ^ 2 + k) / 2)

/-- The `k`-th triangular number `T_k = (k^2+k)/2`. -/
def Tri (k : ℕ) : ℕ := (k ^ 2 + k) / 2

theorem even_sq_add (k : ℕ) : Even (k ^ 2 + k) := by
  have : k ^ 2 + k = k * (k + 1) := by ring
  rw [this]; exact Nat.even_mul_succ_self k

theorem two_mul_Tri (k : ℕ) : 2 * Tri k = k ^ 2 + k := by
  unfold Tri; rw [Nat.two_mul_div_two_of_even (even_sq_add k)]

theorem Tri_strictMono : StrictMono Tri := by
  apply strictMono_nat_of_lt_succ
  intro k
  nlinarith [two_mul_Tri k, two_mul_Tri (k + 1)]

theorem Tri_injective : Function.Injective Tri := Tri_strictMono.injective

/-- The `k`-th summand of `jacobiSeries`. -/
noncomputable def js (k : ℕ) : PowerSeries ℤ :=
  (C ((-1 : ℤ) ^ k * (2 * (k : ℤ) + 1))) * (X : PowerSeries ℤ) ^ (Tri k)

theorem jacobiSeries_eq_tsum_js : jacobiSeries = ∑' k : ℕ, js k := rfl

theorem coeff_js (k d : ℕ) :
    coeff d (js k) = if Tri k = d then (-1 : ℤ) ^ k * (2 * (k : ℤ) + 1) else 0 := by
  unfold js
  rw [coeff_C_mul, coeff_X_pow]
  by_cases h : Tri k = d
  · subst h; simp
  · rw [if_neg (by simpa [eq_comm] using h), if_neg h, mul_zero]

theorem hasSum_coeff_js_tri (k₀ d : ℕ) (hd : Tri k₀ = d) :
    HasSum (fun k => coeff d (js k)) ((-1 : ℤ) ^ k₀ * (2 * (k₀ : ℤ) + 1)) := by
  have : ((-1 : ℤ) ^ k₀ * (2 * (k₀ : ℤ) + 1)) = (fun k => coeff d (js k)) k₀ := by
    simp only [coeff_js, if_pos hd]
  rw [this]
  apply hasSum_single
  intro b hb
  rw [coeff_js, if_neg]
  intro h
  exact hb (Tri_injective (h.trans hd.symm))

theorem hasSum_coeff_js_nontri (d : ℕ) (hd : ∀ k, Tri k ≠ d) :
    HasSum (fun k => coeff d (js k)) 0 := by
  have : (fun k => coeff d (js k)) = (fun _ => (0 : ℤ)) := by
    funext k; rw [coeff_js, if_neg (hd k)]
  rw [this]
  exact hasSum_zero

theorem summable_js : Summable js := by
  rw [summable_iff_summable_coeff ℤ]
  intro d
  by_cases h : ∃ k, Tri k = d
  · obtain ⟨k₀, hk₀⟩ := h
    exact (hasSum_coeff_js_tri k₀ d hk₀).summable
  · push_neg at h
    exact (hasSum_coeff_js_nontri d h).summable

theorem hasSum_js : HasSum js jacobiSeries := by
  rw [jacobiSeries_eq_tsum_js]; exact summable_js.hasSum

/-- Coefficient of `jacobiSeries` at a triangular index `Tri k`. -/
theorem coeff_jacobiSeries_tri (k : ℕ) :
    coeff (Tri k) jacobiSeries = (-1 : ℤ) ^ k * (2 * (k : ℤ) + 1) := by
  have hmap : HasSum (fun j => coeff (Tri k) (js j)) (coeff (Tri k) jacobiSeries) :=
    hasSum_js.map (coeff (Tri k)) (continuous_coeff ℤ (Tri k))
  exact ((hasSum_coeff_js_tri k (Tri k) rfl).unique hmap).symm

/-- Coefficient of `jacobiSeries` at a non-triangular index. -/
theorem coeff_jacobiSeries_nontri (m : ℕ) (h : ∀ k, Tri k ≠ m) :
    coeff m jacobiSeries = 0 := by
  have hmap : HasSum (fun j => coeff m (js j)) (coeff m jacobiSeries) :=
    hasSum_js.map (coeff m) (continuous_coeff ℤ m)
  exact ((hasSum_coeff_js_nontri m h).unique hmap).symm

theorem eulerCube_multipliable :
    Multipliable (fun n : ℕ => (1 - (X : PowerSeries ℤ) ^ (n + 1)) ^ 3) := by
  apply PowerSeries.WithPiTopology.multipliable_of_tendsto_order_sub_one
  have hle : ∀ m : ℕ, ((m : ℕ∞)) ≤ ((1 - (X : PowerSeries ℤ) ^ (m + 1)) ^ 3 - 1).order := by
    intro m
    apply PowerSeries.le_order
    intro i hi
    have hi' : i < m := by exact_mod_cast hi
    have heq : (1 - (X : PowerSeries ℤ) ^ (m + 1)) ^ 3 - 1
        = (-3 : ℤ) • X ^ (m + 1) + (3 : ℤ) • X ^ (2 * (m + 1)) - X ^ (3 * (m + 1)) := by
      ring
    rw [heq]
    simp only [map_sub, map_add, map_smul, coeff_X_pow, smul_eq_mul]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring
  exact tendsto_nhds_top_mono ENat.tendsto_nat_nhds_top (Filter.Eventually.of_forall hle)

theorem coeff_eulerCube_eq_coeff_finprod (d : ℕ) :
    coeff d eulerCube
      = coeff d (∏ j ∈ Finset.Iio (d + 1), (1 - (X : PowerSeries ℤ) ^ (j + 1)) ^ 3) := by
  rw [eulerCube]
  apply PowerSeries.WithPiTopology.coeff_tprod_of_lt_order_sub_one eulerCube_multipliable
  intro m hm
  have hle : ((m : ℕ∞)) ≤ ((1 - (X : PowerSeries ℤ) ^ (m + 1)) ^ 3 - 1).order := by
    apply PowerSeries.le_order
    intro i hi
    have hi' : i < m := by exact_mod_cast hi
    have heq : (1 - (X : PowerSeries ℤ) ^ (m + 1)) ^ 3 - 1
        = (-3 : ℤ) • X ^ (m + 1) + (3 : ℤ) • X ^ (2 * (m + 1)) - X ^ (3 * (m + 1)) := by
      ring
    rw [heq]
    simp only [map_sub, map_add, map_smul, coeff_X_pow, smul_eq_mul]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring
  have hdm : (d : ℕ∞) < (m : ℕ∞) := by
    have : (d : ℕ∞) < ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self d
    calc (d : ℕ∞) < ((d + 1 : ℕ) : ℕ∞) := this
      _ ≤ (m : ℕ∞) := by exact_mod_cast hm
  exact lt_of_lt_of_le hdm hle

open PowerSeries.DiscreteTopology in
theorem eulerCube_eq_qPochhammerCube :
    eulerCube = (qPochhammerInf (X : PowerSeries ℤ) X) ^ 3 := by
  apply PowerSeries.ext
  intro d
  rw [coeff_eulerCube_eq_coeff_finprod d]
  have hmul0 : Multipliable fun m : ℕ => 1 - (X : PowerSeries ℤ) * PowerSeries.X ^ m := by
    apply PowerSeries.WithPiTopology.multipliable_of_tendsto_order_sub_one
    apply tendsto_nhds_top_mono ENat.tendsto_nat_nhds_top
    apply Filter.Eventually.of_forall
    intro m
    show (m : ℕ∞) ≤ (1 - (X : PowerSeries ℤ) * PowerSeries.X ^ m - 1).order
    have heq : (1 - (X : PowerSeries ℤ) * PowerSeries.X ^ m - 1) = -(X ^ (m + 1)) := by ring
    rw [heq, order_neg, order_X_pow]
    exact_mod_cast Nat.le_succ m
  have hmul : Multipliable fun m : ℕ => (1 - (X : PowerSeries ℤ) * PowerSeries.X ^ m) ^ 3 := by
    apply PowerSeries.WithPiTopology.multipliable_of_tendsto_order_sub_one
    apply tendsto_nhds_top_mono ENat.tendsto_nat_nhds_top
    apply Filter.Eventually.of_forall
    intro m
    show (m : ℕ∞) ≤ ((1 - (X : PowerSeries ℤ) * PowerSeries.X ^ m) ^ 3 - 1).order
    apply PowerSeries.le_order
    intro i hi
    have hi' : i < m := by exact_mod_cast hi
    have heq : ((1 - (X : PowerSeries ℤ) * PowerSeries.X ^ m) ^ 3 - 1)
        = (-3 : ℤ) • X ^ (m + 1) + (3 : ℤ) • X ^ (2 * (m + 1)) - X ^ (3 * (m + 1)) := by
      ring
    rw [heq]
    simp only [map_sub, map_add, map_smul, coeff_X_pow, smul_eq_mul]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring
  have hprodeq : (∏ j ∈ Finset.Iio (d + 1), (1 - (X : PowerSeries ℤ) ^ (j + 1)) ^ 3)
      = ∏ j ∈ Finset.Iio (d + 1), (1 - (X : PowerSeries ℤ) * X ^ j) ^ 3 := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [pow_succ' (X : PowerSeries ℤ) j]
  rw [hprodeq, qPochhammerInf_eq_tprod HasEval.X, ← Multipliable.tprod_pow hmul0]
  rw [PowerSeries.WithPiTopology.coeff_tprod_of_lt_order_sub_one hmul (N := d + 1) (i := d)]
  intro m hm
  show (d : ℕ∞) < ((1 - (X : PowerSeries ℤ) * PowerSeries.X ^ m) ^ 3 - 1).order
  apply lt_of_lt_of_le (b := (m : ℕ∞))
  · exact_mod_cast (by omega : d < m)
  · apply PowerSeries.le_order
    intro i hi
    have hi' : i < m := by exact_mod_cast hi
    have heq : ((1 - (X : PowerSeries ℤ) * PowerSeries.X ^ m) ^ 3 - 1)
        = (-3 : ℤ) • X ^ (m + 1) + (3 : ℤ) • X ^ (2 * (m + 1)) - X ^ (3 * (m + 1)) := by
      ring
    rw [heq]
    simp only [map_sub, map_add, map_smul, coeff_X_pow, smul_eq_mul]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring

noncomputable instance : UniformSpace (LaurentPolynomial ℤ) := ⊥

abbrev Rbi := PowerSeries (LaurentPolynomial ℤ)

noncomputable def zvar : Rbi := PowerSeries.C (LaurentPolynomial.T 1)
noncomputable def zinv : Rbi := PowerSeries.C (LaurentPolynomial.T (-1))

noncomputable def Dcoeff (f : LaurentPolynomial ℤ) : ℤ := f.sum (fun m c => m * c)

noncomputable def Dop (F : Rbi) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => Dcoeff ((PowerSeries.coeff n) F))

noncomputable def PRODbi : Rbi :=
  qPochhammerInf (X : Rbi) X * qPochhammerInf zvar X * qPochhammerInf (zinv * X) X

noncomputable def THETAbi : Rbi :=
  ∑' (n : ℤ), abPow (-zvar) (-(zinv * X)) n * (X : Rbi) ^ n.natAbs.choose 2

theorem jtp_bivariate : PRODbi = THETAbi := by
  unfold PRODbi THETAbi
  rw [show (qPochhammerInf zvar X : Rbi) = qPochhammerInf (-(-zvar)) X by rw [neg_neg],
      show (qPochhammerInf (zinv * X) X : Rbi) = qPochhammerInf (-(-(zinv * X))) X by rw [neg_neg]]
  apply jacobi_triple_product PowerSeries.HasEval.X
  show (-zvar) * (-(zinv * X)) = X
  unfold zvar zinv
  rw [neg_mul_neg]
  rw [show PowerSeries.C (LaurentPolynomial.T 1) * (PowerSeries.C (LaurentPolynomial.T (-1)) * X) = (PowerSeries.C (LaurentPolynomial.T 1) * PowerSeries.C (LaurentPolynomial.T (-1))) * X by ring]
  rw [← map_mul, ← LaurentPolynomial.T_add]
  simp

theorem Dop_THETAbi : Dop THETAbi = - jacobiSeries := by
  let DH : LaurentPolynomial ℤ →+ ℤ :=
    { toFun := fun f => f.sum (fun m c => m * c)
      map_zero' := Finsupp.sum_zero_index
      map_add' := fun f g => Finsupp.sum_add_index' (fun i => by simp) (fun i b₁ b₂ => by ring) }
  have coeff_DopD : ∀ (n : ℕ) (F : Rbi), coeff n (Dop F) = DH (coeff n F) := by
    intro n F; simp only [Dop, coeff_mk]; rfl
  have DH_C_mul_T : ∀ (c : ℤ) (m : ℤ),
      DH (LaurentPolynomial.C c * LaurentPolynomial.T m) = m * c := by
    intro c m
    show (LaurentPolynomial.C c * LaurentPolynomial.T m).sum (fun j d => (j : ℤ) * d) = m * c
    rw [← LaurentPolynomial.single_eq_C_mul_T, Finsupp.sum_single_index (by simp)]
  set Tn : ℤ → Rbi := fun n => abPow (-zvar) (-(zinv * X)) n * (X : Rbi) ^ n.natAbs.choose 2 with hTndef
  have Dop_C_mul_Xpow : ∀ (c : LaurentPolynomial ℤ) (e : ℕ),
      Dop (PowerSeries.C c * X ^ e) = PowerSeries.C (DH c) * X ^ e := by
    intro c e
    ext d
    rw [coeff_DopD, coeff_C_mul, coeff_X_pow, coeff_C_mul, coeff_X_pow]
    by_cases h : d = e <;> simp [h]
  have abeq : (-zvar) * (-(zinv * X)) = (X : Rbi) := by
    unfold zvar zinv
    rw [neg_mul_neg]
    rw [show PowerSeries.C (LaurentPolynomial.T 1) * (PowerSeries.C (LaurentPolynomial.T (-1)) * X)
          = (PowerSeries.C (LaurentPolynomial.T 1) * PowerSeries.C (LaurentPolynomial.T (-1))) * X by ring]
    rw [← map_mul, ← LaurentPolynomial.T_add]; simp
  have hTn : HasSum Tn THETAbi := by
    have h := jacobi_triple_product_hasSum (q := (X:Rbi)) (a := -zvar) (b := -(zinv*X))
      PowerSeries.HasEval.X abeq
    have hsum : Summable Tn := by rw [hTndef]; exact h.summable
    rw [THETAbi, hTndef]
    exact hsum.hasSum
  have hDopTheta : HasSum (fun n => Dop (Tn n)) (Dop THETAbi) := by
    rw [hasSum_iff_hasSum_coeff ℤ]
    intro d
    have hc : HasSum (fun n => coeff d (Tn n)) (coeff d THETAbi) :=
      hTn.map (coeff d) (continuous_coeff (LaurentPolynomial ℤ) d)
    simp only [coeff_DopD]
    exact hc.map DH continuous_of_discreteTopology
  have hpos : ∀ k : ℕ, Dop (Tn (k:ℤ)) = PowerSeries.C ((k:ℤ) * (-1)^k) * X^(k.choose 2) := by
    intro k
    rw [hTndef]
    simp only
    rw [abPow_nat, show ((k:ℤ).natAbs) = k by simp]
    rw [show ((-zvar)^k) = PowerSeries.C (LaurentPolynomial.C ((-1:ℤ)^k) * LaurentPolynomial.T (k:ℤ)) by
      rw [neg_pow, zvar, ← map_pow, LaurentPolynomial.T_pow, show ((k:ℤ) * 1) = (k:ℤ) by ring, map_mul]
      congr 1; simp [map_pow]]
    rw [Dop_C_mul_Xpow, DH_C_mul_T]
  have hneg : ∀ k : ℕ, Dop (Tn (-(k:ℤ))) = PowerSeries.C (-(k:ℤ) * (-1)^k) * X^(k + k.choose 2) := by
    intro k
    rw [hTndef]
    simp only
    rw [abPow_neg_nat, show ((-(k:ℤ)).natAbs) = k by simp]
    rw [show ((-(zinv*X))^k)
          = PowerSeries.C (LaurentPolynomial.C ((-1:ℤ)^k) * LaurentPolynomial.T (-(k:ℤ))) * X^k by
      rw [neg_pow, mul_pow, zinv, ← map_pow, LaurentPolynomial.T_pow,
          show ((k:ℤ) * (-1)) = (-(k:ℤ)) by ring, map_mul]
      rw [mul_assoc]; congr 1; simp [map_pow]]
    rw [mul_assoc, ← pow_add, Dop_C_mul_Xpow, DH_C_mul_T]
  have choose_two_succ : ∀ t : ℕ, (t+1).choose 2 = Tri t := by
    intro t
    have h1 := two_mul_Tri t
    have h2 : 2 * (t+1).choose 2 = (t+1) * t := by
      rw [Nat.choose_two_right, Nat.mul_div_cancel']
      · simp
      · exact (Nat.even_mul_pred_self (t+1)).two_dvd
    nlinarith [h1, h2]
  have add_choose_two : ∀ t : ℕ, t + t.choose 2 = Tri t := by
    intro t
    have h1 := two_mul_Tri t
    have h2 : 2 * (t.choose 2) + 2*t = t*t + t := by
      rw [Nat.choose_two_right, Nat.mul_div_cancel']
      · cases t with | zero => simp | succ n => simp; ring
      · exact (Nat.even_mul_pred_self t).two_dvd
    nlinarith [h1, h2]
  have hterm : ∀ t : ℕ, Dop (Tn ((t:ℤ)+1)) + Dop (Tn (-(t:ℤ))) = -(js t) := by
    intro t
    rw [show ((t:ℤ)+1) = ((t+1 : ℕ):ℤ) by push_cast; ring, hpos (t+1), hneg t,
        choose_two_succ t, add_choose_two t]
    rw [js, ← add_mul, ← map_add, ← neg_mul, ← map_neg]
    congr 2
    push_cast
    rw [pow_succ]; ring
  let myEquiv : ℕ ⊕ ℕ ≃ ℤ :=
    { toFun := fun s => match s with | Sum.inl t => (t:ℤ) + 1 | Sum.inr t => -(t:ℤ)
      invFun := fun n => if 0 < n then Sum.inl (n.toNat - 1) else Sum.inr (-n).toNat
      left_inv := by rintro (t | t) <;> simp
      right_inv := by
        intro n
        simp only
        rcases lt_or_ge 0 n with h | h
        · rw [if_pos h]; show (↑(n.toNat - 1) : ℤ) + 1 = n; omega
        · rw [if_neg (by omega)]; show (-↑((-n).toNat) : ℤ) = n; omega }
  have hsumF : Summable (fun n => Dop (Tn n)) := hDopTheta.summable
  have hposS : Summable (fun t : ℕ => Dop (Tn ((t:ℤ)+1))) := by
    have hinj : Function.Injective (fun t : ℕ => ((t:ℤ)+1)) := by
      intro a b hab; simp only at hab; omega
    exact (hsumF.comp_injective hinj)
  have hnegS : Summable (fun t : ℕ => Dop (Tn (-(t:ℤ)))) := by
    have hinj : Function.Injective (fun t : ℕ => (-(t:ℤ))) := by
      intro a b hab; simp only at hab; omega
    exact (hsumF.comp_injective hinj)
  have hF : HasSum (fun n => Dop (Tn n)) (∑' t : ℕ, Dop (Tn ((t:ℤ)+1)) + ∑' t : ℕ, Dop (Tn (-(t:ℤ)))) := by
    rw [← Equiv.hasSum_iff myEquiv]
    have hsumtype : HasSum (fun s => (fun n => Dop (Tn n)) (myEquiv s))
        (∑' t : ℕ, Dop (Tn ((t:ℤ)+1)) + ∑' t : ℕ, Dop (Tn (-(t:ℤ)))) := by
      apply HasSum.sum
      · exact hposS.hasSum
      · exact hnegS.hasSum
    exact hsumtype
  have hhalf : HasSum (fun t : ℕ => Dop (Tn ((t:ℤ)+1)) + Dop (Tn (-(t:ℤ))))
      (∑' t : ℕ, Dop (Tn ((t:ℤ)+1)) + ∑' t : ℕ, Dop (Tn (-(t:ℤ)))) :=
    (hposS.hasSum).add (hnegS.hasSum)
  have hjsneg : HasSum (fun t : ℕ => -(js t)) (-jacobiSeries) := hasSum_js.neg
  have heq : (∑' t : ℕ, Dop (Tn ((t:ℤ)+1)) + ∑' t : ℕ, Dop (Tn (-(t:ℤ)))) = -jacobiSeries := by
    have hcong : HasSum (fun t : ℕ => -(js t))
        (∑' t : ℕ, Dop (Tn ((t:ℤ)+1)) + ∑' t : ℕ, Dop (Tn (-(t:ℤ)))) := by
      apply hhalf.congr_fun
      intro t; exact (hterm t).symm
    exact hcong.unique hjsneg
  rw [heq] at hF
  exact hDopTheta.unique hF

noncomputable def DcoeffHom : LaurentPolynomial ℤ →+ ℤ where
  toFun f := f.sum (fun m c => m * c)
  map_zero' := Finsupp.sum_zero_index
  map_add' f g := Finsupp.sum_add_index' (fun i => by simp) (fun i b₁ b₂ => by ring)

noncomputable def ev1lp : LaurentPolynomial ℤ →+* ℤ := LaurentPolynomial.eval₂ (RingHom.id ℤ) 1

noncomputable def ev1 : Rbi →+* PowerSeries ℤ := PowerSeries.map ev1lp

@[simp] lemma coeff_Dop (n : ℕ) (F : Rbi) : coeff n (Dop F) = DcoeffHom (coeff n F) := by
  simp only [Dop, coeff_mk]; rfl
@[simp] lemma coeff_ev1 (n : ℕ) (F : Rbi) : coeff n (ev1 F) = ev1lp (coeff n F) := by
  simp [ev1, PowerSeries.coeff_map]
@[simp] lemma DcoeffHom_C_mul_T (c : ℤ) (n : ℤ) :
    DcoeffHom (LaurentPolynomial.C c * LaurentPolynomial.T n) = n * c := by
  show (LaurentPolynomial.C c * LaurentPolynomial.T n).sum (fun m d => (m : ℤ) * d) = n * c
  rw [← LaurentPolynomial.single_eq_C_mul_T, Finsupp.sum_single_index (by simp)]
@[simp] lemma ev1lp_C_mul_T (c : ℤ) (n : ℤ) :
    ev1lp (LaurentPolynomial.C c * LaurentPolynomial.T n) = c := by
  show (LaurentPolynomial.eval₂ (RingHom.id ℤ) 1) (LaurentPolynomial.C c * LaurentPolynomial.T n) = c
  rw [map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T]; simp
@[simp] lemma DcoeffHom_C (c : ℤ) : DcoeffHom (LaurentPolynomial.C c) = 0 := by
  have : LaurentPolynomial.C c = LaurentPolynomial.C c * LaurentPolynomial.T 0 := by simp
  rw [this, DcoeffHom_C_mul_T]; ring
@[simp] lemma DcoeffHom_one : DcoeffHom (1 : LaurentPolynomial ℤ) = 0 := by
  have : (1 : LaurentPolynomial ℤ) = LaurentPolynomial.C 1 := by simp
  rw [this, DcoeffHom_C]
@[simp] lemma DcoeffHom_T (n : ℤ) : DcoeffHom (LaurentPolynomial.T n) = n := by
  show (LaurentPolynomial.T n).sum (fun m c => (m : ℤ) * c) = n
  rw [LaurentPolynomial.T, Finsupp.sum_single_index (by simp)]; simp
@[simp] lemma ev1lp_C (c : ℤ) : ev1lp (LaurentPolynomial.C c) = c := by
  show (LaurentPolynomial.eval₂ (RingHom.id ℤ) 1) (LaurentPolynomial.C c) = c
  rw [LaurentPolynomial.eval₂_C]; simp

lemma DcoeffHom_mul (f g : LaurentPolynomial ℤ) :
    DcoeffHom (f * g) = ev1lp f * DcoeffHom g + DcoeffHom f * ev1lp g := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [add_mul, map_add, hp, hq]; ring
  | C_mul_T m a =>
    induction g using LaurentPolynomial.induction_on' with
    | add p q hp hq => simp only [mul_add, map_add, hp, hq]; ring
    | C_mul_T k b =>
      rw [show LaurentPolynomial.C a * LaurentPolynomial.T m
              * (LaurentPolynomial.C b * LaurentPolynomial.T k)
            = LaurentPolynomial.C (a * b) * LaurentPolynomial.T (m + k) by
          rw [map_mul, LaurentPolynomial.T_add]; ring]
      simp only [DcoeffHom_C_mul_T, ev1lp_C_mul_T]; ring

lemma Dop_mul (F G : Rbi) : Dop (F * G) = ev1 F * Dop G + Dop F * ev1 G := by
  ext n
  rw [coeff_Dop, map_add, PowerSeries.coeff_mul, PowerSeries.coeff_mul, PowerSeries.coeff_mul,
      map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [coeff_Dop, coeff_ev1]
  rw [DcoeffHom_mul]

lemma Dop_map_C (g : PowerSeries ℤ) :
    Dop (PowerSeries.map (LaurentPolynomial.C (R := ℤ)) g) = 0 := by
  ext n
  rw [coeff_Dop, PowerSeries.coeff_map]
  show DcoeffHom (LaurentPolynomial.C ((coeff n) g)) = (0 : PowerSeries ℤ).coeff n
  rw [DcoeffHom_C]; simp

lemma ev1_X : ev1 (X : Rbi) = X := by unfold ev1; rw [PowerSeries.map_X]
lemma ev1_zvar : ev1 zvar = 1 := by
  unfold ev1 zvar; rw [PowerSeries.map_C]
  show PowerSeries.C (ev1lp (LaurentPolynomial.T 1)) = 1
  rw [show ev1lp (LaurentPolynomial.T 1) = 1 by
        show (LaurentPolynomial.eval₂ (RingHom.id ℤ) 1) (LaurentPolynomial.T 1) = 1
        rw [LaurentPolynomial.eval₂_T]; simp, map_one]
lemma ev1_zinv_mul_X : ev1 (zinv * X) = X := by
  unfold ev1 zinv; rw [map_mul, PowerSeries.map_C, PowerSeries.map_X]
  show PowerSeries.C (ev1lp (LaurentPolynomial.T (-1))) * X = X
  rw [show ev1lp (LaurentPolynomial.T (-1)) = 1 by
        show (LaurentPolynomial.eval₂ (RingHom.id ℤ) 1) (LaurentPolynomial.T (-1)) = 1
        rw [LaurentPolynomial.eval₂_T]; simp, map_one, one_mul]

@[simp] lemma coeff_zvar_zero : coeff 0 zvar = LaurentPolynomial.T 1 := by
  simp [zvar, PowerSeries.coeff_C]
lemma coeff_zvar_succ (n : ℕ) (h : n ≠ 0) : coeff n zvar = 0 := by
  simp [zvar, PowerSeries.coeff_C, h]

lemma Dop_one_sub_zvar : Dop (1 - zvar) = -1 := by
  ext n
  rw [coeff_Dop, map_sub]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [coeff_zvar_succ n (by omega)]
    rw [show ((coeff n) (1 : Rbi)) = 0 by rw [PowerSeries.coeff_one, if_neg (by omega)]]
    rw [show ((coeff n) (-1 : PowerSeries ℤ)) = 0 by
          rw [map_neg, PowerSeries.coeff_one, if_neg (by omega), neg_zero]]
    simp

lemma ev1_one_sub_zvar : ev1 (1 - zvar) = 0 := by
  rw [map_sub, map_one, ev1_zvar, sub_self]

open PowerSeries.DiscreteTopology in
lemma Dop_phi_Rbi_zero : Dop (qPochhammerInf (X : Rbi) X) = 0 := by
  rw [show (qPochhammerInf (X : Rbi) X)
        = PowerSeries.map (LaurentPolynomial.C (R := ℤ)) (qPochhammerInf X X) by
        rw [map_qPochhammerInf (PowerSeries.map (LaurentPolynomial.C (R := ℤ)))
              continuous_map _ PowerSeries.HasEval.X]
        congr 1 <;> rw [PowerSeries.map_X]]
  exact Dop_map_C _

open PowerSeries.DiscreteTopology in
lemma ev1_phi_Rbi : ev1 (qPochhammerInf (X : Rbi) X) = qPochhammerInf X X := by
  unfold ev1
  rw [map_qPochhammerInf (PowerSeries.map ev1lp) continuous_map _ PowerSeries.HasEval.X,
      PowerSeries.map_X]

open PowerSeries.DiscreteTopology in
lemma ev1_C_fac : ev1 (qPochhammerInf (zinv * X) X) = qPochhammerInf X X := by
  unfold ev1
  rw [map_qPochhammerInf (PowerSeries.map ev1lp) continuous_map _ PowerSeries.HasEval.X]
  show qPochhammerInf (ev1 (zinv * X)) (ev1 X) = qPochhammerInf X X
  rw [ev1_zinv_mul_X, ev1_X]

open PowerSeries.DiscreteTopology in
lemma ev1_B : ev1 (qPochhammerInf zvar X) = 0 := by
  unfold ev1
  rw [map_qPochhammerInf (PowerSeries.map ev1lp) continuous_map _ PowerSeries.HasEval.X]
  show qPochhammerInf (ev1 zvar) (ev1 X) = 0
  rw [ev1_zvar, qPochhammerInf_one]

open PowerSeries.DiscreteTopology in
lemma ev1_PB : ev1 (qPochhammerInf (zvar * X) X) = qPochhammerInf X X := by
  unfold ev1
  rw [map_qPochhammerInf (PowerSeries.map ev1lp) continuous_map _ PowerSeries.HasEval.X]
  show qPochhammerInf (ev1 (zvar * X)) (ev1 X) = qPochhammerInf X X
  rw [show ev1 (zvar * X) = X by rw [map_mul, ev1_zvar, ev1_X, one_mul], ev1_X]

open PowerSeries.DiscreteTopology in
lemma Dop_B : Dop (qPochhammerInf zvar X) = -(qPochhammerInf X X) := by
  rw [qPochhammerInf_eq_one_sub_mul_qPochhammerInf PowerSeries.HasEval.X, Dop_mul,
      ev1_one_sub_zvar, Dop_one_sub_zvar, ev1_PB]
  ring

open PowerSeries.DiscreteTopology in
theorem Dop_PRODbi :
    Dop PRODbi = - (qPochhammerInf (X : PowerSeries ℤ) X) ^ 3 := by
  unfold PRODbi
  rw [Dop_mul, Dop_mul, map_mul, Dop_phi_Rbi_zero, ev1_phi_Rbi, ev1_B, ev1_C_fac, Dop_B]
  ring

open PowerSeries.DiscreteTopology in
theorem qPochhammerCube_eq_jacobiSeries :
    (qPochhammerInf (X : PowerSeries ℤ) X) ^ 3 = jacobiSeries := by
  have hD : Dop PRODbi = Dop THETAbi := by rw [jtp_bivariate]
  rw [Dop_THETAbi, Dop_PRODbi] at hD
  exact neg_injective hD

theorem jacobi_master : eulerCube = jacobiSeries :=
  eulerCube_eq_qPochhammerCube.trans qPochhammerCube_eq_jacobiSeries

theorem coeff_finprod_cube_eq_jacobiSeries (d : ℕ) :
    coeff d (∏ j ∈ Finset.Iio (d + 1), (1 - (X : PowerSeries ℤ) ^ (j + 1)) ^ 3)
      = coeff d jacobiSeries := by
  rw [← coeff_eulerCube_eq_coeff_finprod d, jacobi_master]

theorem coeff_eulerCube_eq_jacobiSeries (d : ℕ) :
    coeff d eulerCube = coeff d jacobiSeries := by
  rw [coeff_eulerCube_eq_coeff_finprod d, coeff_finprod_cube_eq_jacobiSeries d]

-- Main Statement(s)

/-- **Jacobi's identity.** In the ring of formal power series `ℤ⟦q⟧`,
`∏_{n=1}^{∞} (1 - q^n)^3 = ∑_{k=0}^{∞} (-1)^k (2k+1) q^{(k^2+k)/2}`. -/
theorem jacobi_cube_euler : eulerCube = jacobiSeries :=
  PowerSeries.ext (fun d => coeff_eulerCube_eq_jacobiSeries d)

/-
Correctness statements anchoring the meaning of the `tprod`/`tsum` definitions in
terms of the coefficients of the formal power series (the coefficient form from
the Remarks). These guard against the statement being vacuously true because of
junk values returned by `tprod`/`tsum` when convergence fails.
-/

/-- Coefficient form, triangular case: the coefficient of `q^{T_k}` in
`∏_{n=1}^{∞} (1 - q^n)^3` is `(-1)^k (2k+1)`, where `T_k = (k^2+k)/2`. -/
theorem jacobi_coeff_triangular (k : ℕ) :
    (coeff (R := ℤ) ((k ^ 2 + k) / 2)) eulerCube = (-1 : ℤ) ^ k * (2 * (k : ℤ) + 1) := by
  have hd : ((k ^ 2 + k) / 2) = Tri k := rfl
  rw [hd, coeff_eulerCube_eq_jacobiSeries, coeff_jacobiSeries_tri]

/-- Coefficient form, non-triangular case: the coefficient of `q^m` in
`∏_{n=1}^{∞} (1 - q^n)^3` is `0` whenever `m` is not a triangular number. -/
theorem jacobi_coeff_nontriangular (m : ℕ) (h : ∀ k : ℕ, (k ^ 2 + k) / 2 ≠ m) :
    (coeff (R := ℤ) m) eulerCube = 0 := by
  rw [coeff_eulerCube_eq_jacobiSeries]
  exact coeff_jacobiSeries_nontri m (fun k => h k)
