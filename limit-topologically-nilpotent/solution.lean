import Mathlib
import RogersRamanujan

open Filter Topology Pointwise

lemma pow_pos_mem_of_mul_self_le {R : Type*} [CommRing R]
    {M : AddSubgroup R} (hM : M * M ≤ M)
    {x : R} (hx : x ∈ M) {k : ℕ} (hk : 1 ≤ k) :
    x ^ k ∈ M := by
  induction k, hk using Nat.le_induction with
  | base => simpa using hx
  | succ n _ ih =>
    rw [pow_succ]
    exact AddSubgroup.mul_le_iff.mp hM _ ih _ hx

lemma mul_diff_mem_of_subgroup {R : Type*} [CommRing R]
    {M₀ M : AddSubgroup R}
    (hM_mul : M * M ≤ M) (hM_le : M ≤ M₀)
    {l d : R} (hd : d ∈ M)
    (hM_l : ∀ x ∈ M, l * x ∈ M₀) :
    (l - d) * d ∈ M₀ := by
  rw [show (l - d) * d = l * d - d * d by ring]
  exact M₀.sub_mem (hM_l d hd) (hM_le (AddSubgroup.mul_le_iff.mp hM_mul d hd d hd))

lemma factorize_pow_mul_pow {R : Type*} [CommRing R]
    (a d : R) {m n : ℕ} (h : 2 * m ≤ n) :
    a ^ m * d ^ (n - m) = (a * d) ^ m * d ^ (n - 2 * m) := by
  rw [mul_pow, mul_assoc, ← pow_add, show m + (n - 2 * m) = n - m by omega]

lemma binomial_term_mem_subgroup {R : Type*} [CommRing R]
    {M₀ M : AddSubgroup R}
    (hM₀_mul : M₀ * M₀ ≤ M₀) (hM_mul : M * M ≤ M)
    (hM_le : M ≤ M₀)
    {a d : R} (hd_M : d ∈ M)
    (had : a * d ∈ M₀)
    {Q : ℕ} (ha_pow : ∀ k, Q ≤ k → a ^ k ∈ M₀)
    {n m : ℕ} (hn : 2 * Q ≤ n) (hm : m ∈ Finset.range (n + 1)) :
    a ^ m * d ^ (n - m) ∈ M₀ := by
  rw [Finset.mem_range] at hm
  by_cases hQm : Q ≤ m
  · by_cases hnm : n - m = 0
    · simp [hnm, ha_pow m hQm]
    · exact AddSubgroup.mul_le_iff.mp hM₀_mul _ (ha_pow m hQm) _
        (hM_le (pow_pos_mem_of_mul_self_le hM_mul hd_M (by omega)))
  · push_neg at hQm
    obtain rfl | hm0 := eq_or_ne m 0
    · simpa using hM_le (pow_pos_mem_of_mul_self_le hM_mul hd_M (by omega))
    · rw [factorize_pow_mul_pow a d (by omega)]
      exact AddSubgroup.mul_le_iff.mp hM₀_mul _
        (pow_pos_mem_of_mul_self_le hM₀_mul had (by omega)) _
        (hM_le (pow_pos_mem_of_mul_self_le hM_mul hd_M (by omega)))

lemma pow_mem_of_binomial {R : Type*} [CommRing R]
    {M₀ M : AddSubgroup R}
    (hM₀_mul : M₀ * M₀ ≤ M₀) (hM_mul : M * M ≤ M)
    (hM_le : M ≤ M₀)
    {a d : R} (hd_M : d ∈ M)
    (had : a * d ∈ M₀)
    {Q : ℕ} (ha_pow : ∀ k, Q ≤ k → a ^ k ∈ M₀)
    {n : ℕ} (hn : 2 * Q ≤ n) :
    (a + d) ^ n ∈ M₀ := by
  simp_rw [add_pow, ← nsmul_eq_mul']
  exact sum_mem fun m hm =>
    M₀.nsmul_mem (binomial_term_mem_subgroup hM₀_mul hM_mul hM_le hd_M had ha_pow hn hm) _

theorem isTopologicallyNilpotent_of_tendsto
    {R : Type*} [CommRing R] [TopologicalSpace R] [StrongNonarchimedeanRing R]
    {f : ℕ → R} {l : R} (hf : Tendsto f atTop (𝓝 l)) (hnf : ∀ n, IsTopologicallyNilpotent (f n)) :
    IsTopologicallyNilpotent l := by
  show Tendsto (fun n => l ^ n) atTop (𝓝 0)
  rw [hasBasis_nhds_zero_addSubgroup_mul_le.tendsto_right_iff]
  intro M₀ ⟨hM₀_open, hM₀_mul⟩
  obtain ⟨M, hM_open, hM_mul, hM_le, hM_l⟩ := exists_addSubgroup_mul_le_sub hM₀_open l
  have hf_sub : Tendsto (fun n => f n - l) atTop (𝓝 0) := by
    have := hf.sub (tendsto_const_nhds (x := l))
    rwa [sub_self] at this
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp
    (hf_sub.eventually (hM_open.mem_nhds M.zero_mem))
  have hd_M : l - f n₀ ∈ M := by
    simpa [neg_sub] using M.neg_mem (hn₀ n₀ le_rfl)
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.mp
    ((hnf n₀).eventually (hM₀_open.mem_nhds M₀.zero_mem))
  have had : f n₀ * (l - f n₀) ∈ M₀ := by
    simpa [sub_sub_cancel] using mul_diff_mem_of_subgroup hM_mul hM_le hd_M hM_l
  rw [Filter.eventually_atTop]
  exact ⟨2 * Q, fun n hn => by
    rw [show l = f n₀ + (l - f n₀) by ring]
    exact pow_mem_of_binomial hM₀_mul hM_mul hM_le hd_M had hQ hn⟩
