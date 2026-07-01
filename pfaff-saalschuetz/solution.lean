import Mathlib

/-! # Basic definitions in q-theory -/

open Finset SummationFilter

section CommSemiring
variable {R : Type*} [CommSemiring R]

/-- $q$-analogue of integer, $[n]_q = 1 + q + q^2 + \dots + q^{n-1}$. -/
def qInt (q : R) (n : ℕ) : R :=
  ∑ i ∈ range n, q ^ i

/-- $q$-factorial, $[n]_q! = [1]_q [2]_q \dots [n]_q$ -/
def qFactorial (q : R) (n : ℕ) : R :=
  ∏ i ∈ range n, qInt q (i + 1)

/-- q-binomial coefficients. q-analogue of `Nat.choose`. -/
def qChoose (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qChoose q n k + q ^ (k + 1) * qChoose q n (k + 1)

end CommSemiring

/-- $q$-Pochhammer symbol, $(a;q)_n = \prod_{i=0}^{n-1} (1 - a*q^i)$

To enable the notation `(a; q)_n`, use `open scoped QTheory`.

For the unsafe version (use with caution) `(a)_n` which uses any local variable called `q`, use
`open scoped QTheoryUnsafe`.
-/
def qPochhammer {R : Type*} [CommRing R] (a q : R) (n : ℕ) : R :=
  ∏ i ∈ range n, (1 - a * q ^ i)

/-- Infinite $q$-Pochhammer symbol, $(a;q)_\infty = \prod_{i=0}^{\infty} (1 - a*q^i)$

To enable the notation `(a; q)_∞`, use `open scoped QTheory`.

For the unsafe version (use with caution) `(a)_∞` which uses any local variable called `q`, use
`open scoped QTheoryUnsafe`. -/
noncomputable def qPochhammerInf {R : Type*} [TopologicalSpace R] [CommRing R] (a q : R) : R :=
  ∏'[conditional ℕ] i, (1 - a * q ^ i)

namespace QTheory

@[inherit_doc] scoped notation:max "(" a "; " q ")_" n:arg => qPochhammer a q n
@[inherit_doc] scoped notation:max "(" a "; " q ")_∞" => qPochhammerInf a q

end QTheory

namespace QTheoryUnsafe

set_option hygiene false
@[inherit_doc] scoped notation:max "(" a ")_" n:arg => qPochhammer a q n
@[inherit_doc] scoped notation:max "(" a ")_∞" => qPochhammerInf a q

end QTheoryUnsafe

open QTheoryUnsafe

theorem qPochhammer_succ_right {R : Type*} [CommRing R] (x q : R) (m : ℕ) :
    qPochhammer x q (m + 1) = qPochhammer x q m * (1 - x * q ^ m) := by
  unfold qPochhammer
  rw [Finset.prod_range_succ]

theorem qPochhammer_succ_left {R : Type*} [CommRing R] (x q : R) (m : ℕ) :
    qPochhammer x q (m + 1) = (1 - x) * qPochhammer (x * q) q m := by
  induction m with
  | zero => simp [qPochhammer]
  | succ m ih => rw [qPochhammer_succ_right, ih, qPochhammer_succ_right]; ring

theorem qChoose_zero_right {R : Type*} [CommSemiring R] (q : R) (n : ℕ) :
    qChoose q n 0 = 1 := by cases n <;> rfl

theorem qChoose_eq_zero_of_lt {R : Type*} [CommSemiring R] (q : R) :
    ∀ n k, n < k → qChoose q n k = 0 := by
  intro n
  induction n with
  | zero => intro k hk; cases k with | zero => omega | succ k => rfl
  | succ n ih =>
    intro k hk
    cases k with
    | zero => omega
    | succ k => unfold qChoose; rw [ih k (by omega), ih (k+1) (by omega)]; ring

theorem qChoose_self {R : Type*} [CommSemiring R] (q : R) (n : ℕ) :
    qChoose q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show qChoose q n n + q ^ (n + 1) * qChoose q n (n + 1) = 1
    rw [ih]
    have : qChoose q n (n + 1) = 0 := qChoose_eq_zero_of_lt q n (n + 1) (by omega)
    rw [this]; ring

theorem qChoose_one_right {R : Type*} [CommSemiring R] (q : R) (n : ℕ) :
    qChoose q n 1 = ∑ i ∈ range n, q ^ i := by
  induction n with
  | zero => simp [qChoose]
  | succ n ih =>
    show qChoose q n 0 + q ^ 1 * qChoose q n 1 = _
    rw [qChoose_zero_right, ih, Finset.sum_range_succ' (fun i => q ^ i) n]
    rw [pow_one, Finset.mul_sum]
    simp only [pow_succ, pow_zero, mul_comm]
    ring

theorem qChoose_rel {R : Type*} [CommRing R] (q : R) : ∀ n k, k < n →
    qChoose q n (k + 1) * (q ^ (k + 1) - 1) = qChoose q n k * (q ^ (n - k) - 1) := by
  intro n
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [qChoose_zero_right, one_mul, qChoose_one_right]
      have : (∑ i ∈ range (n + 1), q ^ i) * (q ^ 1 - 1) = q ^ (n + 1) - 1 := by
        rw [pow_one]; exact geom_sum_mul q (n + 1)
      have e0 : n + 1 - 0 = n + 1 := by omega
      rw [e0]; exact this
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hkpos)
      show (qChoose q n (j + 1) + q ^ (j + 2) * qChoose q n (j + 2)) * (q ^ (j + 2) - 1)
          = (qChoose q n j + q ^ (j + 1) * qChoose q n (j + 1)) * (q ^ (n + 1 - (j + 1)) - 1)
      have hj : j + 1 < n + 1 := hk
      rcases Nat.lt_or_ge (j + 1) n with hlt | hge
      · have h1 := ih j (by omega)
        have h2 := ih (j + 1) hlt
        have e1 : n + 1 - (j + 1) = n - j := by omega
        have e2 : n - j = (n - (j + 1)) + 1 := by omega
        rw [e1, e2]
        rw [e2] at h1
        have e3 : j + 2 = (j + 1) + 1 := by omega
        rw [e3]
        simp only [pow_succ] at h1 h2 ⊢
        linear_combination h1 + q ^ (j + 1) * q * h2
      · have hjn : j + 1 = n := by omega
        subst hjn
        have hz : qChoose q (j + 1) (j + 2) = 0 := qChoose_eq_zero_of_lt q (j + 1) (j + 2) (by omega)
        rw [hz]
        have h1 := ih j (by omega)
        have e1 : j + 1 + 1 - (j + 1) = 1 := by omega
        have e2 : (j + 1) - j = 1 := by omega
        rw [e2] at h1
        rw [e1]
        have e3 : j + 2 = (j + 1) + 1 := by omega
        rw [e3]
        simp only [pow_succ, pow_one] at h1 ⊢
        linear_combination h1

theorem sum_recurrence {R : Type*} [CommRing R] (a b c q : R) (n : ℕ) :
    ∑ k ∈ range (n + 1 + 1),
      qChoose q (n + 1) k * (a)_k * (b)_k * c ^ k * (c)_(n + 1 - k) *
        (a * b * c * q ^ k)_(n + 1 - k) =
    (1 - a * c * q ^ n) * (1 - b * c * q ^ n) *
      ∑ k ∈ range (n + 1),
        qChoose q n k * (a)_k * (b)_k * c ^ k * (c)_(n - k) * (a * b * c * q ^ k)_(n - k) := by
  set F : ℕ → ℕ → R := fun m k =>
    qChoose q m k * (a)_k * (b)_k * c ^ k * (c)_(m - k) * (a * b * c * q ^ k)_(m - k) with hF
  set mu : R := (1 - a * c * q ^ n) * (1 - b * c * q ^ n) with hmu
  set G : ℕ → R := fun k =>
    if k = 0 then 0
    else -c * q ^ (n + 1 - k) * (1 - a * q ^ (k - 1)) * (1 - b * q ^ (k - 1)) * F n (k - 1)
    with hG
  have hFval : ∀ m k, F m k =
      qChoose q m k * (a)_k * (b)_k * c ^ k * (c)_(m - k) * (a * b * c * q ^ k)_(m - k) := by
    intro m k; rw [hF]
  have key : ∀ k, k < n + 1 + 1 → F (n + 1) k - mu * F n k = G (k + 1) - G k := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [hFval, hFval, hmu]
      simp only [hG, if_true, if_neg (by norm_num : (0:ℕ) + 1 ≠ 0)]
      have e : (0 + 1 - 1 : ℕ) = 0 := by norm_num
      rw [e, hFval]
      simp only [Nat.sub_zero, Nat.add_sub_cancel]
      rw [qChoose_zero_right, qChoose_zero_right]
      have hCsplit : (c)_(n + 1) = (c)_n * (1 - c * q ^ n) := qPochhammer_succ_right c q n
      have hDsplit : (a * b * c * q ^ 0)_(n + 1) =
          (a * b * c * q ^ 0)_n * (1 - a * b * c * q ^ 0 * q ^ n) :=
        qPochhammer_succ_right (a * b * c * q ^ 0) q n
      rw [hCsplit, hDsplit]
      simp only [pow_zero, mul_one]
      ring
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hkpos)
      rcases Nat.lt_or_ge (j + 1) (n + 1) with hgen | hbdry
      · simp only [Nat.succ_eq_add_one]
        have hjn : j < n := by omega
        have hrel := qChoose_rel q n j hjn
        rw [hFval, hFval, hmu]
        simp only [hG, if_neg (by norm_num : j + 1 + 1 ≠ 0), if_neg (by norm_num : j + 1 ≠ 0)]
        have e5 : (j + 1 + 1 - 1 : ℕ) = j + 1 := by omega
        have e6 : (j + 1 - 1 : ℕ) = j := by omega
        rw [e5, e6, hFval, hFval]
        have hqc : qChoose q (n + 1) (j + 1) = qChoose q n j + q ^ (j + 1) * qChoose q n (j + 1) := rfl
        rw [hqc]
        have hi1 : (n + 1 - (j + 1) : ℕ) = (n - j - 1) + 1 := by omega
        have hi2 : (n - (j + 1) : ℕ) = n - j - 1 := by omega
        have hi3 : (n + 1 - (j + 1) : ℕ) = n - j := by omega
        have hCn1k : (c)_(n + 1 - (j+1)) = (c)_(n-j-1) * (1 - c * q ^ (n-j-1)) := by
          rw [hi1]; exact qPochhammer_succ_right c q (n-j-1)
        have hDn1k : (a * b * c * q ^ (j+1))_(n + 1 - (j+1)) =
            (a * b * c * q ^ (j+1))_(n-j-1) * (1 - a * b * c * q ^ (j+1) * q ^ (n-j-1)) := by
          rw [hi1]; exact qPochhammer_succ_right (a * b * c * q ^ (j+1)) q (n-j-1)
        rw [hi2] at *
        have hCnj : (c)_(n-j) = (c)_(n-j-1) * (1 - c * q ^ (n-j-1)) := by
          have : (n - j : ℕ) = (n-j-1) + 1 := by omega
          rw [this]; exact qPochhammer_succ_right c q (n-j-1)
        have hDnj : (a * b * c * q ^ j)_(n-j) =
            (1 - a * b * c * q ^ j) * (a * b * c * q ^ (j+1))_(n-j-1) := by
          have hidx : (n - j : ℕ) = (n-j-1) + 1 := by omega
          rw [hidx, qPochhammer_succ_left]
          congr 2
          rw [pow_succ]; ring
        have hAj : (a)_(j + 1) = (a)_j * (1 - a * q ^ j) := qPochhammer_succ_right a q j
        have hBj : (b)_(j + 1) = (b)_j * (1 - b * q ^ j) := qPochhammer_succ_right b q j
        rw [hCn1k, hDn1k, hCnj, hDnj, hAj, hBj]
        have hpow1 : q ^ (j + 1) = q * q ^ j := by rw [pow_succ]; ring
        have hpow2 : q ^ (n - j - 1 + 1) = q ^ (n - j - 1) * q := pow_succ q (n-j-1)
        have hpowN : q ^ n = q * q ^ j * q ^ (n - j - 1) := by
          have : q ^ (j + 1 + (n - j - 1)) = q ^ n := by congr 1; omega
          rw [← this, pow_add, pow_add, pow_one]; ring
        have hidxA : (n + 1 - (j + 1 + 1) : ℕ) = n - j - 1 := by omega
        have hidxB : (n + 1 - (j + 1) : ℕ) = n - j := by omega
        rw [hidxA, hidxB, hpow1, hpowN]
        have hcpow : c ^ (j + 1) = c * c ^ j := by rw [pow_succ]; ring
        rw [hcpow]
        set P := qChoose q n j with hP
        set Q := qChoose q n (j + 1) with hQ
        set Aj := (a)_j with hAj'
        set Bj := (b)_j with hBj'
        set cj := c ^ j with hcj
        set Cw := (c)_(n - j - 1) with hCw
        set Dw := (a * b * c * (q * q ^ j))_(n - j - 1) with hDw
        set tj := q ^ j with htj
        set sj := q ^ (n - j - 1) with hsj
        rw [hpow1] at hrel
        have hnj : q ^ (n - j) = q * sj := by
          rw [hsj]
          have : q ^ ((n - j - 1) + 1) = q ^ (n - j) := by congr 1; omega
          rw [← this, pow_succ]; ring
        rw [hnj] at hrel ⊢
        linear_combination
          (c * (1 - a * tj) * (1 - b * tj) * (1 - c * sj) * Aj * Bj * cj * Cw * Dw) * hrel
      · have hjn : j = n := by omega
        subst hjn
        simp only [Nat.succ_eq_add_one]
        rw [hFval, hFval]
        rw [qChoose_eq_zero_of_lt q j (j + 1) (by omega)]
        simp only [hG, if_neg (by norm_num : j + 1 + 1 ≠ 0), if_neg (by norm_num : j + 1 ≠ 0)]
        have e1 : (j + 1 + 1 - 1 : ℕ) = j + 1 := by omega
        have e2 : (j + 1 - 1 : ℕ) = j := by omega
        rw [e1, e2, hFval, hFval]
        rw [qChoose_eq_zero_of_lt q j (j + 1) (by omega)]
        show qChoose q (j + 1) (j + 1) * (a)_(j+1) * (b)_(j+1) * c ^ (j+1) * (c)_(j + 1 - (j+1)) *
              (a * b * c * q ^ (j+1))_(j + 1 - (j+1)) -
            (1 - a * c * q ^ j) * (1 - b * c * q ^ j) *
              (0 * (a)_(j+1) * (b)_(j+1) * c ^ (j+1) * (c)_(j - (j+1)) *
                (a * b * c * q ^ (j+1))_(j - (j+1))) = _
        have e3 : (j + 1 - (j + 1) : ℕ) = 0 := by omega
        have e4 : (j - j : ℕ) = 0 := by omega
        rw [e3]
        rw [qChoose_self]
        simp only [e4, qChoose_self]
        have hA : (a)_(j + 1) = (a)_j * (1 - a * q ^ j) := qPochhammer_succ_right a q j
        have hB : (b)_(j + 1) = (b)_j * (1 - b * q ^ j) := qPochhammer_succ_right b q j
        have hd0 : ∀ x : R, qPochhammer x q 0 = 1 := by intro x; simp [qPochhammer]
        rw [hA, hB]
        simp only [hd0, pow_succ, mul_one]
        ring
  have hFn1 : (∑ k ∈ range (n + 1 + 1),
      qChoose q (n + 1) k * (a)_k * (b)_k * c ^ k * (c)_(n + 1 - k) *
        (a * b * c * q ^ k)_(n + 1 - k)) = ∑ k ∈ range (n + 1 + 1), F (n + 1) k := by
    apply Finset.sum_congr rfl; intro k _; simp only [hF]
  have hFn : (∑ k ∈ range (n + 1),
      qChoose q n k * (a)_k * (b)_k * c ^ k * (c)_(n - k) * (a * b * c * q ^ k)_(n - k)) =
      ∑ k ∈ range (n + 1), F n k := by
    apply Finset.sum_congr rfl; intro k _; simp only [hF]
  rw [hFn1, hFn]
  have hzero : F n (n + 1) = 0 := by
    simp only [hF]
    rw [qChoose_eq_zero_of_lt q n (n + 1) (by omega)]; ring
  have hext : (∑ k ∈ range (n + 1), F n k) = ∑ k ∈ range (n + 1 + 1), F n k := by
    rw [Finset.sum_range_succ (f := F n) (n := n + 1), hzero, add_zero]
  rw [hext, Finset.mul_sum]
  have htel : (∑ k ∈ range (n + 1 + 1), (F (n + 1) k - mu * F n k)) = 0 := by
    rw [Finset.sum_congr rfl (fun k hk => key k (Finset.mem_range.mp hk))]
    rw [Finset.sum_range_sub G]
    have hGtop : G (n + 1 + 1) = 0 := by
      simp only [hG]
      rw [if_neg (by omega)]
      have : n + 1 + 1 - 1 = n + 1 := by omega
      rw [this, hzero]; ring
    have hG0 : G 0 = 0 := by simp only [hG, if_pos rfl]
    rw [hGtop, hG0, sub_zero]
  rw [Finset.sum_sub_distrib] at htel
  exact sub_eq_zero.mp htel

theorem sum_qChoose_mul_qPochhammer_eq_qPochhammer_mul
    {R : Type*} [CommRing R] (a b c q : R) (n : ℕ) :
    ∑ k ∈ range (n + 1),
      qChoose q n k * (a)_k * (b)_k * c ^ k * (c)_(n - k) * (a * b * c * q ^ k)_(n - k) =
    (a * c)_n * (b * c)_n := by
  induction n with
  | zero =>
      simp [qChoose, qPochhammer]
  | succ n ih =>
      rw [sum_recurrence]; rw [ih]; rw [qPochhammer_succ_right, qPochhammer_succ_right]; ring
