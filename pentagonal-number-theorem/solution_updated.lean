import Mathlib
import RogersRamanujan
set_option backward.isDefEq.respectTransparency false

open PowerSeries.WithPiTopology
open scoped DiscreteUniformity

def generalizedPentagonal (k : ℤ) : ℕ := (k * (3 * k - 1) / 2).toNat

set_option maxHeartbeats 800000 in
lemma product_side_eq :
    qPochhammerInf (PowerSeries.X ^ 3 : PowerSeries ℤ) (PowerSeries.X ^ 3)
    * qPochhammerInf (PowerSeries.X : PowerSeries ℤ) (PowerSeries.X ^ 3)
    * qPochhammerInf (PowerSeries.X ^ 2 : PowerSeries ℤ) (PowerSeries.X ^ 3)
    = qPochhammerInf (PowerSeries.X : PowerSeries ℤ) PowerSeries.X := by
  have hnil : IsTopologicallyNilpotent (PowerSeries.X : PowerSeries ℤ) := PowerSeries.HasEval.X
  have h := qPochhammerInf_eq_prod_range (m := 3) (by omega : (3 : ℕ) ≠ 0) hnil (a := PowerSeries.X)
  rw [h]
  simp [Finset.prod_range_succ]
  ring

private lemma ofNat_arith (n : ℕ) : n + 1 + 3 * ((n + 1) * n / 2) = (n + 1) * (3 * n + 2) / 2 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    rw [show (k + k + 1) * (k + k) = 2 * ((k + k + 1) * k) from by ring,
       Nat.mul_div_cancel_left _ (by omega : 0 < 2),
       show (k + k + 1) * (3 * (k + k) + 2) = 2 * ((k + k + 1) * (3 * k + 1)) from by ring,
       Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    ring
  · subst hk
    rw [show (2 * k + 1 + 1) * (2 * k + 1) = 2 * ((k + 1) * (2 * k + 1)) from by ring,
       Nat.mul_div_cancel_left _ (by omega : 0 < 2),
       show (2 * k + 1 + 1) * (3 * (2 * k + 1) + 2) = 2 * ((k + 1) * (6 * k + 5)) from by ring,
       Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    ring

private lemma negSucc_arith (m : ℕ) : 2 * (m + 1) + 3 * ((m + 1) * m / 2) = (m + 1) * (3 * m + 4) / 2 := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    rw [show (k + k + 1) * (k + k) = 2 * ((k + k + 1) * k) from by ring,
       Nat.mul_div_cancel_left _ (by omega : 0 < 2),
       show (k + k + 1) * (3 * (k + k) + 4) = 2 * ((k + k + 1) * (3 * k + 2)) from by ring,
       Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    ring
  · subst hk
    rw [show (2 * k + 1 + 1) * (2 * k + 1) = 2 * ((k + 1) * (2 * k + 1)) from by ring,
       Nat.mul_div_cancel_left _ (by omega : 0 < 2),
       show (2 * k + 1 + 1) * (3 * (2 * k + 1) + 4) = 2 * ((k + 1) * (6 * k + 7)) from by ring,
       Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    ring

private lemma gp_ofNat (n : ℕ) :
    generalizedPentagonal (Int.ofNat n) = n * (3 * n - 1) / 2 := by
  unfold generalizedPentagonal
  rcases n with _ | n
  · simp
  · have key : (Int.ofNat (n+1)) * (3 * Int.ofNat (n+1) - 1) = ↑((n+1) * (3*n+2)) := by
      simp only [Int.ofNat_eq_natCast]; push_cast; ring
    rw [key, show (2 : ℤ) = ↑(2 : ℕ) from rfl, ← Int.natCast_div, Int.toNat_natCast]
    congr 1

private lemma gp_negSucc (m : ℕ) :
    generalizedPentagonal (Int.negSucc m) = (m+1) * (3*m+4) / 2 := by
  unfold generalizedPentagonal
  simp only [Int.negSucc_eq]
  have key : (-(↑m + 1) : ℤ) * (3 * (-(↑m + 1)) - 1) = ↑((m+1) * (3*m+4)) := by push_cast; ring
  rw [key, show (2 : ℤ) = ↑(2 : ℕ) from rfl, ← Int.natCast_div, Int.toNat_natCast]

lemma sum_term_eq (k : ℤ) :
    abPow (-PowerSeries.X : PowerSeries ℤ) (-PowerSeries.X ^ 2) k
      * (PowerSeries.X ^ 3) ^ (k.natAbs.choose 2)
    = (-1 : PowerSeries ℤ) ^ k.natAbs * PowerSeries.X ^ generalizedPentagonal k := by
  cases k with
  | ofNat n =>
    simp only [abPow, Int.natAbs_ofNat']
    rw [show (-PowerSeries.X : PowerSeries ℤ) = (-1) * PowerSeries.X from by ring]
    rw [mul_pow, mul_assoc, ← pow_mul, ← pow_add]
    congr 2
    rw [Nat.choose_two_right, gp_ofNat]
    rcases n with _ | n
    · simp
    · exact ofNat_arith n
  | negSucc m =>
    simp only [abPow, Int.natAbs_negSucc]
    rw [show (-PowerSeries.X ^ 2 : PowerSeries ℤ) = (-1) * PowerSeries.X ^ 2 from by ring]
    rw [mul_pow, mul_assoc, ← pow_mul, ← pow_mul, ← pow_add]
    congr 2
    rw [Nat.choose_two_right, gp_negSucc]
    exact negSucc_arith m

theorem pentagonal_number_theorem' :
    HasSum
      (fun k : ℤ =>
        (-1 : PowerSeries ℤ) ^ k.natAbs * PowerSeries.X ^ generalizedPentagonal k)
      (qPochhammerInf (PowerSeries.X : PowerSeries ℤ) PowerSeries.X) := by
  have hnil : IsTopologicallyNilpotent (PowerSeries.X ^ 3 : PowerSeries ℤ) := by
    apply IsTopologicallyNilpotent.pow
    · exact PowerSeries.HasEval.X
    · omega
  have hab : (-PowerSeries.X : PowerSeries ℤ) * (-PowerSeries.X ^ 2) = PowerSeries.X ^ 3 := by
    ring
  have hjtp := jacobi_triple_product_hasSum hnil hab
  have hprod_simp : qPochhammerInf (PowerSeries.X ^ 3 : PowerSeries ℤ) (PowerSeries.X ^ 3) *
      qPochhammerInf (- -PowerSeries.X : PowerSeries ℤ) (PowerSeries.X ^ 3) *
      qPochhammerInf (- -(PowerSeries.X : PowerSeries ℤ) ^ 2) (PowerSeries.X ^ 3) =
    qPochhammerInf (PowerSeries.X ^ 3 : PowerSeries ℤ) (PowerSeries.X ^ 3) *
      qPochhammerInf (PowerSeries.X : PowerSeries ℤ) (PowerSeries.X ^ 3) *
      qPochhammerInf (PowerSeries.X ^ 2 : PowerSeries ℤ) (PowerSeries.X ^ 3) := by
    simp [neg_neg]
  rw [hprod_simp, product_side_eq] at hjtp
  exact hjtp.congr_fun (fun k => (sum_term_eq k).symm)
