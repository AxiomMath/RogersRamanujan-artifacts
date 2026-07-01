import Mathlib
import RogersRamanujan
set_option backward.isDefEq.respectTransparency false

open PowerSeries.WithPiTopology
open scoped DiscreteUniformity

def generalizedPentagonal (k : ℤ) : ℕ := (k * (3 * k - 1) / 2).toNat

theorem pentagonal_number_theorem :
    HasSum
      (fun k : ℤ =>
        (-1 : PowerSeries ℤ) ^ k.natAbs * PowerSeries.X ^ generalizedPentagonal k)
      (qPochhammerInf (PowerSeries.X : PowerSeries ℤ) PowerSeries.X) := by
  sorry
