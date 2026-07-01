import Mathlib
import RogersRamanujan
set_option backward.isDefEq.respectTransparency false

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

-- Main Statement(s)

/-- **Jacobi's identity.** In the ring of formal power series `ℤ⟦q⟧`,
`∏_{n=1}^{∞} (1 - q^n)^3 = ∑_{k=0}^{∞} (-1)^k (2k+1) q^{(k^2+k)/2}`. -/
theorem jacobi_cube_euler : eulerCube = jacobiSeries := by
  sorry

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
  sorry

/-- Coefficient form, non-triangular case: the coefficient of `q^m` in
`∏_{n=1}^{∞} (1 - q^n)^3` is `0` whenever `m` is not a triangular number. -/
theorem jacobi_coeff_nontriangular (m : ℕ) (h : ∀ k : ℕ, (k ^ 2 + k) / 2 ≠ m) :
    (coeff (R := ℤ) m) eulerCube = 0 := by
  sorry
