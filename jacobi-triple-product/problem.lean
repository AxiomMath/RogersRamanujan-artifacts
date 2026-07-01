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

theorem jacobi_triple_product : lhs = rhs := by
  sorry
