import Mathlib

theorem nil_stable_not :
    ¬ ∀ (R : Type) [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R],
    {x : R | ∀ q, IsTopologicallyNilpotent q → IsTopologicallyNilpotent (x * q)} ∈ nhds 0 := by
  sorry
