import Mathlib
import RogersRamanujan

open Filter Topology in
theorem isTopologicallyNilpotent_of_tendsto
    {R : Type*} [CommRing R] [TopologicalSpace R] [StrongNonarchimedeanRing R]
    {f : ℕ → R} {l : R} (hf : Tendsto f atTop (𝓝 l)) (hnf : ∀ n, IsTopologicallyNilpotent (f n)) :
    IsTopologicallyNilpotent l := by
  sorry
