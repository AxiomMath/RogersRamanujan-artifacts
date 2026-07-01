import Mathlib

private abbrev K : Type := ℚ_[2]

private lemma inf_comap_eval_subset_pi (I : Finset ℕ) (W : ℕ → OpenAddSubgroup K) :
    ↑(I.inf (fun i => OpenAddSubgroup.comap
      ((Pi.evalRingHom (fun _ : ℕ => K) i).toAddMonoidHom)
      (continuous_apply i) (W i))) ⊆
    (↑I : Set ℕ).pi (fun i => (↑(W i) : Set K)) := by
  intro x hx i hi
  simpa [Pi.evalRingHom_apply] using
    (OpenAddSubgroup.mem_comap.mp (SetLike.le_def.mp (Finset.inf_le hi) hx))

/-! ## ℕ → K is nonarchimedean -/

private lemma piNat_nonarchimedean : NonarchimedeanRing (ℕ → K) :=
  NonarchimedeanRing.mk fun U hU => by
    letI : NonarchimedeanRing K :=
      NonarchimedeanRing.mk fun V hV => NonarchimedeanAddGroup.is_nonarchimedean V hV
    rw [nhds_pi] at hU
    obtain ⟨I, t, ht, hsub⟩ := Filter.mem_pi'.mp hU
    choose W hW using fun i => NonarchimedeanRing.is_nonarchimedean (t i) (ht i)
    exact ⟨I.inf (fun i => OpenAddSubgroup.comap
        ((Pi.evalRingHom (fun _ : ℕ => K) i).toAddMonoidHom)
        (continuous_apply i) (W i)),
      (inf_comap_eval_subset_pi I W).trans ((Set.pi_mono fun i _ => hW i).trans hsub)⟩

/-! ## Topological nilpotence facts -/

private lemma const2_isTopNil : IsTopologicallyNilpotent (fun _ : ℕ => (2 : K)) := by
  rw [IsTopologicallyNilpotent, tendsto_pi_nhds]
  exact fun _ => by
    simpa only [Pi.pow_apply, Pi.zero_apply] using
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one

private lemma one_not_isTopNil : ¬ IsTopologicallyNilpotent (1 : K) := by
  intro h
  have : Filter.Tendsto (fun _ : ℕ => (1 : K)) Filter.atTop (nhds 0) := by
    rwa [show (fun _ : ℕ => (1 : K)) = (fun n => (1 : K) ^ n) from
      funext fun n => (one_pow n).symm]
  exact one_ne_zero.symm (tendsto_nhds_unique this tendsto_const_nhds)

private lemma eval_of_isTopNil (f : ℕ → K) (j : ℕ) (hf : IsTopologicallyNilpotent f) :
    IsTopologicallyNilpotent (f j) := by
  have : IsTopologicallyNilpotent (Pi.evalRingHom (fun _ : ℕ => K) j f) :=
    hf.map (continuous_apply j)
  simpa using this

/-! ## Main counterexample construction -/

private lemma exists_in_nhds_not_in_stability (U : Set (ℕ → K)) (hU : U ∈ nhds 0) :
    ∃ x ∈ U, ∃ q : ℕ → K,
      IsTopologicallyNilpotent q ∧ ¬ IsTopologicallyNilpotent (x * q) := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hsub⟩ := hU
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset hI.toFinset
  refine ⟨Function.update 0 j ((2 : K)⁻¹), ?_, fun _ => (2 : K), const2_isTopNil, ?_⟩
  · apply hsub
    intro i hi
    simp only [Function.update_of_ne (show i ≠ j from fun h => hj (h ▸ hI.mem_toFinset.mpr hi)),
      Pi.zero_apply]
    exact mem_of_mem_nhds (ht i)
  · intro h
    apply one_not_isTopNil
    have h1 := eval_of_isTopNil _ j h
    simp only [Pi.mul_apply, Function.update_self] at h1
    rwa [inv_mul_cancel₀ (two_ne_zero' K)] at h1

theorem nil_stable_not :
    ¬ ∀ (R : Type) [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R],
    {x : R | ∀ q, IsTopologicallyNilpotent q → IsTopologicallyNilpotent (x * q)} ∈ nhds 0 := by
  intro h
  letI := piNat_nonarchimedean
  obtain ⟨x, hxS, q, hq, hxq⟩ := exists_in_nhds_not_in_stability _ (h (ℕ → K))
  exact hxq (hxS q hq)
