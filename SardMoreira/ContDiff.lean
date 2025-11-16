import Mathlib.Analysis.Calculus.ContDiff.Basic

open scoped unitInterval Topology NNReal
open Asymptotics Filter Set

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f : E → F} {s : Set E} {n : WithTop ℕ∞} {k : ℕ} {a : E}

protected alias UniqueDiffOn.univ := uniqueDiffOn_univ

theorem ContDiffOn.continuousAt_iteratedFDerivWithin (hf : ContDiffOn 𝕜 n f s)
    (hs : UniqueDiffOn 𝕜 s) (ha : s ∈ 𝓝 a) (hk : k ≤ n) :
    ContinuousAt (iteratedFDerivWithin 𝕜 k f s) a :=
  (hf.continuousOn_iteratedFDerivWithin hk hs).continuousAt ha

theorem ContDiffWithinAt.continuousWithinAt_iteratedFDerivWithin (hf : ContDiffWithinAt 𝕜 n f s a)
    (hs : UniqueDiffOn 𝕜 s) (ha : a ∈ s) (hk : k ≤ n) :
    ContinuousWithinAt (iteratedFDerivWithin 𝕜 k f s) s a :=
  (hf.iteratedFDerivWithin_right hs (by rwa [zero_add]) ha).continuousWithinAt

theorem ContDiffAt.continuousAt_iteratedFDeriv (hf : ContDiffAt 𝕜 n f a) (hk : k ≤ n) :
    ContinuousAt (iteratedFDeriv 𝕜 k f) a := by
  simp only [← continuousWithinAt_univ, ← iteratedFDerivWithin_univ]
  exact hf.contDiffWithinAt.continuousWithinAt_iteratedFDerivWithin uniqueDiffOn_univ trivial hk

theorem ContDiffAt.differentiableAt_iteratedFDeriv (hf : ContDiffAt 𝕜 n f a) (hk : k < n) :
    DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 k f) a := by
  simp only [← differentiableWithinAt_univ, ← iteratedFDerivWithin_univ]
  exact hf.differentiableWithinAt_iteratedFDerivWithin hk (by simp [uniqueDiffOn_univ])

/-- Generalizes `ContinuousLinearMap.iteratedFderivWithin_comp_left`
by weakening a `ContDiffOn` assumption to `ContDiffWithinAt`.  -/
theorem ContinuousLinearMap.iteratedFDerivWithin_comp_left' (g : F →L[𝕜] G)
    (hf : ContDiffWithinAt 𝕜 n f s a) (hs : UniqueDiffOn 𝕜 s) (ha : a ∈ s) {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s a =
      g.compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s a) := by
  rcases hf.contDiffOn' hi (by simp) with ⟨U, hU, haU, hfU⟩
  rw [← iteratedFDerivWithin_inter_open hU haU, ← iteratedFDerivWithin_inter_open (f := f) hU haU]
  rw [insert_eq_of_mem ha] at hfU
  exact .symm <| (hfU.ftaylorSeriesWithin (hs.inter hU)).continuousLinearMap_comp g
    |>.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter hU) ⟨ha, haU⟩

/-- Generalizes `ContinuousLinearMap.iteratedFderiv_comp_left`
by weakening a `ContDiff` assumption to `ContDiffAt`.  -/
theorem ContinuousLinearMap.iteratedFDeriv_comp_left' (g : F →L[𝕜] G) (hf : ContDiffAt 𝕜 n f a)
    {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (g ∘ f) a = g.compContinuousMultilinearMap (iteratedFDeriv 𝕜 i f a) := by
  simp only [← iteratedFDerivWithin_univ]
  exact g.iteratedFDerivWithin_comp_left' hf.contDiffWithinAt .univ (mem_univ _) hi
