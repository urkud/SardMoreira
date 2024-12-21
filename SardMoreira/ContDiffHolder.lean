import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped unitInterval Topology
open Asymptotics Filter Set

theorem Asymptotics.IsBigO.id_rpow_of_le_one {a : ℝ} (ha : a ≤ 1) :
    (id : ℝ → ℝ) =O[𝓝[≥] 0] (· ^ a) :=
  .of_bound' <| mem_of_superset (Icc_mem_nhdsWithin_Ici' one_pos) fun x hx ↦ by
    simpa [Real.abs_rpow_of_nonneg hx.1, abs_of_nonneg hx.1]
      using Real.self_le_rpow_of_le_one hx.1 hx.2 ha

section NormedField

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem ContDiffOn.continuousAt_iteratedFDerivWithin {f : E → F} {s : Set E} {n : WithTop ℕ∞}
    {k : ℕ} {a : E} (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (ha : s ∈ 𝓝 a) (hk : k ≤ n) :
    ContinuousAt (iteratedFDerivWithin 𝕜 k f s) a :=
  (hf.continuousOn_iteratedFDerivWithin hk hs).continuousAt ha

theorem ContDiffWithinAt.continuousWithinAt_iteratedFDerivWithin
    {f : E → F} {s : Set E} {n : WithTop ℕ∞} {k : ℕ} {a : E} (hf : ContDiffWithinAt 𝕜 n f s a)
    (hs : UniqueDiffOn 𝕜 s) (ha : a ∈ s) (hk : k ≤ n) :
    ContinuousWithinAt (iteratedFDerivWithin 𝕜 k f s) s a :=
  (hf.iteratedFderivWithin_right hs (by rwa [zero_add]) ha).continuousWithinAt

theorem ContDiffAt.continuousAt_iteratedFDeriv
    {f : E → F} {n : WithTop ℕ∞} {k : ℕ} {a : E} (hf : ContDiffAt 𝕜 n f a) (hk : k ≤ n) :
    ContinuousAt (iteratedFDeriv 𝕜 k f) a := by
  simp only [← continuousWithinAt_univ, ← iteratedFDerivWithin_univ]
  exact hf.contDiffWithinAt.continuousWithinAt_iteratedFDerivWithin uniqueDiffOn_univ trivial hk

theorem ContDiffAt.differentiableAt_iteratedFDeriv
    {f : E → F} {a : E} {n : WithTop ℕ∞} {m : ℕ} (hf : ContDiffAt 𝕜 n f a) (hm : m < n) :
    DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 m f) a := by
  simp only [← differentiableWithinAt_univ, ← iteratedFDerivWithin_univ]
  exact hf.differentiableWithinAt_iteratedFDerivWithin hm (by simp [uniqueDiffOn_univ])

variable (𝕜) in
structure ContDiffHolderAt (k : ℕ) (α : I) (f : E → F) (a : E) : Prop where
  contDiffAt : ContDiffAt 𝕜 k f a
  isBigO : (iteratedFDeriv 𝕜 k f · - iteratedFDeriv 𝕜 k f a) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ))

theorem ContDiffAt.contDiffHolderAt {n : WithTop ℕ∞} {k : ℕ} {f : E → F} {a : E}
    (h : ContDiffAt 𝕜 n f a) (hk : k < n) (α : I) : ContDiffHolderAt 𝕜 k α f a where
  contDiffAt := h.of_le hk.le
  isBigO := calc
    (iteratedFDeriv 𝕜 k f · - iteratedFDeriv 𝕜 k f a) =O[𝓝 a] (· - a) :=
      (h.differentiableAt_iteratedFDeriv hk).isBigO_sub
    _ =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) := by
      refine .of_norm_left <| .comp_tendsto (.id_rpow_of_le_one α.2.2) ?_
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, by simp⟩
      exact Continuous.tendsto' (by fun_prop) _ _ (by simp)

namespace ContDiffHolderAt

@[simp]
theorem zero_exponent_iff {k : ℕ} {f : E → F} {a : E} :
    ContDiffHolderAt 𝕜 k 0 f a ↔ ContDiffAt 𝕜 k f a := by
  refine ⟨contDiffAt, fun h ↦ ⟨h, ?_⟩⟩
  simpa using ((h.continuousAt_iteratedFDeriv le_rfl).sub_const _).norm.isBoundedUnder_le

end ContDiffHolderAt
