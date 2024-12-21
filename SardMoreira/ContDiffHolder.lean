import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped unitInterval Topology
open Asymptotics Filter Set

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
    (hs : UniqueDiffOn 𝕜 (insert a s)) (hk : k ≤ n) :
    ContinuousWithinAt (iteratedFDerivWithin 𝕜 k f s) s a := by
  rcases hf.contDiffOn' hk (by simp) with ⟨U, hUo, haU, hfU⟩
  have H := hfU.continuousOn_iteratedFDerivWithin le_rfl (hs.inter hUo) a ⟨mem_insert _ _, haU⟩
  rw [← continuousWithinAt_insert_self]
  have {b t} (hb : b ∈ U) : (t ∩ U : Set E) =ᶠ[𝓝 b] t :=
    inter_eventuallyEq_left.2 <| mem_nhds_iff.mpr ⟨U, fun _ h _ ↦ h, hUo, hb⟩
  refine (H.congr_of_mem (fun y hy ↦ ?_) (by simpa)).congr_set (this haU)
  rw [← iteratedFDerivWithin_insert, iteratedFDerivWithin_congr_set (this hy.2)]

theorem ContDiffAt.continuousAt_iteratedFDeriv
    {f : E → F} {n : WithTop ℕ∞} {k : ℕ} {a : E} (hf : ContDiffAt 𝕜 n f a) (hk : k ≤ n) :
    ContinuousAt (iteratedFDeriv 𝕜 k f) a := by
  simp only [← continuousWithinAt_univ, ← iteratedFDerivWithin_univ]
  exact hf.contDiffWithinAt.continuousWithinAt_iteratedFDerivWithin (by simp [uniqueDiffOn_univ]) hk

variable (𝕜) in
structure ContDiffHolderAt (k : ℕ) (α : I) (f : E → F) (a : E) : Prop where
  contDiffAt : ContDiffAt 𝕜 k f a
  isBigO : (iteratedFDeriv 𝕜 k f · - iteratedFDeriv 𝕜 k f a) =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ)

namespace ContDiffHolderAt

@[simp]
theorem zero_exponent_iff {k : ℕ} {f : E → F} {a : E} :
    ContDiffHolderAt 𝕜 k 0 f a ↔ ContDiffAt 𝕜 k f a := by
  refine ⟨contDiffAt, fun h ↦ ⟨h, ?_⟩⟩
  simpa using ((h.continuousAt_iteratedFDeriv le_rfl).sub_const _).norm.isBoundedUnder_le

end ContDiffHolderAt
