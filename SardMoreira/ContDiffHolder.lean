import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Holder

open scoped unitInterval Topology NNReal
open Asymptotics Filter Set

namespace Asymptotics

/-- If `a ≤ b`, then `x^b = O(x^a)` as `x → 0`, `x ≥ 0`, unless `b = 0` and `a ≠ 0`. -/
theorem IsBigO.rpow_rpow_nhdsWithin_Ici_zero_of_le {a b : ℝ} (h : a ≤ b) (himp : b = 0 → a = 0) :
    (· ^ b : ℝ → ℝ) =O[𝓝[≥] 0] (· ^ a) :=
  .of_bound' <| mem_of_superset (Icc_mem_nhdsGE one_pos) fun x hx ↦ by
    simpa [Real.abs_rpow_of_nonneg hx.1, abs_of_nonneg hx.1]
     using Real.rpow_le_rpow_of_exponent_ge_of_imp hx.1 hx.2 h fun _ ↦ himp

theorem IsBigO.id_rpow_of_le_one {a : ℝ} (ha : a ≤ 1) :
    (id : ℝ → ℝ) =O[𝓝[≥] 0] (· ^ a) := by
  simpa using rpow_rpow_nhdsWithin_Ici_zero_of_le ha (by simp)

end Asymptotics

@[to_additive]
theorem tendsto_norm_div_self_nhdsLE {E : Type*} [SeminormedGroup E] (a : E) :
    Tendsto (‖· / a‖) (𝓝 a) (𝓝[≥] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_norm_div_self a, by simp⟩

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
    _ =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) :=
      .of_norm_left <| .comp_tendsto (.id_rpow_of_le_one α.2.2) <| tendsto_norm_sub_self_nhdsLE a

namespace ContDiffHolderAt

@[simp]
theorem zero_exponent_iff {k : ℕ} {f : E → F} {a : E} :
    ContDiffHolderAt 𝕜 k 0 f a ↔ ContDiffAt 𝕜 k f a := by
  refine ⟨contDiffAt, fun h ↦ ⟨h, ?_⟩⟩
  simpa using ((h.continuousAt_iteratedFDeriv le_rfl).sub_const _).norm.isBoundedUnder_le

theorem of_exponent_le {k : ℕ} {f : E → F} {a : E} {α β : I} (hf : ContDiffHolderAt 𝕜 k α f a)
    (hle : β ≤ α) : ContDiffHolderAt 𝕜 k β f a where
  contDiffAt := hf.contDiffAt
  isBigO := hf.isBigO.trans <| by
    refine .comp_tendsto (.rpow_rpow_nhdsWithin_Ici_zero_of_le hle fun hα ↦ ?_) ?_
    · exact le_antisymm (le_trans (mod_cast hle) hα.le) β.2.1
    · exact tendsto_norm_sub_self_nhdsLE a

theorem of_lt {k l : ℕ} {f : E → F} {a : E} {α β : I} (hf : ContDiffHolderAt 𝕜 k α f a)
    (hlt : l < k) : ContDiffHolderAt 𝕜 l β f a :=
  hf.contDiffAt.contDiffHolderAt (mod_cast hlt) _

theorem of_toLex_le {k l : ℕ} {f : E → F} {a : E} {α β : I} (hf : ContDiffHolderAt 𝕜 k α f a)
    (hle : toLex (l, β) ≤ toLex (k, α)) : ContDiffHolderAt 𝕜 l β f a :=
  ((Prod.Lex.le_iff _ _).mp hle).elim hf.of_lt <| by rintro ⟨rfl, hle⟩; exact hf.of_exponent_le hle

theorem of_contDiffOn_holderWith {f : E → F} {s : Set E} {k : ℕ} {α : I} {a : E} {C : ℝ≥0}
    (hf : ContDiffOn 𝕜 k f s) (hs : s ∈ 𝓝 a)
    (hd : HolderOnWith C ⟨α, α.2.1⟩ (iteratedFDeriv 𝕜 k f) s) :
    ContDiffHolderAt 𝕜 k α f a where
  contDiffAt := hf.contDiffAt hs
  isBigO := .of_bound C <| mem_of_superset hs fun x hx ↦ by
    simpa [Real.abs_rpow_of_nonneg, ← dist_eq_norm, dist_nonneg]
      using hd.dist_le hx (mem_of_mem_nhds hs)

end ContDiffHolderAt
