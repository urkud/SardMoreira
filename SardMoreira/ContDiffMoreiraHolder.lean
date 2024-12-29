import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Holder
import SardMoreira.ContDiff

open scoped unitInterval Topology NNReal
open Asymptotics Filter Set

namespace Asymptotics

/-- If `a ≤ b`, then `x^b = O(x^a)` as `x → 0`, `x ≥ 0`, unless `b = 0` and `a ≠ 0`. -/
theorem IsBigO.rpow_rpow_nhdsGE_zero_of_le {a b : ℝ} (h : a ≤ b) (himp : b = 0 → a = 0) :
    (· ^ b : ℝ → ℝ) =O[𝓝[≥] 0] (· ^ a) :=
  .of_bound' <| mem_of_superset (Icc_mem_nhdsGE one_pos) fun x hx ↦ by
    simpa [Real.abs_rpow_of_nonneg hx.1, abs_of_nonneg hx.1]
     using Real.rpow_le_rpow_of_exponent_ge_of_imp hx.1 hx.2 h fun _ ↦ himp

theorem IsBigO.id_rpow_of_le_one {a : ℝ} (ha : a ≤ 1) :
    (id : ℝ → ℝ) =O[𝓝[≥] 0] (· ^ a) := by
  simpa using rpow_rpow_nhdsGE_zero_of_le ha (by simp)

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

variable (𝕜) in
structure ContDiffMoreiraHolderAt (k : ℕ) (α : I) (f : E → F) (a : E) : Prop where
  contDiffAt : ContDiffAt 𝕜 k f a
  isBigO : (iteratedFDeriv 𝕜 k f · - iteratedFDeriv 𝕜 k f a) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ))

theorem ContDiffAt.contDiffMoreiraHolderAt {n : WithTop ℕ∞} {k : ℕ} {f : E → F} {a : E}
    (h : ContDiffAt 𝕜 n f a) (hk : k < n) (α : I) : ContDiffMoreiraHolderAt 𝕜 k α f a where
  contDiffAt := h.of_le hk.le
  isBigO := calc
    (iteratedFDeriv 𝕜 k f · - iteratedFDeriv 𝕜 k f a) =O[𝓝 a] (· - a) :=
      (h.differentiableAt_iteratedFDeriv hk).isBigO_sub
    _ =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) :=
      .of_norm_left <| .comp_tendsto (.id_rpow_of_le_one α.2.2) <| tendsto_norm_sub_self_nhdsLE a

namespace ContDiffMoreiraHolderAt

@[simp]
theorem zero_exponent_iff {k : ℕ} {f : E → F} {a : E} :
    ContDiffMoreiraHolderAt 𝕜 k 0 f a ↔ ContDiffAt 𝕜 k f a := by
  refine ⟨contDiffAt, fun h ↦ ⟨h, ?_⟩⟩
  simpa using ((h.continuousAt_iteratedFDeriv le_rfl).sub_const _).norm.isBoundedUnder_le

theorem of_exponent_le {k : ℕ} {f : E → F} {a : E} {α β : I}
    (hf : ContDiffMoreiraHolderAt 𝕜 k α f a) (hle : β ≤ α) : ContDiffMoreiraHolderAt 𝕜 k β f a where
  contDiffAt := hf.contDiffAt
  isBigO := hf.isBigO.trans <| by
    refine .comp_tendsto (.rpow_rpow_nhdsGE_zero_of_le hle fun hα ↦ ?_) ?_
    · exact le_antisymm (le_trans (mod_cast hle) hα.le) β.2.1
    · exact tendsto_norm_sub_self_nhdsLE a

theorem of_lt {k l : ℕ} {f : E → F} {a : E} {α β : I} (hf : ContDiffMoreiraHolderAt 𝕜 k α f a)
    (hlt : l < k) : ContDiffMoreiraHolderAt 𝕜 l β f a :=
  hf.contDiffAt.contDiffMoreiraHolderAt (mod_cast hlt) _

theorem of_toLex_le {k l : ℕ} {f : E → F} {a : E} {α β : I} (hf : ContDiffMoreiraHolderAt 𝕜 k α f a)
    (hle : toLex (l, β) ≤ toLex (k, α)) : ContDiffMoreiraHolderAt 𝕜 l β f a :=
  ((Prod.Lex.le_iff _ _).mp hle).elim hf.of_lt <| by rintro ⟨rfl, hle⟩; exact hf.of_exponent_le hle

theorem of_contDiffOn_holderWith {f : E → F} {s : Set E} {k : ℕ} {α : I} {a : E} {C : ℝ≥0}
    (hf : ContDiffOn 𝕜 k f s) (hs : s ∈ 𝓝 a)
    (hd : HolderOnWith C ⟨α, α.2.1⟩ (iteratedFDeriv 𝕜 k f) s) :
    ContDiffMoreiraHolderAt 𝕜 k α f a where
  contDiffAt := hf.contDiffAt hs
  isBigO := .of_bound C <| mem_of_superset hs fun x hx ↦ by
    simpa [Real.abs_rpow_of_nonneg, ← dist_eq_norm, dist_nonneg]
      using hd.dist_le hx (mem_of_mem_nhds hs)

end ContDiffMoreiraHolderAt

structure ContDiffMoreiraHolderOn
