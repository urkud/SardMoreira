import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Holder
import SardMoreira.ContDiff

open scoped unitInterval Topology NNReal
open Asymptotics Filter Set

theorem monotone_fst_ofLex {α β : Type*} [Preorder α] [Preorder β] :
    Monotone fun x : α ×ₗ β ↦ (ofLex x).1 := fun _ _ h ↦
  ((Prod.Lex.le_iff _ _).mp h).elim le_of_lt <| le_of_eq ∘ And.left

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
theorem tendsto_norm_div_self_nhdsGE {E : Type*} [SeminormedGroup E] (a : E) :
    Tendsto (‖· / a‖) (𝓝 a) (𝓝[≥] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_norm_div_self a, by simp⟩

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

structure ContDiffMoreiraHolderAt (k : ℕ) (α : I) (f : E → F) (a : E) : Prop where
  contDiffAt : ContDiffAt ℝ k f a
  isBigO : (iteratedFDeriv ℝ k f · - iteratedFDeriv ℝ k f a) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ))

theorem ContDiffAt.contDiffMoreiraHolderAt {n : WithTop ℕ∞} {k : ℕ} {f : E → F} {a : E}
    (h : ContDiffAt ℝ n f a) (hk : k < n) (α : I) : ContDiffMoreiraHolderAt k α f a where
  contDiffAt := h.of_le hk.le
  isBigO := calc
    (iteratedFDeriv ℝ k f · - iteratedFDeriv ℝ k f a) =O[𝓝 a] (· - a) :=
      (h.differentiableAt_iteratedFDeriv hk).isBigO_sub
    _ =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) :=
      .of_norm_left <| .comp_tendsto (.id_rpow_of_le_one α.2.2) <| tendsto_norm_sub_self_nhdsGE a

namespace ContDiffMoreiraHolderAt

@[simp]
theorem zero_exponent_iff {k : ℕ} {f : E → F} {a : E} :
    ContDiffMoreiraHolderAt k 0 f a ↔ ContDiffAt ℝ k f a := by
  refine ⟨contDiffAt, fun h ↦ ⟨h, ?_⟩⟩
  simpa using ((h.continuousAt_iteratedFDeriv le_rfl).sub_const _).norm.isBoundedUnder_le

theorem of_exponent_le {k : ℕ} {f : E → F} {a : E} {α β : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (hle : β ≤ α) : ContDiffMoreiraHolderAt k β f a where
  contDiffAt := hf.contDiffAt
  isBigO := hf.isBigO.trans <| by
    refine .comp_tendsto (.rpow_rpow_nhdsGE_zero_of_le hle fun hα ↦ ?_) ?_
    · exact le_antisymm (le_trans (mod_cast hle) hα.le) β.2.1
    · exact tendsto_norm_sub_self_nhdsGE a

theorem of_lt {k l : ℕ} {f : E → F} {a : E} {α β : I} (hf : ContDiffMoreiraHolderAt k α f a)
    (hlt : l < k) : ContDiffMoreiraHolderAt l β f a :=
  hf.contDiffAt.contDiffMoreiraHolderAt (mod_cast hlt) _

theorem of_toLex_le {k l : ℕ} {f : E → F} {a : E} {α β : I} (hf : ContDiffMoreiraHolderAt k α f a)
    (hle : toLex (l, β) ≤ toLex (k, α)) : ContDiffMoreiraHolderAt l β f a :=
  ((Prod.Lex.le_iff _ _).mp hle).elim hf.of_lt <| by rintro ⟨rfl, hle⟩; exact hf.of_exponent_le hle

theorem of_le {k l : ℕ} {f : E → F} {a : E} {α : I} (hf : ContDiffMoreiraHolderAt k α f a)
    (hl : l ≤ k) : ContDiffMoreiraHolderAt l α f a :=
  hf.of_toLex_le <| Prod.Lex.toLex_mono ⟨hl, le_rfl⟩

theorem of_contDiffOn_holderWith {f : E → F} {s : Set E} {k : ℕ} {α : I} {a : E} {C : ℝ≥0}
    (hf : ContDiffOn ℝ k f s) (hs : s ∈ 𝓝 a)
    (hd : HolderOnWith C ⟨α, α.2.1⟩ (iteratedFDeriv ℝ k f) s) :
    ContDiffMoreiraHolderAt k α f a where
  contDiffAt := hf.contDiffAt hs
  isBigO := .of_bound C <| mem_of_superset hs fun x hx ↦ by
    simpa [Real.abs_rpow_of_nonneg, ← dist_eq_norm, dist_nonneg]
      using hd.dist_le hx (mem_of_mem_nhds hs)

theorem fst {k : ℕ} {α : I} {a : E × F} : ContDiffMoreiraHolderAt k α Prod.fst a :=
  contDiffAt_fst.contDiffMoreiraHolderAt (WithTop.coe_lt_top _) α

theorem prodMk {k : ℕ} {α : I} {f : E → F} {g : E → G} {a : E}
    (hf : ContDiffMoreiraHolderAt k α f a) (hg : ContDiffMoreiraHolderAt k α g a) :
    ContDiffMoreiraHolderAt k α (fun x ↦ (f x, g x)) a where
  contDiffAt := hf.contDiffAt.prod hg.contDiffAt
  isBigO := sorry

-- See `YK-moreira` branch in Mathlib
theorem comp {g : F → G} {f : E → F} {a : E} {k : ℕ} {α : I}
    (hg : ContDiffMoreiraHolderAt k α g (f a)) (hf : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a :=
  sorry

theorem continuousLinearMap_comp {f : E → F} {a : E} {k : ℕ} {α : I}
    (hf : ContDiffMoreiraHolderAt k α f a) (g : F →L[ℝ] G) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a where
  contDiffAt := g.contDiff.contDiffAt.comp a hf.contDiffAt
  isBigO := by
    refine .trans (.of_bound ‖g‖ ?_) hf.isBigO
    refine (hf.contDiffAt.eventually (by simp)).mono fun x hx ↦ ?_
    rw [g.iteratedFDeriv_comp_left' hx le_rfl, g.iteratedFDeriv_comp_left' hf.contDiffAt le_rfl]
    -- TODO: add `ContinuousLinearMap.compContinuousMultilinearMap_sub`
    convert g.norm_compContinuousMultilinearMap_le _
    ext; simp

end ContDiffMoreiraHolderAt

structure ContDiffMoreiraHolderOn (k : ℕ) (α : I) (f : E → F) (s U : Set E) : Prop where
  subset : s ⊆ U
  isOpen : IsOpen U
  contDiffOn : ContDiffOn ℝ k f U
  isBigO : ∀ a ∈ s, (iteratedFDeriv ℝ k f · - iteratedFDeriv ℝ k f a) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ))

namespace ContDiffMoreiraHolderOn

variable {f : E → F} {s U : Set E} {k : ℕ} {α : I} {a : E}

theorem contDiffMoreiraHolderAt (h : ContDiffMoreiraHolderOn k α f s U) (ha : a ∈ s) :
    ContDiffMoreiraHolderAt k α f a :=
  ⟨h.contDiffOn.contDiffAt <| h.isOpen.mem_nhds <| h.subset ha, h.isBigO a ha⟩

theorem fst {s U : Set (E × F)} (hsub : s ⊆ U) (ho : IsOpen U) :
    ContDiffMoreiraHolderOn k α Prod.fst s U :=
  ⟨hsub, ho, contDiffOn_fst, fun _ _ ↦ ContDiffMoreiraHolderAt.fst.isBigO⟩

theorem prodMk {g : E → G} (hf : ContDiffMoreiraHolderOn k α f s U)
    (hg : ContDiffMoreiraHolderOn k α g s U) :
    ContDiffMoreiraHolderOn k α (fun x ↦ (f x, g x)) s U where
  __ := hf
  contDiffOn := hf.contDiffOn.prod hg.contDiffOn
  isBigO _a ha := ((hf.contDiffMoreiraHolderAt ha).prodMk (hg.contDiffMoreiraHolderAt ha)).isBigO

theorem _root_.ContDiffOn.contDiffMoreiraHolderOn {n : WithTop ℕ∞} (h : ContDiffOn ℝ n f U)
    (hs : s ⊆ U) (hU : IsOpen U) (hk : k < n) (α : I) : ContDiffMoreiraHolderOn k α f s U where
  subset := hs
  isOpen := hU
  contDiffOn := h.of_le hk.le
  isBigO _a ha := ((h.contDiffAt <| hU.mem_nhds <| hs ha).contDiffMoreiraHolderAt hk _).isBigO

theorem of_toLex_le (h : ContDiffMoreiraHolderOn k α f s U) {l β}
    (hl : toLex (l, β) ≤ toLex (k, α)) :
    ContDiffMoreiraHolderOn l β f s U where
  __ := h
  contDiffOn := h.contDiffOn.of_le <| mod_cast monotone_fst_ofLex hl
  isBigO _a ha := ((h.contDiffMoreiraHolderAt ha).of_toLex_le hl).isBigO

theorem of_lt (h : ContDiffMoreiraHolderOn k α f s U) {l β} (hl : l < k) :
    ContDiffMoreiraHolderOn l β f s U :=
  h.of_toLex_le <| .left _ _ hl

theorem of_le (h : ContDiffMoreiraHolderOn k α f s U) {l} (hl : l ≤ k) :
    ContDiffMoreiraHolderOn l α f s U :=
  h.of_toLex_le <| Prod.Lex.toLex_mono ⟨hl, le_rfl⟩

theorem comp {g : F → G} {t V : Set F} (hg : ContDiffMoreiraHolderOn k α g t V)
    (hf : ContDiffMoreiraHolderOn k α f s U) (hUV : MapsTo f U V) (hst : MapsTo f s t)
    (hk : k ≠ 0) :
    ContDiffMoreiraHolderOn k α (g ∘ f) s U where
  __ := hf
  contDiffOn := hg.contDiffOn.comp hf.contDiffOn hUV
  isBigO _a ha := ((hg.contDiffMoreiraHolderAt <| hst ha).comp
    (hf.contDiffMoreiraHolderAt ha) hk).isBigO

theorem continuousLinearMap_comp (hf : ContDiffMoreiraHolderOn k α f s U) (g : F →L[ℝ] G) :
    ContDiffMoreiraHolderOn k α (g ∘ f) s U where
  __ := hf
  contDiffOn := g.contDiff.comp_contDiffOn hf.contDiffOn
  isBigO _a ha := ((hf.contDiffMoreiraHolderAt ha).continuousLinearMap_comp g).isBigO

end ContDiffMoreiraHolderOn
