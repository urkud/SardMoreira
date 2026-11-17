module

public import Mathlib

@[expose] public section

open scoped ENNReal NNReal Filter Uniformity Topology
open Function

noncomputable section

namespace Metric.Snowflaking

variable {X : Type*} {α : ℝ} {hα₀ : 0 < α} {hα₁ : α ≤ 1}

variable [MeasurableSpace X]

instance instMeasurableSpace : MeasurableSpace (Snowflaking X α hα₀ hα₁) :=
  .comap ofSnowflaking ‹_›

@[fun_prop]
theorem measurable_ofSnowflaking : Measurable (ofSnowflaking : Snowflaking X α hα₀ hα₁ → X) :=
  comap_measurable _

@[fun_prop]
theorem measurable_toSnowflaking : Measurable (toSnowflaking : X → Snowflaking X α hα₀ hα₁) :=
  .of_comap_le <| by
    rw [instMeasurableSpace, MeasurableSpace.comap_comp, ofSnowflaking_comp_toSnowflaking,
      MeasurableSpace.comap_id]

/-
Define a measurable equivalence between this space and X.
-/
@[simps! -fullyApplied toEquiv apply symm_apply]
def measurableEquiv : Snowflaking X α hα₀ hα₁ ≃ᵐ X where
  toEquiv := ofSnowflaking
  measurable_toFun := measurable_ofSnowflaking
  measurable_invFun := measurable_toSnowflaking

theorem measurableEmbedding_toSnowflaking :
    MeasurableEmbedding (toSnowflaking : X → Snowflaking X α hα₀ hα₁) :=
  measurableEquiv.symm.measurableEmbedding

instance [TopologicalSpace X] [BorelSpace X] : BorelSpace (Snowflaking X α hα₀ hα₁) :=
  measurableEquiv.measurableEmbedding.borelSpace homeomorph.isInducing

end Metric.Snowflaking

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X] {α : ℝ} {hα₀ : 0 < α} {hα₁ : α ≤ 1} {μ : Measure X}

open Metric Metric.Snowflaking

variable (α hα₀ hα₁) in
def snowflaking (μ : Measure X) : Measure (Snowflaking X α hα₀ hα₁) :=
  μ.map toSnowflaking

theorem snowflaking_apply (μ : Measure X) (s : Set (Snowflaking X α hα₀ hα₁)) :
    μ.snowflaking α hα₀ hα₁ s = μ (toSnowflaking ⁻¹' s) := by
  rw [snowflaking, measurableEmbedding_toSnowflaking.map_apply]

instance [IsFiniteMeasure μ] : IsFiniteMeasure (μ.snowflaking α hα₀ hα₁) := by
  unfold snowflaking
  infer_instance

instance [SigmaFinite μ] : SigmaFinite (μ.snowflaking α hα₀ hα₁) :=
  measurableEquiv.symm.measurableEmbedding.sigmaFinite_map

instance [SFinite μ] : SFinite (μ.snowflaking α hα₀ hα₁) := by
  unfold snowflaking
  infer_instance

section TopologicalSpace

variable [TopologicalSpace X]

-- TODO: generalize to a homeomorphism
instance [IsLocallyFiniteMeasure μ] : IsLocallyFiniteMeasure (μ.snowflaking α hα₀ hα₁) where
  finiteAtNhds := by
    intro x
    rcases μ.finiteAt_nhds x.ofSnowflaking with ⟨s, hsx, hμs⟩
    simp only [homeomorph.nhds_eq_comap, homeomorph_apply]
    refine ⟨_, Filter.preimage_mem_comap hsx, ?_⟩
    rwa [snowflaking, measurableEmbedding_toSnowflaking.map_apply]

instance [IsFiniteMeasureOnCompacts μ] : IsFiniteMeasureOnCompacts (μ.snowflaking α hα₀ hα₁) where
  lt_top_of_isCompact := by
    intro K hK
    rw [snowflaking_apply, ← image_ofSnowflaking_eq_preimage]
    exact hK.image continuous_ofSnowflaking |>.measure_lt_top

instance [μ.OuterRegular] : (μ.snowflaking α hα₀ hα₁).OuterRegular := by
  refine ⟨fun A hA r hr ↦ ?_⟩
  rw [snowflaking_apply] at hr
  rcases Set.exists_isOpen_lt_of_lt _ r hr with ⟨U, hAU, hUo, hU⟩
  refine ⟨ofSnowflaking ⁻¹' U, ?_, hUo.preimage continuous_ofSnowflaking,
    by rwa [snowflaking_apply]⟩
  intro x hx
  exact hAU hx

instance [μ.InnerRegular] : (μ.snowflaking α hα₀ hα₁).InnerRegular := by
  constructor
  rw [snowflaking, ← measurableEquiv_symm_apply]
  exact InnerRegular.innerRegular.map' _ measurable_toSnowflaking fun K hK ↦
    hK.image continuous_toSnowflaking

instance [μ.WeaklyRegular] : (μ.snowflaking α hα₀ hα₁).WeaklyRegular where
  innerRegular := by
    rw [snowflaking, ← measurableEquiv_symm_apply]
    apply WeaklyRegular.innerRegular.map'
    · exact fun U hU ↦ hU.preimage continuous_toSnowflaking
    · intro K hK
      rwa [measurableEquiv_symm_apply, ← homeomorph_symm_apply, Homeomorph.isClosed_image]

instance [μ.InnerRegularCompactLTTop] : (μ.snowflaking α hα₀ hα₁).InnerRegularCompactLTTop where
  innerRegular := by
    rw [snowflaking, ← measurableEquiv_symm_apply]
    apply InnerRegularCompactLTTop.innerRegular.map'
    · rintro U ⟨hUm, hμU⟩
      rw [MeasurableEquiv.map_apply] at hμU
      exact ⟨hUm.preimage <| MeasurableEquiv.measurable _, hμU⟩
    · exact fun K hK ↦ hK.image continuous_toSnowflaking

instance [μ.Regular] : (μ.snowflaking α hα₀ hα₁).Regular where
  innerRegular := by
    rw [snowflaking, ← measurableEquiv_symm_apply]
    apply Regular.innerRegular.map'
    · exact fun U hU ↦ hU.preimage continuous_toSnowflaking
    · exact fun K hK ↦ hK.image continuous_toSnowflaking

end TopologicalSpace

@[simp]
theorem snowflaking_hausdorffMeasure [EMetricSpace X] [BorelSpace X] (d : ℝ) :
    (μH[d] : Measure X).snowflaking α hα₀ hα₁ = μH[d / α] := by
  ext s hs
  simp only [snowflaking_apply, hausdorffMeasure_apply,
    ← (Surjective.piMap fun _ : ℕ ↦
      (toSnowflaking : X ≃ Snowflaking X α hα₀ hα₁).injective.preimage_surjective).iInf_comp,
    Pi.map_apply, ← Set.preimage_iUnion, toSnowflaking.surjective.preimage_subset_preimage_iff,
    ediam_preimage_toSnowflaking, toSnowflaking.surjective.nonempty_preimage,
    ENNReal.rpow_inv_le_iff hα₀]
  apply (ENNReal.rpow_left_surjective hα₀.ne').iSup_congr
  intro r
  simp [← ENNReal.rpow_mul, div_eq_inv_mul, pos_iff_ne_zero, hα₀, hα₀.le]

instance [PseudoMetricSpace X] [IsUnifLocDoublingMeasure μ] :
    IsUnifLocDoublingMeasure (μ.snowflaking α hα₀ hα₁) where
  exists_measure_closedBall_le_mul'' := by
    use IsUnifLocDoublingMeasure.scalingConstantOf μ (2 ^ α⁻¹)
    rcases (nhdsGT_basis _).eventually_iff.mp
      (IsUnifLocDoublingMeasure.eventually_measure_le_scaling_constant_mul μ (2 ^ α⁻¹))
      with ⟨r, hr₀, hr⟩
    filter_upwards [Ioo_mem_nhdsGT (show 0 < r ^ α by positivity)]
    rintro a ⟨ha₀, ha⟩ x
    simpa (disch := positivity) [snowflaking_apply, Real.mul_rpow, Real.rpow_pos_of_pos,
      Real.rpow_inv_lt_iff_of_pos, *] using fun h ↦ @hr (a ^ α⁻¹) h x.ofSnowflaking

end MeasureTheory.Measure
