import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Topology NNReal unitInterval
open Asymptotics Filter MeasureTheory AffineMap Set

lemma MeasureTheory.Measure.ae_ne {α : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [NoAtoms μ] (a : α) : ∀ᵐ x ∂μ, x ≠ a :=
  (countable_singleton a).ae_notMem μ

section NormedField

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem lineMap_mem_openSegment (a b : E) {t : ℝ} (ht : t ∈ Ioo 0 1) :
    lineMap a b t ∈ openSegment ℝ a b :=
  (openSegment_eq_image_lineMap _ _ _).superset <| mem_image_of_mem _ ht

theorem DifferentiableAt.lineDifferentiableAt {f : E → F} {a b : E} (hf : DifferentiableAt ℝ f a) :
    LineDifferentiableAt ℝ f a b :=
  hf.hasFDerivAt.hasLineDerivAt _ |>.lineDifferentiableAt

lemma dist_le_integral_of_norm_deriv_le_of_le {f : ℝ → E} {B : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn f (Set.Icc a b)) (hfd : DifferentiableOn ℝ f (Set.Ioo a b))
    (hfB : ∀ᵐ t, t ∈ Ioo a b → ‖deriv f t‖ ≤ B t)
    (hBi : IntervalIntegrable B volume a b) : dist (f a) (f b) ≤ ∫ t in a..b, B t := by
  wlog hE : CompleteSpace E generalizing E
  · set g : ℝ → UniformSpace.Completion E := (↑) ∘ f with hg
    have hgc : ContinuousOn g (Icc a b) :=
      (UniformSpace.Completion.continuous_coe E).comp_continuousOn hfc
    have hgd : DifferentiableOn ℝ g (Ioo a b) :=
      UniformSpace.Completion.toComplL.differentiable.comp_differentiableOn hfd
    have hdg : ∀ t ∈ Set.Ioo a b, deriv g t = deriv f t := by
      intro t ht
      have : HasFDerivAt (𝕜 := ℝ) (↑) UniformSpace.Completion.toComplL (f t) := by
        rw [← UniformSpace.Completion.coe_toComplL (𝕜 := ℝ)]
        exact (UniformSpace.Completion.toComplL (E := E) (𝕜 := ℝ)).hasFDerivAt
      have hdft : HasDerivAt f (deriv f t) t := hfd.hasDerivAt <| Ioo_mem_nhds ht.1 ht.2
      rw [hg, (this.comp_hasDerivAt t hdft).deriv, UniformSpace.Completion.coe_toComplL]
    have hgn : ∀ᵐ t, t ∈ Ioo a b → ‖deriv g t‖ ≤ B t :=
      hfB.mono fun t htB ht ↦ by
        simpa only [hdg t ht, UniformSpace.Completion.norm_coe] using htB ht
    simpa [g] using this hgc hgd hgn inferInstance
  have hfB' : (‖deriv f ·‖) ≤ᵐ[volume.restrict (uIoc a b)] B := by
    rwa [uIoc_of_le hab, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc, EventuallyLE,
        ae_restrict_iff' measurableSet_Ioo]
  rw [dist_eq_norm_sub', ← intervalIntegral.integral_eq_sub_of_hasDeriv_right (f' := deriv f)]
  · apply intervalIntegral.norm_integral_le_of_norm_le hab _ hBi
    rwa [← ae_restrict_iff' measurableSet_Ioc, ← uIoc_of_le hab]
  · rwa [uIcc_of_le hab]
  · rw [min_eq_left hab, max_eq_right hab]
    intro t ht
    exact hfd.hasDerivAt (isOpen_Ioo.mem_nhds ht) |>.hasDerivWithinAt
  · apply hBi.mono_fun (aestronglyMeasurable_deriv _ _)
    exact hfB'.trans <| .of_forall fun _ ↦ le_abs_self _

lemma dist_le_mul_volume_of_norm_deriv_le_of_le {f : ℝ → E} {a b C : ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn f (Icc a b)) (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hnorm : ∀ᵐ t, t ∈ Ioo a b → ‖deriv f t‖ ≤ C) :
    dist (f a) (f b) ≤ C * volume.real {x ∈ Ioo a b | deriv f x ≠ 0} := by
  set s := toMeasurable volume {x | deriv f x ≠ 0}
  have hsm : MeasurableSet s := by measurability
  calc
    dist (f a) (f b) ≤ ∫ t in a..b, indicator s (fun _ ↦ C) t := by
      apply dist_le_integral_of_norm_deriv_le_of_le hab hfc hfd
      · refine hnorm.mono fun t ht ht_mem ↦ ?_
        apply le_indicator_apply
        · exact fun ht' ↦ ht ht_mem
        · simp only [s, norm_le_zero_iff]
          exact not_imp_comm.2 fun h ↦ subset_toMeasurable _ _ h
      · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
        refine (integrableOn_const ?_ ?_).indicator hsm <;> simp
    _ = C * volume.real {x ∈ Ioo a b | deriv f x ≠ 0} := by
      rw [intervalIntegral.integral_of_le hab, Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm,
        integral_indicator hsm, Measure.restrict_restrict hsm,
        setIntegral_const, smul_eq_mul, mul_comm]
      simp only [s, Measure.real,
        Measure.measure_toMeasurable_inter_of_sFinite measurableSet_Ioo]
      simp only [inter_def, mem_setOf_eq, and_comm]

lemma dist_le_mul_volume_of_norm_lineDeriv_le {f : E → F} {a b : E} {C : ℝ}
    (hfc : ContinuousOn f (segment ℝ a b))
    (hfd : ∀ t ∈ Ioo (0 : ℝ) 1, LineDifferentiableAt ℝ f (lineMap a b t) (b - a))
    (hf' : ∀ᵐ t : ℝ, t ∈ Ioo (0 : ℝ) 1 → ‖lineDeriv ℝ f (lineMap a b t) (b - a)‖ ≤ C) :
    ‖f b - f a‖ ≤
      C * volume.real {t ∈ Ioo (0 : ℝ) 1 | lineDeriv ℝ f (lineMap a b t) (b - a) ≠ 0} := by
  set g : ℝ → F := fun t ↦ f (lineMap a b t)
  have hgc : ContinuousOn g (Icc 0 1) := by
    refine hfc.comp ?_ ?_
    · exact AffineMap.lineMap_continuous.continuousOn
    · simp [segment_eq_image_lineMap, mapsTo_image]
  have hdg (t : ℝ) (ht : t ∈ Ioo 0 1) : HasDerivAt g (lineDeriv ℝ f (lineMap a b t) (b - a)) t := by
    have := (hfd t ht).hasLineDerivAt.scomp_of_eq (𝕜 := ℝ) t ((hasDerivAt_id t).sub_const t)
    simpa [g, lineMap_apply_module', Function.comp_def, sub_smul, add_comm _ a] using this
  suffices dist (g 0) (g 1) ≤ C * volume.real {t ∈ Ioo 0 1 | deriv g t ≠ 0} by
    convert this using 1
    · simp [g, dist_eq_norm_sub']
    · congr 2 with t
      simp +contextual [(hdg _ _).deriv]
  apply dist_le_mul_volume_of_norm_deriv_le_of_le zero_le_one hgc
  · exact fun t ht ↦ (hdg t ht).differentiableAt.differentiableWithinAt
  · exact hf'.mono fun t ht ht_mem ↦ by simpa only [(hdg t ht_mem).deriv] using ht ht_mem

lemma dist_le_mul_volume_of_norm_fderiv_le {f : E → F} {a b : E} {C : ℝ} {s : Set E}
    (hs : IsOpen s) (hf : DiffContOnCl ℝ f s) (hab : openSegment ℝ a b ⊆ s)
    (hC : ∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ C) :
    ‖f b - f a‖ ≤
      C * ‖b - a‖ * volume.real {t ∈ Ioo (0 : ℝ) 1 | fderiv ℝ f (lineMap a b t) ≠ 0} := by
  have hmem_s : ∀ t ∈ Ioo (0 : ℝ) 1, lineMap a b t ∈ s := fun t ht ↦
    hab <| lineMap_mem_openSegment a b ht
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans <| hC _ <| hmem_s (1 / 2) (by norm_num)
  have hfc : ContinuousOn f (segment ℝ a b) :=
    hf.continuousOn.mono <| segment_subset_closure_openSegment.trans <| closure_mono hab
  have hfd : ∀ t ∈ Ioo (0 : ℝ) 1, LineDifferentiableAt ℝ f (lineMap a b t) (b - a) := fun t ht ↦
    (hf.differentiableAt hs <| hmem_s t ht).lineDifferentiableAt
  have hfC : ∀ t ∈ Ioo (0 : ℝ) 1, ‖lineDeriv ℝ f (lineMap a b t) (b - a)‖ ≤ C * ‖b - a‖ := by
    intro t ht
    rw [DifferentiableAt.lineDeriv_eq_fderiv]
    · exact ContinuousLinearMap.le_of_opNorm_le _ (hC _ <| hmem_s t ht) _
    · exact hf.differentiableAt hs <| hmem_s t ht
  refine dist_le_mul_volume_of_norm_lineDeriv_le hfc hfd (.of_forall hfC) |>.trans ?_
  gcongr
  · refine ne_top_of_le_ne_top ?_ (measure_mono inter_subset_left)
    simp
  · contrapose!
    simp +contextual [(hf.differentiableAt hs <| hmem_s _ ‹_›).lineDeriv_eq_fderiv]

