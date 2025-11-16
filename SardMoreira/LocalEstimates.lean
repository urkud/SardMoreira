import Mathlib

open scoped Topology NNReal unitInterval
open Asymptotics Filter MeasureTheory AffineMap Set

-- From Mathlib
@[simp]
lemma UniformSpace.Completion.coe_eq_zero_iff {α : Type*} [UniformSpace α] [Zero α] [T0Space α]
    {x : α} : (x : Completion α) = 0 ↔ x = 0 :=
  (Completion.coe_injective α).eq_iff

lemma MeasureTheory.Measure.ae_ne {α : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [NoAtoms μ] (a : α) : ∀ᵐ x ∂μ, x ≠ a :=
  (countable_singleton a).ae_not_mem μ

section NormedField

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma dist_le_mul_volume_of_norm_deriv_le {f : ℝ → E} {a b C : ℝ}
    (hfd : DifferentiableOn ℝ f (Set.uIcc a b)) (hnorm : ∀ᵐ t, t ∈ Set.uIcc a b → ‖deriv f t‖ ≤ C) :
    dist (f a) (f b) ≤ C * volume.real {x ∈ Set.uIcc a b | deriv f x ≠ 0} := by
  set s := {x ∈ uIcc a b | deriv f x ≠ 0}
  wlog hab : a < b generalizing a b
  · rcases (not_lt.mp hab).eq_or_lt with rfl | hlt
    · have : volume s = 0 := measure_mono_null (by simp [s]) (measure_singleton b)
      simp [this, Measure.real]
    · rw [dist_comm]
      simp only [s]
      rw [uIcc_comm] at hfd hnorm ⊢
      apply this <;> assumption
  have hC₀ : 0 ≤ C := by
    have : ∃ᵐ t, t ∈ uIcc a b := by simp [frequently_ae_iff, sub_eq_zero, hab.ne']
    rcases hnorm.and_frequently this |>.exists with ⟨t, ht₁, ht₂⟩
    exact (norm_nonneg _).trans (ht₁ ht₂)
  wlog hE : CompleteSpace E generalizing E
  · set g : ℝ → UniformSpace.Completion E := (↑) ∘ f with hg
    have hgd : DifferentiableOn ℝ g (Set.uIcc a b) :=
      UniformSpace.Completion.toComplL.differentiable.comp_differentiableOn hfd
    have hdg : ∀ᵐ t, t ∈ Set.uIcc a b → deriv g t = deriv f t := by
      filter_upwards [hnorm, volume.ae_ne (min a b), volume.ae_ne (max a b)]
        with t hft htmin htmax htuIcc
      have : HasFDerivAt (𝕜 := ℝ) (↑) UniformSpace.Completion.toComplL (f t) := by
        rw [← UniformSpace.Completion.coe_toComplL (𝕜 := ℝ)]
        exact (UniformSpace.Completion.toComplL (E := E) (𝕜 := ℝ)).hasFDerivAt
      have hdft : HasDerivAt f (deriv f t) t :=
        hfd.hasDerivAt <| Icc_mem_nhds (lt_of_le_of_ne htuIcc.1 htmin.symm)
          (lt_of_le_of_ne htuIcc.2 htmax)
      rw [hg, (this.comp_hasDerivAt t hdft).deriv, UniformSpace.Completion.coe_toComplL]
    have hgn : ∀ᵐ t, t ∈ Set.uIcc a b → ‖deriv g t‖ ≤ C := by
      filter_upwards [hnorm, hdg] with t hft ht ht_mem
      rw [ht ht_mem, UniformSpace.Completion.norm_coe]
      exact hft ht_mem
    have hgs : s =ᵐ[volume] {t ∈ uIcc a b | deriv g t ≠ 0} := by
      refine .set_eq ?_
      filter_upwards [hdg] with t ht
      simp +contextual [s, ht]
    convert this hgd hgn inferInstance using 1
    · simp [g]
    · rw [measureReal_congr hgs]
  set s := {x ∈ uIcc a b | deriv f x ≠ 0}
  calc
    dist (f a) (f b) ≤ ‖∫ t in uIcc a b, deriv f t‖ := by
      rw [dist_eq_norm_sub', ← intervalIntegral.integral_eq_sub_of_hasDeriv_right]
      · rw [intervalIntegral.norm_integral_eq_norm_integral_uIoc,
          Measure.restrict_congr_set uIoc_ae_eq_interval]
      · exact hfd.continuousOn
      · intro t ht
        exact hfd.hasDerivAt (Icc_mem_nhds ht.1 ht.2) |>.hasDerivWithinAt
      · refine (intervalIntegrable_const (c := C)).mono_fun' ?_ ?_
        · apply aestronglyMeasurable_deriv
        · rwa [Measure.restrict_congr_set uIoc_ae_eq_interval, Filter.EventuallyLE,
            ae_restrict_iff']
          exact measurableSet_uIcc
    _ = ‖∫ t in s, deriv f t‖ := by
      rw [setIntegral_eq_of_subset_of_ae_diff_eq_zero]
      · exact measurableSet_uIcc.nullMeasurableSet
      · exact inter_subset_left
      · apply ae_of_all
        rintro t ⟨ht, hts⟩
        simpa [s, ht] using hts
    _ ≤ C * volume.real s := by
      apply norm_setIntegral_le_of_norm_le_const_ae'
      · calc
          volume s ≤ volume (uIcc a b) := by gcongr; apply inter_subset_left
          _ < ⊤ := by simp
      · exact hnorm.mono fun t ht hts ↦ ht hts.1

lemma dist_le_mul_volume_of_norm_lineDeriv_le {f : E → F} {a b : E} {C : ℝ≥0}
    (hf : DifferentiableOn ℝ f (segment ℝ a b))
    (hf' : ∀ᵐ t : ℝ, t ∈ I → ‖lineDeriv ℝ f (lineMap a b t) (b - a)‖ ≤ C) :
    ‖f b - f a‖ ≤ C * volume.real {t ∈ I | lineDeriv ℝ f (lineMap a b t) (b - a) ≠ 0} := by
  set g : ℝ → F := fun t ↦ f (lineMap a b t)
  have hdg (t : ℝ) : deriv g t = lineDeriv ℝ f (lineMap a b t) (b - a) := by
    conv_lhs => rw [← zero_add t, ← deriv_comp_add_const]
    rw [lineDeriv]
    simp [lineMap_apply_module', g, add_smul, add_assoc, add_comm, add_left_comm]
  suffices dist (g 0) (g 1) ≤ C * volume.real {t ∈ uIcc 0 1 | deriv g t ≠ 0} by
    simpa [g, ← hdg, dist_eq_norm_sub'] using this
  apply dist_le_mul_volume_of_norm_deriv_le
  · refine hf.comp (lineMap _ _).differentiableOn ?_
    simp [segment_eq_image_lineMap, mapsTo_image]
  · simpa [hdg] using hf'
