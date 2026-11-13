module

public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import SardMoreira.LebesgueDensity
public import SardMoreira.ContDiff

@[expose] public section

open scoped Topology NNReal ENNReal unitInterval
open Asymptotics Filter MeasureTheory AffineMap Set Metric

theorem UniformSpace.Completion.hasFDerivAt_coe {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {a : E} :
    HasFDerivAt ((↑) : E → Completion E) (toComplL : E →L[𝕜] Completion E) a := by
  simpa using (toComplL (S := 𝕜) (α := E)).hasFDerivAt

section NormedField

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem openSegment_subset_ball_left {x y : E} (h : x ≠ y) :
    openSegment ℝ x y ⊆ ball x ‖y - x‖ := by
  rw [openSegment_eq_image_lineMap, ← mapsTo_iff_image_subset]
  intro t ht
  rw [mem_ball, dist_lineMap_left, dist_eq_norm_sub', Real.norm_of_nonneg ht.1.le]
  exact mul_lt_of_lt_one_left (by simpa [sub_eq_zero, eq_comm] using h) ht.2

open UniformSpace (Completion) in
theorem sub_isLittleO_norm_rpow_add_one_of_fderiv_of_density_point [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {f : E → F} {a : E} {r : ℝ}
    {μ : Measure E} [μ.IsAddHaarMeasure] {s : Set E}
    (hr : 0 ≤ r) (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x)
    (hderiv : fderiv ℝ f =O[𝓝 a] (‖· - a‖ ^ r))
    (hs : fderiv ℝ f =ᶠ[𝓝[s] a] 0)
    (hmeas : Tendsto (fun r ↦ μ (s ∩ closedBall a r) / μ (closedBall a r)) (𝓝[>] 0) (𝓝 1)) :
    (f · - f a) =o[𝓝 a] (‖· - a‖ ^ (r + 1)) := by
  wlog hF : CompleteSpace F generalizing F
  · set e : F →L[ℝ] Completion F := Completion.toComplL
    set g := e ∘ f
    have hdg_eq : fderiv ℝ g =ᶠ[𝓝 a] (e ∘L fderiv ℝ f ·) :=
      hdf.mono fun x hx ↦ (e.hasFDerivAt.comp _ hx.hasFDerivAt).fderiv
    have hdg : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ g x :=
      hdf.mono fun x hx ↦ e.differentiableAt.comp _ hx
    have hg_deriv : fderiv ℝ g =O[𝓝 a] fun x ↦ ‖x - a‖ ^ r := by
      calc
        fderiv ℝ g =ᶠ[𝓝 a] (e ∘L fderiv ℝ f ·) := hdg_eq
        _ =O[𝓝 a] (‖e‖ * ‖fderiv ℝ f ·‖) :=
          .of_norm_le fun _ ↦ ContinuousLinearMap.opNorm_comp_le _ _
        _ =O[𝓝 a] fderiv ℝ f := by
          refine .of_norm_right <| .const_mul_left (isBigO_refl _ _) _
        _ =O[𝓝 a] (‖· - a‖ ^ r) := by
          exact hderiv
    have hg₀ : fderiv ℝ g =ᶠ[𝓝[s] a] 0 := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hdg_eq, hs] with x hx₁ hx₂
      simp [hx₁, hx₂]
    refine IsBigO.trans_isLittleO (.of_norm_right ?_) (this hdg hg_deriv hg₀ inferInstance)
    simp_rw [g, Function.comp_apply, ← map_sub, e, Completion.coe_toComplL, Completion.norm_coe]
    exact (isBigO_refl _ _).norm_right
  wlog hsm : MeasurableSet s generalizing s
  · -- TODO: I'm getting a timeout without this line. Test with the latest Mathlib
    have aux : MeasurableSingletonClass (E →L[ℝ] F) :=
      OpensMeasurableSpace.toMeasurableSingletonClass
    apply @this (toMeasurable μ s ∩ {x | fderiv ℝ f x = 0})
    · refine hmeas.congr' ?_
      rw [EventuallyEq, eventually_nhdsWithin_iff] at hs
      rcases Metric.eventually_nhds_iff_ball.mp hs with ⟨r, hr₀, hr⟩
      filter_upwards [Ioo_mem_nhdsGT hr₀] with δ ⟨hδ₀, hδr⟩
      rw [inter_assoc, Measure.measure_toMeasurable_inter_of_sfinite, ← inter_assoc,
        inter_right_comm, inter_eq_self_of_subset_left (_ : s ∩ _ ⊆ _)]
      · refine fun y hy ↦ hr _ (closedBall_subset_ball hδr hy.2) hy.1
      · exact (measurableSet_eq.preimage (measurable_fderiv _ _)).inter measurableSet_closedBall
    · exact eventually_mem_nhdsWithin.mono fun x hx ↦ hx.2
    · refine measurableSet_toMeasurable _ _ |>.inter ?_
      refine measurableSet_eq.preimage (measurable_fderiv _ _)
  rw [isLittleO_iff]
  intro c hc
  lift c to ℝ≥0 using hc.le
  rcases hderiv.exists_pos with ⟨C, hC₀, hC⟩
  rw [isBigOWith_iff] at hC
  lift C to ℝ≥0 using hC₀.le
  norm_cast at hc hC₀
  rcases exists_pos_forall_measure_le_exists_mem_sphere_dist_lt_volume_lineMap_mem_lt (E := E)
    (show c / C / 2 ≠ 0 by positivity) with ⟨δ, hδ₀, hδ⟩
  specialize hδ μ
  replace hmeas : ∀ᶠ r in 𝓝[>] 0, μ (sᶜ ∩ closedBall a r) ≤ δ * μ (closedBall a r) := by
    refine hmeas.eventually_const_lt (show 1 - δ < (1 : ℝ≥0∞) by simpa [ENNReal.sub_lt_self_iff])
      |>.mono fun r hr ↦ ?_
    replace hr := ENNReal.mul_lt_of_lt_div hr
    have : μ (closedBall a r ∩ s) ≠ ∞ :=
      measure_ne_top_of_subset inter_subset_left measure_closedBall_lt_top.ne
    rw [inter_comm, ← sdiff_eq, ← ENNReal.add_le_add_iff_left this, measure_inter_add_sdiff _ hsm,
      ← tsub_le_iff_right, inter_comm]
    rw [ENNReal.sub_mul, one_mul] at hr
    exacts [hr.le, fun _ _ ↦ measure_closedBall_lt_top.ne]
  rw [eventually_nhds_iff_ball]
  rw [EventuallyEq, eventually_nhdsWithin_iff] at hs
  rcases eventually_nhds_iff_ball.mp (hdf.and <| hs.and hC) with ⟨ε, hε₀, hε⟩
  choose hdf hdfs hdfr using hε
  rw [(nhdsGT_basis (0 : ℝ)).eventually_iff] at hmeas
  rcases hmeas with ⟨ε', hε₀', hε'⟩
  use min ε ε', by positivity
  intro y hy
  rcases eq_or_ne y a with rfl | hya
  · simp; positivity
  obtain ⟨z, hz_mem, hzy, hz_vol⟩ : ∃ z ∈ sphere a ‖y - a‖, dist z y < ↑(c / C / 2) * ‖y - a‖ ∧
      volume {t : ℝ | 0 ≤ t ∧ lineMap a z t ∈ sᶜ ∩ ball a ‖y - a‖} < ↑(c / C / 2) := by
    refine hδ ‖y - a‖ (by simpa [sub_eq_zero]) a (sᶜ ∩ ball a ‖y - a‖) ?_ y (by simp)
    have : Nontrivial E := ⟨⟨_, _, hya⟩⟩
    grw [← Measure.addHaar_closedBall_eq_addHaar_ball, ← hε', ball_subset_closedBall]
    grw [min_le_right] at hy
    simpa [sub_eq_zero, hya, dist_eq_norm_sub] using hy
  have hsub : closedBall a ‖y - a‖ ⊆ ball a ε := by
    apply closedBall_subset_ball
    grw [mem_ball_iff_norm, min_le_left] at hy
    exact hy
  have hz_norm : ‖z - a‖ = ‖y - a‖ := by simpa using hz_mem
  have hyz : ‖f y - f z‖ ≤ (c / 2) * ‖y - a‖ ^ (r + 1) := calc
    ‖f y - f z‖ ≤ C * ‖y - a‖ ^ r * ‖y - z‖ := by
      apply (convex_closedBall a ‖y - a‖).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      · exact fun w hw ↦ hdf w <| hsub hw
      · intro w hw
        grw [hdfr _ (hsub hw), Real.norm_of_nonneg (by positivity), mem_closedBall_iff_norm.mp hw]
      · exact sphere_subset_closedBall hz_mem
      · simp [dist_eq_norm_sub]
    _ ≤ (c / 2) * ‖y - a‖ ^ (r + 1) := by
      grw [← dist_eq_norm_sub' z y, hzy, Real.rpow_add_one' (by positivity) (by positivity)]
      apply le_of_eq
      push_cast
      field_simp
  have hza : ‖f z - f a‖ ≤ (c / 2) * ‖y - a‖ ^ (r + 1) := by
    grw [norm_sub_le_mul_volume_of_norm_fderiv_le (C := C * ‖y - a‖ ^ r) _ _
      (openSegment_subset_ball_left _)]
    · have H :
          volume.real {t : ℝ | t ∈ Ioo 0 1 ∧ fderiv ℝ f ((lineMap a z) t) ≠ 0} < (c / C / 2) := by
        rw [Measure.real]
        apply ENNReal.toReal_lt_of_lt_ofReal
        norm_cast
        rw [ENNReal.ofReal_coe_nnreal]
        refine lt_of_le_of_lt ?_ hz_vol
        gcongr 2 with t
        rintro ⟨⟨ht₀, ht₁⟩, ht⟩
        have : (lineMap a z) t ∈ ball a ‖y - a‖ := by
          -- TODO: Part of the proof of `openSegment_subset_ball_left`. Move to a lemma?
          rw [mem_ball, dist_lineMap_left, Real.norm_of_nonneg ht₀.le, dist_comm, hz_mem]
          exact mul_lt_of_lt_one_left (by simpa [sub_eq_zero]) ht₁
        refine ⟨ht₀.le, ?_, this⟩
        contrapose ht
        apply hdfs
        · grw [← hsub, ← ball_subset_closedBall]
          exact this
        · simpa using ht
      grw [H, hz_norm, Real.rpow_add_one' (by positivity) (by positivity)]
      apply le_of_eq
      field_simp
    · intro w hw
      grw [hdfr, Real.norm_of_nonneg (by positivity), mem_ball_iff_norm.mp hw, hz_norm]
      grw [← hsub, ← ball_subset_closedBall, ← hz_norm]
      exact hw
    · exact isOpen_ball
    · apply DifferentiableOn.diffContOnCl_ball (U := ball a ε)
      · exact fun w hw ↦ (hdf w hw).differentiableWithinAt
      · grw [hz_norm, hsub]
    · rintro rfl
      simpa [sub_eq_zero, hya] using hz_norm.symm
  grw [norm_sub_le_norm_sub_add_norm_sub _ (f z), hyz, hza, Real.norm_of_nonneg (by positivity)]
  apply le_of_eq
  field_simp
  ring

theorem isLittleO_norm_rpow_add_one_of_fderiv_of_density_point_of_apply_eq_zero
   [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {f : E → F} {a : E} {r : ℝ}
    {μ : Measure E} [μ.IsAddHaarMeasure] {s : Set E}
    (hr : 0 ≤ r) (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x)
    (hderiv : fderiv ℝ f =O[𝓝 a] (‖· - a‖ ^ r)) (hs : ∀ᶠ x in 𝓝[s] a, fderiv ℝ f x = 0)
    (hmeas : Tendsto (fun r ↦ μ (s ∩ closedBall a r) / μ (closedBall a r)) (𝓝[>] 0) (𝓝 1))
    (hf₀ : f a = 0) :
    f =o[𝓝 a] (‖· - a‖ ^ (r + 1)) := by
  simpa [hf₀]
    using sub_isLittleO_norm_rpow_add_one_of_fderiv_of_density_point hr hdf hderiv hs hmeas
