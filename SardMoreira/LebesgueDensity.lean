import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Order.LowerUpperTopology
import SardMoreira.UpperLowerSemicontinuous

open scoped ENNReal
open MeasureTheory Filter Set Function Metric Topology

theorem MeasureTheory.tendsto_measure_biUnion_lt {α : Type*} {m : MeasurableSpace α}
    {μ : Measure α} {ι : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
    [DenselyOrdered ι] [FirstCountableTopology ι] {s : ι → Set α} {a : ι}
    (hm : ∀ i j, i ≤ j → j < a → s i ⊆ s j) :
    Tendsto (μ ∘ s) (𝓝[<] a) (𝓝 (μ (⋃ i < a, s i))) := by
  have : (atTop : Filter (Iio a)).IsCountablyGenerated := by
    rw [← comap_coe_Iio_nhdsLT]
    infer_instance
  simp_rw [← map_coe_Iio_atTop, tendsto_map'_iff, ← mem_Iio, biUnion_eq_iUnion]
  exact tendsto_measure_iUnion_atTop fun i j hle ↦ hm i j hle j.2

theorem continuousWithinAt_Iio_measure_ball {X : Type*} [PseudoMetricSpace X]
    {_ : MeasurableSpace X} {μ : Measure X} {x : X} {r : ℝ} :
    ContinuousWithinAt (μ <| ball x ·) (Iio r) r := by
  rw [ContinuousWithinAt, ← biUnion_lt_ball]
  exact tendsto_measure_biUnion_lt fun i j hle _ ↦ by gcongr

theorem continuousWithinAt_Iic_measure_ball {X : Type*} [PseudoMetricSpace X]
    {_ : MeasurableSpace X} {μ : Measure X} {x : X} {r : ℝ} :
    ContinuousWithinAt (μ <| ball x ·) (Iic r) r :=
  continuousWithinAt_Iio_iff_Iic.mp continuousWithinAt_Iio_measure_ball

theorem lowerSemicontinuous_measure_ball_toUpper_symm {X : Type*} [PseudoMetricSpace X]
    {_ : MeasurableSpace X} {μ : Measure X} :
    LowerSemicontinuous fun xr : X × WithUpper ℝ ↦ μ (ball xr.1 (WithUpper.toUpper.symm xr.2)) := by
  simp only [LowerSemicontinuous, Prod.forall, WithUpper.toUpper.surjective.forall,
    LowerSemicontinuousAt, Equiv.symm_apply_apply]
  intro x r m hm
  obtain ⟨r₁, hr₁, hmr₁⟩ : ∃ r₁ < r, m < μ (ball x r₁) :=
    (eventually_mem_nhdsWithin.and
      (continuousWithinAt_Iio_measure_ball.eventually_const_lt hm)).exists
  obtain ⟨r₂, hr₁r₂, hr₂r⟩ : ∃ r₂, r₁ < r₂ ∧ r₂ < r := exists_between hr₁
  have H : ∀ᶠ xr : X × WithUpper ℝ in 𝓝 (x, WithUpper.toUpper r),
      xr.1 ∈ ball x (r₂ - r₁) ∧ r₂ < WithUpper.toUpper.symm xr.2 :=
    prod_mem_nhds (ball_mem_nhds _ (sub_pos.2 hr₁r₂)) (eventually_gt_nhds hr₂r)
  refine H.mono ?_
  simp only [Prod.forall, WithUpper.toUpper.surjective.forall, Equiv.symm_apply_apply, mem_ball]
  rintro y r' ⟨hy, hr'⟩
  refine hmr₁.trans_le <| measure_mono <| ball_subset_ball' ?_
  rw [dist_comm]
  linarith

theorem lowerSemicontinuous_measure_ball {X : Type*} [PseudoMetricSpace X]
    {_ : MeasurableSpace X} {μ : Measure X} :
    LowerSemicontinuous fun xr : X × ℝ ↦ μ (ball xr.1 xr.2) :=
  lowerSemicontinuous_measure_ball_toUpper_symm.comp_continuous <|
    continuous_id.prodMap WithUpper.continuous_toUpper

@[fun_prop]
theorem Measurable.measure_ball {α X : Type*} {_ : MeasurableSpace α}
    [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X}
    {f : α → X} {g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a ↦ μ (ball (f a) (g a))) :=
  lowerSemicontinuous_measure_ball.measurable.comp (hf.prod_mk hg)

theorem IsCompact.exists_isMinOn_measure_ball {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) {s : Set X}
    (hs : IsCompact s) (hne : s.Nonempty) (r : ℝ) : ∃ x ∈ s, IsMinOn (μ <| ball · r) s x :=
  ((lowerSemicontinuous_measure_ball.comp_continuous
    (continuous_id.prod_mk continuous_const)).lowerSemicontinuousOn _).exists_isMinOn hs hne

theorem IsCompact.exists_pos_forall_lt_measure_ball {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure] {s : Set X}
    (hs : IsCompact s) {r : ℝ} (hr : 0 < r) : ∃ m > 0, ∀ x ∈ s, m < μ (ball x r) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · use 1
    simp
  · rcases hs.exists_isMinOn_measure_ball μ hne r with ⟨x, hxs, hx⟩
    rcases exists_between (Metric.measure_ball_pos μ x hr) with ⟨m, hm₀, hmx⟩
    exact ⟨m, hm₀, fun y hy ↦ hmx.trans_le <| hx hy⟩

theorem exists_pos_forall_lt_measure_ball {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    {r : ℝ} (hr : 0 < r) : ∃ m > 0, ∀ x, m < μ (ball x r) := by
  simpa using isCompact_univ.exists_pos_forall_lt_measure_ball μ hr

/-- If $s_b$ is a family of sets such that $\{(a, b) \mid a \in s_b\}$ is a measurable set,
then for any s-finite measure $\mu$, the function $b \mapsto \mu(s_b)$ is measurable.

This is a version of `measurable_measure_prod_mk_right`. -/
theorem Measurable.measure_apply {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (s : β → Set α) (hs : MeasurableSet {p : α × β | p.1 ∈ s p.2}) :
    Measurable fun b ↦ μ (s b) :=
  measurable_measure_prod_mk_right hs

theorem Metric.biInter_lt_rat_closedBall {X : Type*} [PseudoMetricSpace X] (x : X) (r : ℝ) :
    closedBall x r = ⋂ (q : ℚ) (_ : r < q), closedBall x q := by
  ext
  simpa only [mem_iInter₂, mem_closedBall] using le_iff_forall_lt_rat_imp_le

theorem eventually_measure_closedBall_lt_top
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] (x : X) :
    ∀ᶠ r in 𝓝 0, μ (closedBall x r) < ⊤ := by
  rcases (μ.finiteAt_nhds x).exists_mem_basis nhds_basis_closedBall with ⟨ε, ε₀, hε⟩
  exact (eventually_lt_nhds ε₀).mono fun r hr ↦ lt_of_le_of_lt (by gcongr) hε

theorem eventually_forall_le_continuousWithinAt_Ici_measure_closedBall
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] (x : X) :
    ∀ᶠ r : ℝ in 𝓝 0, ∀ ν ≤ μ, ContinuousWithinAt (ν <| closedBall x ·) (Set.Ici r) r := by
  rcases (μ.finiteAt_nhds x).exists_mem_basis nhds_basis_closedBall with ⟨ε, ε₀, hε⟩
  filter_upwards [eventually_lt_nhds ε₀] with r hr ν hν
  rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
  convert tendsto_measure_biInter_gt (by measurability) (by intros; gcongr)
    ⟨ε, hr, ((hν _).trans_lt hε).ne⟩
  rw [biInter_gt_closedBall]

theorem eventually_continuousWithinAt_Ici_measure_inter_closedBall_div
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsLocallyFiniteMeasure μ] (x : X) {s : Set X} (hs : NullMeasurableSet s μ) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      ContinuousWithinAt (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r)) (Set.Ici r) r := by
  by_cases h₀ : ∃ ε > 0, μ (closedBall x ε) = 0
  case pos =>
    rcases h₀ with ⟨ε, ε₀, hε⟩
    filter_upwards [Ioo_mem_nhdsGT ε₀] with r hr
    refine (continuousAt_const.congr (f := 0) ?_).continuousWithinAt
    filter_upwards [eventually_lt_nhds hr.2] with r' hr'
    rw [measure_mono_null _ hε, ENNReal.zero_div, Pi.zero_apply]
    exact inter_subset_right.trans (by gcongr)
  case neg =>
    rw [eventually_nhdsWithin_iff]
    filter_upwards [eventually_measure_closedBall_lt_top μ x,
      eventually_forall_le_continuousWithinAt_Ici_measure_closedBall μ x] with r hr₁ hr₂ hr₀
    refine ENNReal.Tendsto.div ?_ (by simp_all) (hr₂ _ le_rfl) (.inl hr₁.ne)
    simp only [inter_comm s, ← Measure.restrict_apply₀' hs]
    exact hr₂ _ Measure.restrict_le_self

theorem eventually_nhdsWithin_nhds {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U)
    {p : X → Prop} {x : X} :
    (∀ᶠ y in 𝓝[U] x, ∀ᶠ z in 𝓝 y, p z) ↔ ∀ᶠ y in 𝓝[U] x, p y := by
  conv_rhs => rw [← eventually_eventually_nhdsWithin]
  refine eventually_congr <| eventually_mem_nhdsWithin.mono fun y hy ↦ ?_
  rw [hU.nhdsWithin_eq hy]

theorem IsDenseEmbedding.tendsto_nhdsWithin_preimage_iff_of_eventually_continuousWithinAt
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [RegularSpace Z]
    {e : X → Y} {s : Set Y} {x : X} {z : Z} {f : Y → Z} {U : Y → Set Y} [∀ y, (𝓝[U y] y).NeBot]
    (he : IsDenseEmbedding e) (hs : IsOpen s) (hU : ∀ y, IsOpen (U y))
    (hcont : ∀ᶠ y in 𝓝[s] (e x), ContinuousWithinAt f (U y) y) :
    Tendsto (f ∘ e) (𝓝[e ⁻¹' s] x) (𝓝 z) ↔ Tendsto f (𝓝[s] (e x)) (𝓝 z) := by
  refine ⟨fun h ↦ ?mp, fun h ↦ h.comp ?mpr⟩
  case mpr =>
    exact he.continuous.continuousWithinAt.tendsto_nhdsWithin (mapsTo_preimage _ _)
  case mp =>
    rw [(closed_nhds_basis z).tendsto_right_iff]
    rintro V ⟨hV, hVc⟩
    rw [← tendsto_map'_iff, he.isEmbedding.map_nhdsWithin_eq, image_preimage_eq_inter_range] at h
    replace h := h.eventually (eventually_mem_set.mpr hV)
    rw [nhdsWithin_inter', eventually_inf_principal, ← eventually_nhdsWithin_nhds hs] at h
    filter_upwards [hcont, h] with y hy₁ hy₂
    refine hVc.mem_of_frequently_of_tendsto ?_ hy₁
    refine .mp ?_ (eventually_nhdsWithin_of_eventually_nhds hy₂)
    rw [(nhdsWithin_basis_open _ _).frequently_iff]
    rintro W ⟨hyW, hWo⟩
    simp only [mem_inter_iff, @and_comm _ (_ ∈ range e), exists_range_iff]
    apply he.dense.exists_mem_open (hWo.inter (hU y))
    rw [inter_comm]
    exact nonempty_of_mem <| inter_mem_nhdsWithin _ (hWo.mem_nhds hyW)

theorem tendsto_measure_inter_closedBall_div_iff_rat
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsLocallyFiniteMeasure μ] {x : X} {a : ℝ≥0∞} {s : Set X}
    (hs : NullMeasurableSet s μ) :
    Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 a) ↔
      Tendsto (fun r : ℚ ↦ μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 a) := by
  rw [← Rat.cast_zero (α := ℝ), ← Rat.preimage_cast_Ioi (K := ℝ),
    ← Rat.isDenseEmbedding_coe_real.tendsto_nhdsWithin_preimage_iff_of_eventually_continuousWithinAt
      (U := Ioi), comp_def]
  · exact isOpen_Ioi
  · exact fun _ ↦ isOpen_Ioi
  · simp only [Rat.cast_zero, continuousWithinAt_Ioi_iff_Ici]
    exact eventually_continuousWithinAt_Ici_measure_inter_closedBall_div _ hs

-- The next 2 lemmas depend on Polish spaces,
-- because they are formulated for a measurable `f`.
-- However, we always apply them to simple functions.
-- We may decide to reformulate in order to reduce dependencies.
theorem MeasurableSet.setOf_tendsto_measure_sectl_inter_closedBall_div
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {α : Type*} [MeasurableSpace α]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [SFinite μ]
    {s : Set (X × α)} (hs : MeasurableSet s) {f : X × α → ℝ≥0∞} (hf : Measurable f) :
    MeasurableSet {p : X × α |
      Tendsto (fun r : ℝ ↦ μ ((·, p.2) ⁻¹' s  ∩ closedBall p.1 r) / μ (closedBall p.1 r)) (𝓝[>] 0)
        (𝓝 (f p))} := by
  have hm : ∀ {a}, MeasurableSet ((·, a) ⁻¹' s) := hs.preimage (by measurability)
  simp only [tendsto_measure_inter_closedBall_div_iff_rat hm.nullMeasurableSet]
  have {q} : MeasurableSet {p : X × X × α | p.1 ∈ closedBall p.2.1 q} := by
    simp only [mem_closedBall]
    apply measurableSet_le
    · exact measurable_fst.dist measurable_snd.fst
    · exact measurable_const
  refine measurableSet_tendsto_fun (fun q ↦ .div ?_ (.measure_apply μ _ this)) hf
  refine .measure_apply _ _ ?_
  exact .inter (hs.preimage <| .prod_mk measurable_fst measurable_snd.snd) this

theorem MeasurableSet.setOf_tendsto_measure_inter_closedBall_div
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [SFinite μ]
    {s : Set X} (hs : MeasurableSet s) {f : X → ℝ≥0∞} (hf : Measurable f) :
    MeasurableSet {x : X |
      Tendsto (fun r ↦ μ (s  ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 (f x))} := by
  -- Another option is to apply the previous lemma to the product with `univ : Set Unit`,
  -- but repeating the proof is shorter in this case.
  simp only [tendsto_measure_inter_closedBall_div_iff_rat hs.nullMeasurableSet]
  have H {q} : MeasurableSet {p : X × X | p.1 ∈ closedBall p.2 q} :=
    measurableSet_le (measurable_fst.dist measurable_snd) measurable_const
  refine measurableSet_tendsto_fun (fun q ↦ .div (.measure_apply μ _ ?_) (.measure_apply μ _ H)) hf
  exact .inter (hs.preimage measurable_fst) H

/-- Parametrized version of `ae_tendsto_measure_inter_div_of_measurableSet`. -/
theorem Besicovitch.ae_tendsto_measure_sectl_inter_closedBall_div
    {X : Type*} [MetricSpace X] [SecondCountableTopology X] [HasBesicovitchCovering X]
    [MeasurableSpace X] [BorelSpace X]
    {α : Type*} [MeasurableSpace α]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [SFinite μ] (ν : Measure α) [SFinite ν]
    {s : Set (X × α)} (hs : MeasurableSet s) :
    ∀ᵐ p ∂μ.prod ν, Tendsto (fun r ↦ μ ((·, p.2) ⁻¹' s  ∩ closedBall p.1 r) / μ (closedBall p.1 r))
      (𝓝[>] 0) (𝓝 (s.indicator 1 p)) := by
  have H := hs.setOf_tendsto_measure_sectl_inter_closedBall_div μ <|
    (measurable_const (a := 1)).indicator hs
  rw [Measure.ae_prod_iff_ae_ae, Measure.ae_ae_comm] <;> try exact H
  refine .of_forall fun y ↦ ae_tendsto_measure_inter_div_of_measurableSet μ <| hs.preimage ?_
  measurability
