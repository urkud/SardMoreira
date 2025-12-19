import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.LowerUpperTopology

open MeasureTheory Topology Filter Set Metric
open scoped NNReal

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
  simp only [Semicontinuous, Prod.forall, WithUpper.toUpper.surjective.forall,
    SemicontinuousAt, Equiv.symm_apply_apply]
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
  lowerSemicontinuous_measure_ball_toUpper_symm.comp <|
    continuous_id.prodMap WithUpper.continuous_toUpper

@[fun_prop]
theorem Measurable.measure_ball {α X : Type*} {_ : MeasurableSpace α}
    [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X}
    {f : α → X} {g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a ↦ μ (ball (f a) (g a))) :=
  lowerSemicontinuous_measure_ball.measurable.comp (hf.prodMk hg)

theorem IsCompact.exists_isMinOn_measure_ball {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) {s : Set X}
    (hs : IsCompact s) (hne : s.Nonempty) (r : ℝ) : ∃ x ∈ s, IsMinOn (μ <| ball · r) s x :=
  ((lowerSemicontinuous_measure_ball.comp
    (continuous_id.prodMk continuous_const)).lowerSemicontinuousOn _).exists_isMinOn hne hs

theorem IsCompact.exists_pos_forall_lt_measure_ball {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure] {s : Set X}
    (hs : IsCompact s) {r : ℝ} (hr : 0 < r) : ∃ m > (0 : ℝ≥0), ∀ x ∈ s, m < μ (ball x r) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · use 1
    simp
  · rcases hs.exists_isMinOn_measure_ball μ hne r with ⟨x, hxs, hx⟩
    rcases ENNReal.lt_iff_exists_nnreal_btwn.mp (Metric.measure_ball_pos μ x hr) with ⟨m, hm₀, hmx⟩
    exact ⟨m, mod_cast hm₀, fun y hy ↦ hmx.trans_le <| hx hy⟩

theorem exists_pos_forall_lt_measure_ball {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    {r : ℝ} (hr : 0 < r) : ∃ m > (0 : ℝ≥0), ∀ x, m < μ (ball x r) := by
  simpa using isCompact_univ.exists_pos_forall_lt_measure_ball μ hr
