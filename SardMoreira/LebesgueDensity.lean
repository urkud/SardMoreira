import Mathlib

open scoped Topology ENNReal
open MeasureTheory Filter Set Function Metric

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

theorem forall_lt_le_iff {α : Type*} [LinearOrder α] [DenselyOrdered α] {a b : α} :
    (∀ c < a, c ≤ b) ↔ a ≤ b :=
  ⟨le_of_forall_ge_of_dense, fun hab _c hca ↦ hca.le.trans hab⟩

theorem forall_gt_ge_iff {α : Type*} [LinearOrder α] [DenselyOrdered α] {a b : α} :
    (∀ c, a < c → b ≤ c) ↔ b ≤ a :=
  forall_lt_le_iff (α := αᵒᵈ)

theorem Metric.biInter_lt_closedBall {X : Type*} [PseudoMetricSpace X] (x : X) (r : ℝ) :
    ⋂ r' > r, closedBall x r' = closedBall x r := by
  ext
  simp [forall_gt_ge_iff]

theorem eventually_forall_le_continuousWithinAt_Ici_measure_closedBall
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] (x : X) :
    ∀ᶠ r : ℝ in 𝓝 0, ∀ ν ≤ μ, ContinuousWithinAt (ν <| closedBall x ·) (Set.Ici r) r := by
  rcases (μ.finiteAt_nhds x).exists_mem_basis nhds_basis_closedBall with ⟨ε, ε₀, hε⟩
  filter_upwards [eventually_lt_nhds ε₀] with r hr ν hν
  rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
  convert tendsto_measure_biInter_gt (by measurability) (by intros; gcongr)
    ⟨ε, hr, ((hν _).trans_lt hε).ne⟩
  rw [biInter_lt_closedBall]

theorem eventually_continuousWithinAt_Ici_measure_inter_closedBall_div
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] (x : X) {s : Set X} (hs : NullMeasurableSet s μ) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      ContinuousWithinAt (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r)) (Set.Ici r) r := by
  by_cases hpos : ∃ ε > 0, μ (closedBall x r) = 0
  

theorem tendsto_measure_inter_closedBall_div_iff_rat
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsLocallyFiniteMeasure μ] {x : X} {a : ℝ≥0∞} {s : Set X} :
    Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 a) ↔
      Tendsto (fun r : ℚ ↦ μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 a) := by
  -- TODO split the proof into reusable lemmas.
  refine ⟨fun h ↦ h.comp ?_, fun h ↦ ?_⟩
  · rw [← Rat.cast_zero (α := ℝ)]
    refine Rat.continuous_coe_real.continuousWithinAt.tendsto_nhdsWithin fun r hr ↦ ?_
    simpa
  · rw [(closed_nhds_basis a).tendsto_right_iff]
    rintro U ⟨hU, hUc⟩
    rw [(nhdsWithin_Ioi_basis _).tendsto_left_iff] at h
    rcases h U hU with ⟨ε, hε₀, hε⟩
    rcases (μ.finiteAt_nhds x).exists_mem_basis nhds_basis_closedBall with ⟨ε', hε₀', hε'⟩
    filter_upwards [Ioo_mem_nhdsWithin_Ioi' (b := (ε : ℝ)) (mod_cast hε₀),
      Ioo_mem_nhdsWithin_Ioi' hε₀'] with δ hδ₁ hδ₂
    
    

theorem MeasurableSet.setOf_tendsto_measure_sectl_inter_closedBall_div
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {α : Type*} [MeasurableSpace α]
    (μ : Measure X) {s : Set (X × α)} (hs : MeasurableSet s) :
    MeasurableSet {p : X × α |
      Tendsto (fun r : ℝ ↦ μ ((·, p.2) ⁻¹' s  ∩ closedBall p.1 r) / μ (closedBall p.1 r)) (𝓝[>] 0)
        (𝓝 (s.indicator 1 p))} := by
  
  sorry
