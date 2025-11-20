import Mathlib
import SardMoreira.UpperLowerSemicontinuous

open scoped ENNReal NNReal Set.Notation
open MeasureTheory Filter Set Function Metric Topology

noncomputable instance : MeasureSpace ℝ≥0 where
  volume := .comap (↑) (volume : Measure ℝ)

@[simp]
theorem ENNReal.min_eq_zero_iff {a b : ℝ≥0∞} : min a b = 0 ↔ a = 0 ∨ b = 0 := min_eq_bot

theorem NNReal.volume_def : (volume : Measure ℝ≥0) = .comap (↑) (volume : Measure ℝ) := rfl

theorem MeasureTheory.Measure.comap_apply_le {α β : Type*} {_ : MeasurableSpace α}
    {_ : MeasurableSpace β} (f : α → β) (μ : Measure β) {s : Set α}
    (hs : NullMeasurableSet s (μ.comap f)) :
    μ.comap f s ≤ μ (f '' s) := by
  by_cases hf : Injective f ∧ ∀ t, MeasurableSet t → NullMeasurableSet (f '' t) μ
  · rw [comap_apply₀ _ _ hf.1 hf.2 hs]
  · rw [comap, dif_neg hf]
    simp

instance {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β} (μ : Measure β) (f : α → β)
    [IsFiniteMeasure μ] : IsFiniteMeasure (μ.comap f) where
  measure_univ_lt_top :=
    (Measure.comap_apply_le _ _ nullMeasurableSet_univ).trans_lt (measure_lt_top _ _)

protected def MeasureTheory.Measure.FiniteSpanningSetsIn.comap {α β : Type*}
    {_ : MeasurableSpace α} {_ : MeasurableSpace β} {μ : Measure β} {T : Set (Set β)}
    (sets : μ.FiniteSpanningSetsIn T) {S : Set (Set α)} {f : α → β} (hf : MapsTo (f ⁻¹' ·) T S)
    (hmeas : ∀ n, MeasurableSet (f ⁻¹' (sets.set n))) :
    (μ.comap f).FiniteSpanningSetsIn S where
  set n := f ⁻¹' (sets.set n)
  set_mem n := hf <| sets.set_mem n
  finite n := (Measure.comap_apply_le _ _ (hmeas n).nullMeasurableSet).trans_lt <|
    (measure_mono (image_preimage_subset _ _)).trans_lt <| sets.finite n
  spanning := by simp [← preimage_iUnion, sets.spanning]

protected theorem MeasureTheory.SigmaFinite.comap
    {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β} (μ : Measure β) {f : α → β}
    (hf : Measurable f) [SigmaFinite μ] : SigmaFinite (μ.comap f) :=
  ⟨⟨μ.toFiniteSpanningSetsIn.comap (mapsTo_univ _ _) fun n ↦
    hf <| μ.toFiniteSpanningSetsIn.set_mem n⟩⟩

instance : SigmaFinite (volume : Measure ℝ≥0) := .comap _ (by fun_prop)

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
  lowerSemicontinuous_measure_ball.measurable.comp (hf.prodMk hg)

theorem IsCompact.exists_isMinOn_measure_ball {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) {s : Set X}
    (hs : IsCompact s) (hne : s.Nonempty) (r : ℝ) : ∃ x ∈ s, IsMinOn (μ <| ball · r) s x :=
  ((lowerSemicontinuous_measure_ball.comp_continuous
    (continuous_id.prodMk continuous_const)).lowerSemicontinuousOn _).exists_isMinOn hs hne

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

theorem absolutelyContinuous_volumeIoiPow_left (n : ℕ) :
    .volumeIoiPow n ≪ .comap Subtype.val volume := by
  apply MeasureTheory.withDensity_absolutelyContinuous

protected theorem MeasureTheory.Measure.AbsolutelyContinuous.comap {α β : Type*}
    {_ : MeasurableSpace α} {_ : MeasurableSpace β} {μ ν : Measure β} (h : μ ≪ ν) (f : α → β)
    (hfν : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) ν) :
    μ.comap f ≪ ν.comap f := by
  by_cases hf : Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) ν
  · refine .mk fun s hsm hs ↦ ?_
    rw [Measure.comap_apply₀ _ _ hf.1] at *
    · exact h hs
    · exact hfν
    · exact hsm.nullMeasurableSet
    · exact fun t ht ↦ (hf.2 t ht).mono_ac h
    · exact hsm.nullMeasurableSet
  · rw [Measure.comap, dif_neg]
    · exact .zero _
    · contrapose! hf
      exact ⟨hf.1, hfν⟩

theorem MeasurableEmbedding.quasiMeasurePreserving_iff_comap {α β : Type*}
    {_ : MeasurableSpace α} {_ : MeasurableSpace β} {e : α → β} (he : MeasurableEmbedding e)
    {μ : Measure α} {ν : Measure β} :
    Measure.QuasiMeasurePreserving e μ ν ↔ μ ≪ .comap e ν := by
  constructor <;> intro h
  · rw [← he.comap_map μ]
    exact h.2.comap _ fun s hs ↦ (he.measurableSet_image.mpr hs).nullMeasurableSet
  · use he.measurable
    refine (h.map he.measurable).trans ?_
    rw [he.map_comap]
    exact ν.restrict_le_self.absolutelyContinuous

theorem MeasureTheory.Measure.QuasiMeasurePreserving.subtypeVal_volumeIoiPow (n : ℕ) :
    Measure.QuasiMeasurePreserving Subtype.val (.volumeIoiPow n) volume := by
  rw [MeasurableEmbedding.quasiMeasurePreserving_iff_comap]
  exacts [absolutelyContinuous_volumeIoiPow_left n, .subtype_coe measurableSet_Ioi]

theorem absolutelyContinuous_volumeIoiPow_right (n : ℕ) :
    .comap Subtype.val volume ≪ .volumeIoiPow n := by
  refine MeasureTheory.withDensity_absolutelyContinuous' ?_ <| .of_forall ?_
  · fun_prop
  · rintro ⟨x, hx : 0 < x⟩
    positivity

/-- If a finite measure `μ` is absolutely continuous with respect to a σ-finite measure `ν`,
then `μ s → 0` as `ν s → 0`. More precisely, for any `ε ≠ 0` there exists `δ > 0`
such that all sets of `ν` measure less than `δ` have a `μ` measure less than `ε`.
 -/
theorem MeasureTheory.Measure.AbsolutelyContinuous.exists_pos_forall_lt_imp_lt_of_isFiniteMeasure
    {α : Type*} {_ : MeasurableSpace α} {μ ν : Measure α} [IsFiniteMeasure μ]
    [μ.HaveLebesgueDecomposition ν]
    (h : μ ≪ ν) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ δ : ℝ≥0, δ > 0 ∧ ∀ s, ν s < δ → μ s < ε := by
  obtain ⟨φ, hφm, rfl⟩ : ∃ φ : α → ℝ≥0∞, Measurable φ ∧ μ = ν.withDensity φ := by
    refine ⟨μ.rnDeriv ν, by fun_prop, ?_⟩
    symm
    refine Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq.mp h
  have hφ : ∫⁻ x, φ x ∂ν ≠ ⊤ := by
    rw [← setLIntegral_univ, ← withDensity_apply _ .univ]
    apply measure_ne_top
  rcases exists_pos_setLIntegral_lt_of_measure_lt hφ hε with ⟨δ, hδ₀, hδ⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hδ₀ with ⟨δ', hδ'₀, hδ'⟩
  refine ⟨δ', mod_cast hδ'₀, fun s hs ↦ ?_⟩
  calc
    ν.withDensity φ s ≤ ν.withDensity φ (toMeasurable ν s) := by gcongr; apply subset_toMeasurable
    _ = ∫⁻ a in toMeasurable ν s, φ a ∂ν := withDensity_apply _ (measurableSet_toMeasurable _ _)
    _ < ε := by
      apply hδ
      rw [measure_toMeasurable]
      exact hs.trans hδ'

/--
The previous lemma is not true unless we assume that `ν` is a finite measure.
Indeed, for `ν = volume` on `ℝ`, `μ = ν.withDensity (Real.nnabs ·)`,
we can choose `s = Set.Icc a (a + δ / 2)` for a large `a`,
and get an arbitriraly large value of `μ s`.
-/
theorem exists_absolutelyContinuous_forall_pos_exists_lt_gt :
    ∃ μ ν : Measure ℝ, μ ≪ ν ∧ ∀ C δ : ℝ≥0, δ ≠ 0 →
      ∃ s, MeasurableSet s ∧ ν s < δ ∧ μ s > C := by
  -- Define the measures μ and ν as described.
  use MeasureTheory.volume.withDensity (‖·‖ₑ), MeasureTheory.volume
  constructor
  · exact withDensity_absolutelyContinuous volume fun x ↦ ↑(Real.nnabs x);
  · intro C δ hδ
    -- Choose $a > 0$ large enough such that $a * δ / 2 > C$.
    obtain ⟨a, ha₀, ha⟩ : ∃ a : ℝ≥0, a > 0 ∧ a * δ / 2 > C := by
      rcases exists_pos_lt_mul (show 0 < (δ / 2 : ℝ) by positivity) C with ⟨a, ha₀, ha⟩
      lift a to ℝ≥0 using ha₀.le
      exact ⟨a, ha₀, by norm_cast at ha; rwa [mul_div_assoc]⟩
    refine ⟨ Set.Icc a ( a + δ / 2 ), measurableSet_Icc, ?_, ?_ ⟩
    · rw [Real.volume_Icc, add_sub_cancel_left]
      norm_cast
      rw [ENNReal.ofReal_coe_nnreal]
      norm_cast
      exact NNReal.half_lt_self hδ
    · calc
        (C : ℝ≥0∞) < a * δ / 2 := by
          rw [gt_iff_lt, ← ENNReal.coe_lt_coe, ENNReal.coe_div (by simp)] at ha
          exact mod_cast ha
        _ = a * volume (Icc (a : ℝ) (a + δ / 2)) := by
          simp [ENNReal.ofReal_div_of_pos, mul_div_assoc]
        _ ≤ _ := by
          rw [withDensity_apply _ measurableSet_Icc, ← setLIntegral_const]
          refine setLIntegral_mono measurable_enorm ?_
          rintro x ⟨hx, -⟩
          simpa [← NNReal.coe_le_coe] using hx.trans (le_abs_self x)

/-- If a finite measure `μ` is absolutely continuous with respect to a σ-finite measure `ν`,
then `μ s → 0` as `ν s → 0`. More precisely, for any `ε ≠ 0` there exists `δ > 0`
such that all sets of `ν` measure less than `δ` have a `μ` measure less than `ε`.
 -/
theorem MeasureTheory.Measure.AbsolutelyContinuous.exists_pos_forall_subset_lt_imp_lt
    {α : Type*} {_ : MeasurableSpace α} {μ ν : Measure α} [SigmaFinite ν]
    (h : μ ≪ ν) {t : Set α} (ht : μ t ≠ ⊤) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ δ : ℝ≥0, δ > 0 ∧ ∀ s ⊆ t, ν s < δ → μ s < ε := by
  have := Fact.mk ht.lt_top
  have : μ.restrict t ≪ ν := .trans μ.restrict_le_self.absolutelyContinuous h
  rcases this.exists_pos_forall_lt_imp_lt_of_isFiniteMeasure hε with ⟨δ, hδ₀, hδ⟩
  refine ⟨δ, hδ₀, fun s hst hs ↦ ?_⟩
  simpa only [Measure.restrict_eq_self _ hst] using hδ s hs

theorem MeasureTheory.Measure.AbsolutelyContinuous.exists_pos_forall_lt_imp_lt
    {α : Type*} {_ : MeasurableSpace α} {μ ν : Measure α} [SigmaFinite ν]
    (h : μ ≪ ν) {ε : ℝ≥0∞} (hε : ε ≠ 0)
    (hrnDeriv : ∃ C : ℝ≥0, μ.rnDeriv ν ≤ᶠ[μ.cofinite] fun _ ↦ C)  :
    ∃ δ : ℝ≥0, δ > 0 ∧ ∀ s, ν s < δ → μ s < ε := by
  rcases hrnDeriv with ⟨C, hC⟩
  simp only [Filter.EventuallyLE, Measure.eventually_cofinite, not_le] at hC
  rcases h.exists_pos_forall_subset_lt_imp_lt hC.ne (ENNReal.half_pos hε).ne' with ⟨δ', hδ'₀, hδ'⟩
  obtain ⟨δ, hδ₀, hδδ', hδε⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ δ' ∧ C * δ < ε / 2 := by
    have : min 1 (ε / 2 / C) ≠ ⊤ := by simp
    refine ⟨min δ' (min 1 (ε / 2 / C)).toNNReal, ?_, min_le_left _ _, ?_⟩
    · apply lt_min hδ'₀
      apply ENNReal.toNNReal_pos
      · simp [hε]
      · exact this
    · push_cast [ENNReal.coe_toNNReal this]
      sorry
  sorry

/-- Let `μ` be a Haar measure on a finite dimensional real normed space.
Then for any positive `ε` there exists a positive `δ`
 -/
theorem exists_pos_forall_measure_le_toSphere_ge_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {_ : MeasurableSpace E} [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ s ⊆ Metric.ball (0 : E) 1, μ s ≤ δ →
      μ.toSphere {x | volume {t : ℝ | 0 ≤ t ∧ t • x.1 ∈ s} ≥ ε} ≤ ε := by
  nontriviality E using exists_gt
  cases ε with | top => simp [exists_gt] | coe ε => ?_
  norm_cast at hε
  set t := Ioi (0 : ℝ) ↓∩ Iio 1
  have ht : volume.comap Subtype.val t ≠ ⊤ := by
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioi).comap_preimage, Subtype.range_val,
      Iio_inter_Ioi, Real.volume_Ioo]
    simp
  rcases absolutelyContinuous_volumeIoiPow_right (Module.finrank ℝ E - 1)
    |>.exists_pos_forall_subset_lt_imp_lt ht (ε := ε) (mod_cast hε)
    with ⟨δ, hδ₀, hδ⟩
  replace hδ : ∀ s ⊆ Ico (0 : ℝ) 1,
      Measure.volumeIoiPow (Module.finrank ℝ E - 1) (Ioi (0 : ℝ) ↓∩ s) < ↑δ → volume s < ε := by
    intro s hs hsδ
    refine lt_of_le_of_lt ?_
      (hδ (Ioi (0 : ℝ) ↓∩ s) (preimage_mono <| hs.trans Ico_subset_Iio_self) hsδ)
    rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioi).comap_preimage, Subtype.range_val]
    apply measure_mono_ae
    filter_upwards [Ioi_ae_eq_Ici.symm.le] with a ha hsa using ⟨hsa, ha (hs hsa).1⟩
  set T : Set E → Set (Metric.sphere (0 : E) 1) := fun s ↦
    {x | Measure.volumeIoiPow (Module.finrank ℝ E - 1)
      {t : Ioi (0 : ℝ) | ((homeomorphUnitSphereProd E).symm (x, t)).1 ∈ s} ≥ δ}
  have hT : ∀ s ⊆ ball (0 : E) 1,
      μ.toSphere {x | volume {t : ℝ | 0 ≤ t ∧ t • x.1 ∈ s} ≥ ε} ≤ μ.toSphere (T s)  := by
    refine fun s hs ↦ measure_mono fun x hx ↦ ?_
    simp only [T]
    rw [mem_setOf_eq] at hx ⊢
    contrapose! hx
    apply hδ
    · refine fun t ⟨ht₀, ht⟩ ↦ ⟨ht₀, ?_⟩
      replace ht := hs ht
      simpa [norm_smul, abs_of_nonneg ht₀] using ht
    · convert hx
      ext t
      simp [t.2.out.le]
  refine ⟨ε * δ, by positivity, ?_⟩
  intro s hs hμs
  wlog hsm : MeasurableSet s generalizing s
  · refine le_trans ?_ (this (toMeasurable μ s ∩ ball 0 1) inter_subset_right ?_ ?_)
    · refine measure_mono fun x hx ↦ ?_
      rw [mem_setOf_eq] at hx ⊢
      exact le_trans hx <| measure_mono fun t ⟨ht₀, ht⟩ ↦ ⟨ht₀, subset_toMeasurable _ _ ht, hs ht⟩
    · rw [Measure.measure_toMeasurable_inter_of_sFinite measurableSet_ball]
      exact (measure_mono inter_subset_left).trans hμs
    · measurability
  refine (hT s hs).trans ?_
  contrapose! hμs
  push_cast
  calc
    (ε * δ : ℝ≥0∞) < μ.toSphere (T s) * δ := by
      gcongr
      simp
    _ ≤ μ.comap (↑) ({(0 : E)}ᶜ ↓∩ s) := by
      have := μ.measurePreserving_homeomorphUnitSphereProd
      rw [← Homeomorph.toMeasurableEquiv_coe] at this
      rw [← this.symm.measure_preimage_emb (MeasurableEquiv.measurableEmbedding _),
        Measure.prod_apply, mul_comm, ← setLIntegral_const]
      · refine (setLIntegral_mono ?_ ?_).trans (setLIntegral_le_lintegral _ _)
        · apply measurable_measure_prodMk_left
          refine MeasurableEquiv.measurable _ ?_
          exact hsm.preimage measurable_subtype_coe
        · intro x hx
          simpa [T] using hx
      · refine MeasurableEquiv.measurable _ ?_
        exact hsm.preimage measurable_subtype_coe
    _ ≤ μ s := by
      rw [(MeasurableEmbedding.subtype_coe <| by measurability).comap_preimage]
      exact measure_mono inter_subset_left

theorem aux₁ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    [FiniteDimensional ℝ E]
    {_ : MeasurableSpace E} [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ s ⊆ Metric.ball (0 : E) 1, μ s ≤ δ →
      ∀ x ∈ Metric.sphere (0 : E) 1, ∃ y ∈ Metric.sphere (0 : E) 1,
        dist y x ≤ ε ∧ volume {t ∈ Ioo (0 : ℝ) 1 | AffineMap.lineMap 0 x t ∈ s} ≤ ε := by
  admit

/-- If $s_b$ is a family of sets such that $\{(a, b) \mid a \in s_b\}$ is a measurable set,
then for any s-finite measure $\mu$, the function $b \mapsto \mu(s_b)$ is measurable.

This is a version of `measurable_measure_prod_mk_right`. -/
theorem Measurable.measure_apply {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (s : β → Set α) (hs : MeasurableSet {p : α × β | p.1 ∈ s p.2}) :
    Measurable fun b ↦ μ (s b) :=
  measurable_measure_prodMk_right hs

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

/-- Let `e : X → Y` be a dense topological embedding, let `Z` be a regular space.
For each `y : Y`, let `U y` be an open set such that `y ∈ closure (U y)`.

Let `s` be an open set, let `x : X` be a point.
Suppose that `f : Y → Z` is continuous within `U y` at all `y ∈ s` close to `e x`.
Then `f (e x')` tends to `z` as `x'` tends to `x`, `e x' ∈ s`,
if and only if `f y` tends to `z` as `y ∈ s` tends to `e x`.

If `X = ℚ`, `Y = ℝ`, and `e = Rat.cast`,
then this lemma can be used to restate convergence of a function defined on real numbers
in terms of convergence of a function on rational numbers,
which is more convenient for measure theory, because there are only countably many rational numbers.
-/
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
-- UPD: I'm not sure if they're true without `SecondCountableTopology` assumption,
-- even for simple functions.
theorem MeasurableSet.setOf_tendsto_measure_sectl_inter_closedBall_div
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {α : Type*} [MeasurableSpace α]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [SFinite μ]
    {s : Set (X × α)} (hs : MeasurableSet s) {f : X × α → ℝ≥0∞} (hf : Measurable f) :
    MeasurableSet {p : X × α |
      Tendsto (fun r : ℝ ↦ μ ((·, p.2) ⁻¹' s ∩ closedBall p.1 r) / μ (closedBall p.1 r)) (𝓝[>] 0)
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
  exact .inter (hs.preimage <| .prodMk measurable_fst measurable_snd.snd) this

theorem MeasurableSet.setOf_tendsto_measure_inter_closedBall_div
    {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [SFinite μ]
    {s : Set X} (hs : MeasurableSet s) {f : X → ℝ≥0∞} (hf : Measurable f) :
    MeasurableSet {x : X |
      Tendsto (fun r ↦ μ (s ∩ closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 (f x))} := by
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
