import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib
import SardMoreira.UnifDoublingCover

namespace MeasureTheory.Measure

open scoped ENNReal NNReal Topology
open Metric Set Filter Fin MeasureTheory TopologicalSpace Besicovitch.TauPackage

attribute [norm_cast] ENNReal.ofReal_coe_nnreal

theorem EMetric.diam_metricClosedBall_le {X : Type*} [PseudoMetricSpace X]
    (x : X) (r : ℝ) : EMetric.diam (Metric.closedBall x r) ≤ 2 * ENNReal.ofReal r := by
  rcases lt_or_ge r 0 with hr | hr
  · simp [ENNReal.ofReal_of_nonpos hr.le, Metric.closedBall_of_neg hr]
  lift r to ℝ≥0 using hr
  grw [← Metric.emetric_closedBall_nnreal, EMetric.diam_closedBall, ENNReal.ofReal_coe_nnreal]

universe u

variable {α : Type*} [MetricSpace α] {β : Type u} [MeasurableSpace α]

class ClosedBallCoveringMeasure {α : Type*} [MetricSpace α] [MeasurableSpace α]
    (μ : Measure α) : Prop where
  exists_closedBall_covering_tsum_measure_le {ε : ℝ≥0∞} (hε : ε ≠ 0) (f : α → Set ℝ) (s : Set α)
    (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty) :
    ∃ (t : Set α) (r : α → ℝ), t.Countable ∧ t ⊆ s ∧ (∀ x ∈ t, r x ∈ f x) ∧
      (s ⊆ ⋃ x ∈ t, closedBall x (r x)) ∧ (∑' x : t, μ (closedBall x (r x))) ≤ μ s + ε

theorem exists_closedBall_covering_tsum_measure_le (μ : Measure α) [ClosedBallCoveringMeasure μ]
    {ε : ℝ≥0∞} (hε : ε ≠ 0) (f : α → Set ℝ) (s : Set α)
    (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty) :
    ∃ (t : Set α) (r : α → ℝ), t.Countable ∧ t ⊆ s ∧ (∀ x ∈ t, r x ∈ f x) ∧
      (s ⊆ ⋃ x ∈ t, closedBall x (r x)) ∧ (∑' x : t, μ (closedBall x (r x))) ≤ μ s + ε :=
  ClosedBallCoveringMeasure.exists_closedBall_covering_tsum_measure_le hε f s hf

instance [SecondCountableTopology α] [OpensMeasurableSpace α] [HasBesicovitchCovering α]
    (μ : Measure α) [SFinite μ] [μ.OuterRegular] : ClosedBallCoveringMeasure μ :=
  ⟨Besicovitch.exists_closedBall_covering_tsum_measure_le μ⟩

open IsUnifLocDoublingMeasure in
instance instClosedBallCoveringMeasureOfIsUnifLocDoublingMeasure [BorelSpace α] [SecondCountableTopology α]
    (μ : Measure α) [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ] :
    ClosedBallCoveringMeasure μ where
  exists_closedBall_covering_tsum_measure_le := by
    intro ε hε₀ f s hf
    -- TODO: we do all the same steps for the Besicovitch instance in Mathlib.
    -- Factor out common parts into a constructor.
    rcases s.exists_isOpen_le_add μ (ENNReal.half_pos hε₀).ne' with ⟨U, hUs, hUo, hμU⟩
    set t : Set (α × ℝ) :=
      {(c, r) : α × ℝ | c ∈ s ∧ r ∈ f c ∩ Ioo 0 (scalingScaleOf μ 3) ∧ closedBall c r ⊆ U}
    obtain ⟨u, hus, huc, hud, hμ⟩ : ∃ u ⊆ t, u.Countable ∧
        u.PairwiseDisjoint (fun a ↦ closedBall a.1 a.2) ∧
        μ (s \ ⋃ a ∈ u, closedBall a.1 a.2) = 0 := by
      apply Vitali.exists_disjoint_covering_ae μ s t (scalingConstantOf μ 3) Prod.snd Prod.fst
      · exact fun _ _ ↦ Subset.rfl
      · exact fun x hx ↦ measure_mul_le_scalingConstantOf_mul _ (by simp) hx.2.1.2.2.le
      · intro x hx
        grw [← ball_subset_interior_closedBall, nonempty_ball]
        exact hx.2.1.2.1
      · exact fun _ _ ↦ isClosed_closedBall
      · intro x hx ε hε
        rcases Metric.nhds_basis_closedBall.mem_iff.mp (hUo.mem_nhds (hUs hx)) with ⟨δ, hδ₀, hδU⟩
        rcases hf x hx (ε ⊓ δ ⊓ scalingScaleOf μ 3)
          (lt_min (lt_min hε hδ₀) (scalingScaleOf_pos _ _)) with ⟨r, hrf, hr₀, hrε⟩
        rw [lt_min_iff, lt_min_iff] at hrε
        refine ⟨(x, r), ⟨hx, ⟨hrf, hr₀, hrε.2⟩, ?_⟩, hrε.1.1.le, rfl⟩
        grw [hrε.1.2, hδU]
    rcases exists_closedBall_covering_tsum_measure_le_of_measure_zero μ (ENNReal.half_pos hε₀).ne'
      f _ hμ (fun x hx δ hδ ↦ hf x hx.1 δ hδ) with ⟨v, r', hvc, hv_sub, hrf, hs_sub, hv_tsum⟩
    set goodR : α → ℝ := Function.extend (fun x : u ↦ x.1.1) (fun cr ↦ cr.1.2) r'
    have hinj : u.InjOn Prod.fst := by
      rintro ⟨x, δ₁⟩ h₁ ⟨x₂, δ₂⟩ h₂ (rfl : x = x₂)
      apply (hud.eq_or_disjoint h₁ h₂).resolve_right ?_
      rw [Set.not_disjoint_iff]
      use x
      simp [(hus h₁).2.1.2.1.le, (hus h₂).2.1.2.1.le]
    have hgoodR_fst_u : ∀ x ∈ u, goodR x.1 = x.2 := by
      intro x hx
      lift x to u using hx
      simp only [goodR]
      apply hinj.injective.extend_apply
    have hgoodR_not_u : ∀ x ∉ Prod.fst '' u, goodR x = r' x := by
      intro x hx
      apply Function.extend_apply'
      simpa using hx
    refine ⟨Prod.fst '' u ∪ v, goodR, ?_, ?_, ?_, ?_, ?_⟩
    · exact huc.image _ |>.union hvc
    · rintro x (⟨y, hy, rfl⟩ | hx)
      · exact (hus hy).1
      · exact (hv_sub hx).1
    · intro x hx
      rcases em (x ∈ Prod.fst '' u) with ⟨y, hy, rfl⟩ | hx'
      · rw [hgoodR_fst_u y hy]
        exact (hus hy).2.1.1
      · rw [hgoodR_not_u x hx']
        exact hrf _ (hx.resolve_left hx')
    · intro x hxs
      simp only [mem_iUnion, exists_prop, mem_union, mem_image]
      by_cases hx : x ∈ ⋃ a ∈ u, closedBall a.1 a.2
      · rw [mem_iUnion₂] at hx
        rcases hx with ⟨y, hyu, hy⟩
        refine ⟨y.1, .inl ⟨y, hyu, rfl⟩, ?_⟩
        rwa [hgoodR_fst_u y hyu]
      · have := hs_sub ⟨hxs, hx⟩
        rcases mem_iUnion₂.mp this with ⟨c, hc, hcx⟩
        refine ⟨c, .inr hc, ?_⟩
        rwa [hgoodR_not_u]
        rintro ⟨y, hy, rfl⟩
        refine (hv_sub hc).2 <| mem_iUnion₂_of_mem hy ?_
        simp [(hus hy).2.1.2.1.le]
    · rw [tsum_congr_set_coe (fun x ↦ μ (closedBall x (goodR x))) Set.union_diff_self.symm]
      grw [ENNReal.tsum_union_le (fun x ↦ μ (closedBall x (goodR x)))]
      rw [tsum_image (fun x ↦ μ (closedBall x (goodR x))) hinj]
      simp only [hgoodR_fst_u _ (Subtype.prop _),
        fun x : ↑(v \ Prod.fst '' u) ↦ hgoodR_not_u x x.2.2]
      grw [← measure_biUnion huc hud (fun _ _ ↦ measurableSet_closedBall),
        ENNReal.tsum_mono_subtype (fun x ↦ μ (closedBall x (r' x))) diff_subset, ← ε.add_halves,
        ← add_assoc, hv_tsum, ← hμU]
      gcongr
      refine iUnion₂_subset fun x hx ↦ ?_
      exact (hus hx).2.2

lemma outerMeasure_le_mul' {μ : Measure α} [ClosedBallCoveringMeasure μ]
    {ν : OuterMeasure α} {C : ℝ≥0∞} {s : Set α} (hsC : μ s ≠ 0 ∨ C ≠ ∞) (hCs : C ≠ 0 ∨ μ s ≠ ∞)
    (h : ∀ x ∈ s, ∃ᶠ εr : ℝ≥0∞ × ℝ in 𝓝[>] 0 ×ˢ 𝓝[>] 0,
      ν (s ∩ closedBall x εr.2) ≤ (C + εr.1) * μ (closedBall x εr.2)) :
    ν s ≤ C * μ s := by
  -- Thus it suffices to prove `ν s ≤ C' * (μ s + ε)` for all `C' > C` and `ε > 0`
  suffices ∀ ε > 0, ν s ≤ (C + ε) * (μ s + ε) by
    have H : Tendsto (fun ε ↦ (C + ε) * (μ s + ε)) (𝓝 0) (𝓝 (C * μ s)) := by
      apply ENNReal.Tendsto.mul <;>
        first | assumption | simpa using tendsto_const_nhds.add (tendsto_id (x := 𝓝 (0 : ℝ≥0∞)))
    exact ge_of_tendsto_of_frequently H <| (frequently_gt_nhds _).mono this
  -- Now we use `exists_closedBall_covering_tsum_measure_le`,
  -- to obtain a covering by countably many balls such that
  -- `ν (s ∩ closedBall x (r x)) ≤ (C + ε) * μ (closedBall x (r x))` for each ball
  -- and `∑' x : t, μ (closedBall x.1 (r x)) ≤ μ s + ε`
  intro ε hε
  obtain ⟨t, r, htc, -, hνμ, hsr, hμ⟩ : ∃ (t : Set α) (r : α → ℝ), Set.Countable t ∧ t ⊆ s ∧
      (∀ x ∈ t, ν (s ∩ closedBall x (r x)) ≤ (C + ε) * μ (closedBall x (r x))) ∧
      s ⊆ ⋃ x ∈ t, closedBall x (r x) ∧ ∑' x : t, μ (closedBall x.1 (r x)) ≤ μ s + ε := by
    refine exists_closedBall_covering_tsum_measure_le μ hε.ne'
      (fun x ↦ {r | ν (s ∩ closedBall x r) ≤ (C + ε) * μ (closedBall x r)}) s ?_
    intro x hx δ hδ
    simp only [((nhdsGT_basis_of_exists_gt ⟨(1 : ℝ≥0∞), one_pos⟩).prod
      (nhdsGT_basis (0 : ℝ))).frequently_iff] at h
    rcases h x hx (ε, δ) ⟨hε, hδ⟩ with ⟨⟨ε', r⟩, ⟨⟨-, hε'⟩, hr⟩, hle⟩
    refine ⟨r, ?_, hr⟩
    simp_all only [mem_setOf_eq]
    refine hle.trans ?_
    gcongr
  have := htc.to_subtype
  calc
    ν s ≤ ν (⋃ x : t, s ∩ closedBall x (r x)) := by
      rw [← inter_iUnion]
      gcongr
      simpa
    _ ≤ ∑' x : t, ν (s ∩ closedBall x (r x)) := measure_iUnion_le _
    _ ≤ ∑' x : t, (C + ε) * μ (closedBall x (r x)) := by gcongr with i; exact hνμ i i.2
    _ ≤ (C + ε) * (μ s + ε) := by rw [ENNReal.tsum_mul_left]; gcongr

lemma outerMeasure_le_mul {μ : Measure α} [SigmaFinite μ] [ClosedBallCoveringMeasure μ]
    {ν : OuterMeasure α} {C : ℝ≥0∞} {s : Set α} (hsC : μ s ≠ 0 ∨ C ≠ ∞)
    (h : ∀ x ∈ s, ∃ᶠ εr : ℝ≥0∞ × ℝ in 𝓝[>] 0 ×ˢ 𝓝[>] 0,
      ν (s ∩ closedBall x εr.2) ≤ (C + εr.1) * μ (closedBall x εr.2)) :
    ν s ≤ C * μ s := by
  rcases eq_or_ne C 0 with rfl | hC
  · calc
    ν s = ν (⋃ n, s ∩ spanningSets μ n) := by simp [← inter_iUnion]
    _ ≤ ∑' n, ν (s ∩ spanningSets μ n) := measure_iUnion_le _
    _ ≤ ∑' n, 0 * μ (s ∩ spanningSets μ n) := by
      gcongr with n
      refine outerMeasure_le_mul' (by simp) (.inr ?_) fun x hx ↦ (h x hx.1).mono ?_
      · exact (measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top ..) |>.ne
      · exact fun _ ↦ le_trans <| by gcongr; apply inter_subset_left
    _ = 0 * μ s := by simp
  · exact outerMeasure_le_mul' hsC (.inl hC) h

/-- Suppose that `ν (s ∩ closedBall x r) = O(μ (closedBall x r))` at all points of a set `s`
and `ν (s ∩ closedBall x r) = o(μ (closedBall x r))` at a.e. points of the set.
Then `ν s = 0`.

The actual statement can't use `Asymptotics.IsBigO` and `Asymptotics.IsLittleO`,
because the LHS and the RHS are in `ℝ≥0∞`, not `ℝ`.

Note that we do not assume measurability of `s` or `C`. -/
lemma outerMeasure_null_of_forall_le_mul_ae_null {μ : Measure α} [SigmaFinite μ]
    [ClosedBallCoveringMeasure μ]
    {ν : OuterMeasure α} {C : α → ℝ≥0} {s : Set α} (hC : ∀ᵐ x ∂μ, x ∈ s → C x = 0)
    (h : ∀ x ∈ s, ∃ᶠ εr : ℝ≥0∞ × ℝ in 𝓝[>] 0 ×ˢ 𝓝[>] 0,
      ν (s ∩ closedBall x εr.2) ≤ (C x + εr.1) * μ (closedBall x εr.2)) :
    ν s = 0 := by
  grw [← nonpos_iff_eq_zero, measure_le_inter_add_diff (t := {x | C x = 0})]
  apply add_nonpos
  · calc
      ν (s ∩ {x | C x = 0}) ≤ 0 * μ (s ∩ {x | C x = 0}) := by
        refine outerMeasure_le_mul (by simp) fun x hx ↦ ?_
        grw [inter_subset_left]
        simpa [hx.2.out] using h x hx.1
      _ = 0 := zero_mul _
  · set t := s \ {x | C x = 0}
    have hμt : μ t = 0 := by simpa [t, ae_iff] using hC
    calc
      ν t = ν (⋃ n : ℕ, {x ∈ t | C x ≤ n}) := by
        congr with x
        simp [exists_nat_ge]
      _ ≤ ∑' n : ℕ, ν {x ∈ t | C x ≤ n} := measure_iUnion_le _
      _ ≤ ∑' n : ℕ, n * μ {x ∈ t | C x ≤ n} := by
        gcongr with n
        apply outerMeasure_le_mul
        · simp
        · intro x hx
          simp only [t]
          grw [sep_subset, diff_subset, ← (mod_cast hx.2 : (C x : ℝ≥0∞) ≤ n)]
          exact h x hx.1.1
      _ ≤ ∑' n : ℕ, n * μ t := by gcongr; apply Set.sep_subset
      _ ≤ 0 := by simp [hμt]

lemma outerMeasure_null_of_null_of_forall_exists_le_mul {μ : Measure α} [SigmaFinite μ]
    [ClosedBallCoveringMeasure μ] {ν : OuterMeasure α} {s : Set α} (hs : μ s = 0)
    (h : ∀ x ∈ s, ∃ C : ℝ≥0, ∃ᶠ r : ℝ in 𝓝[>] 0, ν (s ∩ closedBall x r) ≤ C * μ (closedBall x r)) :
    ν s = 0 := by
  -- TODO: move 2nd part of the proof here instead of calling the result
  choose! C hC using h
  apply outerMeasure_null_of_forall_le_mul_ae_null (μ := μ) (C := C)
  · exact measure_mono_null (by simp +contextual [subset_def]) hs
  · intro x hx
    refine .filter_mono ?_ curry_le_prod
    rw [frequently_curry_iff]
    refine .of_forall fun ε ↦ (hC x hx).mono fun r hr ↦ ?_
    grw [hr, ← le_self_add]

/-- Let `f : α → β` be a map from a space with Besicovitch property to any space.
Let `μ` be a σ-finite outer regular measure on `α`, let `ν` be an outer measure on `β`,
let `s` be a set in the domain, let `C` be a constant such that `μ s ≠ 0` or `C ≠ ∞`.
Suppose that for each `x ∈ s` and a positive `ε`,
for a set of positive `r` that accumulates to zero,
we have `ν (f '' (s ∩ Metric.closedBall x r)) ≤ (C + ε) * μ (Metric.closedBall x r)`.
Then `ν (f '' s) ≤ C * μ s`.

Briefly speaking, this means that `ν (f '' s) ≤ C * μ s`
provided that a similar estimate holds for sufficiently small ball around each point `x ∈ s`.

See also `Besicovitch.measure_image_le_mul`.
-/
lemma outerMeasure_image_le_mul {f : α → β} {μ : Measure α} [SigmaFinite μ]
    [ClosedBallCoveringMeasure μ]
    {ν : OuterMeasure β} {C : ℝ≥0∞} {s : Set α} (hsC : μ s ≠ 0 ∨ C ≠ ∞)
    (h : ∀ x ∈ s, ∃ᶠ εr : ℝ≥0∞ × ℝ in 𝓝[>] 0 ×ˢ 𝓝[>] 0,
      ν (f '' (s ∩ closedBall x εr.2)) ≤ (C + εr.1) * μ (closedBall x εr.2)) :
    ν (f '' s) ≤ C * μ s := by
  simp only [← OuterMeasure.comap_apply] at *
  exact outerMeasure_le_mul hsC h

/-- Let `f : α → β` be a map from a space with Besicovitch property to any space.
Let `μ` be a σ-finite outer regular measure on `α`, let `ν` be a measure on `β`,
let `s` be a set in the domain, let `C` be a constant such that `μ s ≠ 0` or `C ≠ ∞`.
Suppose that for each `x ∈ s` and a positive `ε`,
for a set of positive `r` that accumulates to zero,
we have `ν (f '' (s ∩ Metric.closedBall x r)) ≤ (C + ε) * μ (Metric.closedBall x r)`.
Then `ν (f '' s) ≤ C * μ s`.

Briefly speaking, this means that `ν (f '' s) ≤ C * μ s`
provided that a similar estimate holds for sufficiently small ball around each point `x ∈ s`.

See also `Besicovitch.outerMeasure_image_le_mul`.
-/
lemma measure_image_le_mul {_ : MeasurableSpace β} {f : α → β} {μ : Measure α} [SigmaFinite μ]
    [ClosedBallCoveringMeasure μ] {ν : Measure β} {C : ℝ≥0∞} {s : Set α} (hsC : μ s ≠ 0 ∨ C ≠ ∞)
    (h : ∀ x ∈ s, ∃ᶠ εr : ℝ≥0∞ × ℝ in 𝓝[>] 0 ×ˢ 𝓝[>] 0,
      ν (f '' (s ∩ closedBall x εr.2)) ≤ (C + εr.1) * μ (closedBall x εr.2)) :
    ν (f '' s) ≤ C * μ s :=
  outerMeasure_image_le_mul hsC h

-- TODO: some of the nonnegativity/positivity assumptions can be omitted,
-- because in the other case, the goal is trivial.
lemma hasudorffMeasure_image_le_mul' {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {f : α → X} {μ : Measure α} [ClosedBallCoveringMeasure μ] {C : ℝ≥0∞}
    {s : Set α} (hsC : μ s ≠ 0 ∨ C ≠ ∞) {dimDom holderExp dimImg : ℝ} {μBall : ℝ≥0∞}
    (holderExp_pos : 0 < holderExp)
    (hμ_dim : ∀ x (r : ℝ≥0), μ (closedBall x r) = r ^ dimDom * μBall)
    (hμball₀ : μBall ≠ 0) (hμball : μBall ≠ ∞)
    (hdim : dimDom ≤ holderExp * dimImg)
    (hdimDom : 0 < dimDom)
    (h : ∀ x ∈ s, ∀ ε > 0,
      ∀ᶠ y in 𝓝[s] x, edist (f y) (f x) ≤ (C + ε) * edist y x ^ holderExp) :
    μH[dimImg] (f '' s) ≤ ((2 * C) ^ dimImg / μBall) * μ s := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp
  have hdimImg_pos : 0 < dimImg := by
    grw [← mul_pos_iff_of_pos_left holderExp_pos, ← hdim]
    exact hdimDom
  suffices ∀ d, 0 < d →
      OuterMeasure.mkMetric'.pre
        (fun s ↦ EMetric.diam s ^ dimImg) d (f '' s) ≤ ((2 * C) ^ dimImg / μBall) * μ s by
    simpa only [hausdorffMeasure, ← toOuterMeasure_apply, mkMetric_toOuterMeasure,
      OuterMeasure.mkMetric, OuterMeasure.mkMetric', OuterMeasure.iSup_apply, iSup_le_iff]
  intro d hd
  cases C with
  | top =>
    convert le_top
    simp [ENNReal.top_rpow_of_pos, hdimImg_pos, ENNReal.mul_eq_top, hμball, ENNReal.div_eq_top,
      hsC.neg_resolve_right rfl]
    infer_instance
  | coe C =>
    clear hsC
    have : SigmaFinite μ := by
      refine ⟨⟨⟨(closedBall hsne.choose ·), fun _ ↦ mem_univ _, fun i ↦ ?_,
        iUnion_closedBall_nat _⟩⟩⟩
      simp only [hμ_dim, ← NNReal.coe_natCast]
      refine ENNReal.mul_lt_top ((ENNReal.rpow_lt_top_iff_of_pos ?_).mpr ?_) hμball.lt_top
      · assumption
      · simp
    apply outerMeasure_image_le_mul
    · simp [ENNReal.div_eq_top, hdimImg_pos, hdimImg_pos.not_gt, hμball₀, hμball,
        ENNReal.mul_eq_top]
    intro x hx
    specialize h x hx
    refine .filter_mono ?_ curry_le_prod
    rw [frequently_curry_iff]
    refine Eventually.frequently <| eventually_mem_nhdsWithin.mono fun ε (hε : 0 < ε) ↦ ?_
    obtain ⟨ε', hε'₀, hε'⟩ : ∃ ε' > (0 : ℝ≥0),
        (2 * (C + ε') : ℝ≥0∞) ^ dimImg ≤ (((2 * C) ^ dimImg / μBall) + ε) * μBall := by
      apply Eventually.exists_gt
      refine (ContinuousAt.tendsto ?_).eventually_le_const ?_
      · refine ENNReal.continuous_rpow_const.continuousAt.comp ?_
        refine ENNReal.continuousAt_const_mul (by simp) |>.comp ?_
        fun_prop
      · rw [← ENNReal.div_lt_iff]
        · simp
          apply ENNReal.lt_add_right
          · finiteness
          · positivity
        · exact .inl hμball₀
        · exact .inl hμball
    rw [(nhdsGT_basis _).frequently_iff]
    intro r' hr₀'
    obtain ⟨δ, hδ₀, hδ₁, hδr, hδCε, hδ⟩ : ∃ δ > (0 : ℝ≥0), δ ≤ 1 ∧ δ < r' ∧
        (∀ y ∈ s ∩ closedBall x δ, dist (f y) (f x) ≤ (C + ε') * dist y x ^ holderExp) ∧
        2 * (C + ε') * δ ^ holderExp ≤ d := by
      apply Eventually.exists_gt
      apply_rules [Eventually.and]
      · exact eventually_le_nhds one_pos
      · exact (ContinuousAt.tendsto <| by fun_prop).eventually_lt_const (by simpa)
      · specialize h ε' (mod_cast hε'₀)
        rw [Metric.nhdsWithin_basis_ball.eventually_iff] at h
        rcases h with ⟨δ, hδ₀, hδ⟩
        lift δ to ℝ≥0 using hδ₀.le
        filter_upwards [eventually_lt_nhds (b := δ) (mod_cast hδ₀)] with δ' hδ' y hy
        specialize hδ ⟨closedBall_subset_ball (mod_cast hδ') hy.2, hy.1⟩
        simp (disch := positivity)
          only [dist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg] at hδ ⊢
        exact mod_cast hδ
      · refine (ContinuousAt.tendsto ?_).eventually_le_const ?_
        · refine ENNReal.continuousAt_const_mul (by left; finiteness) |>.comp ?_
          fun_prop
        · simp (disch := positivity) [ENNReal.zero_rpow_of_pos, hd]
    refine ⟨δ, ⟨hδ₀, hδr⟩, ?_⟩
    have hmaps : MapsTo f (s ∩ closedBall x δ) (closedBall (f x) ((C + ε') * δ ^ holderExp)) := by
      intro y hy
      grw [mem_closedBall, hδCε y hy, mem_closedBall.mp hy.2]
    have hdiam : EMetric.diam (f '' (s ∩ closedBall x δ)) ≤ 2 * (C + ε') * δ ^ holderExp := by
      grw [hmaps.image_subset, EMetric.diam_metricClosedBall_le,
        ← ENNReal.coe_rpow_of_nonneg _ (by positivity)]
      norm_cast
      rw [← mul_assoc]
    grw [OuterMeasure.mkMetric'.pre_le, hdiam, hμ_dim, ENNReal.mul_rpow_of_nonneg,
      ← ENNReal.rpow_mul, ← mul_assoc, mul_right_comm]
    gcongr 1
    · apply ENNReal.rpow_le_rpow_of_exponent_ge
      · exact mod_cast hδ₁
      · exact hdim
    · positivity
    · grw [hdiam, hδ]

lemma hasudorffMeasure_image_le_mul {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [OpensMeasurableSpace α] [T1Space α]
    {f : α → X} {μ : Measure α} [ClosedBallCoveringMeasure μ] {C : ℝ≥0∞}
    {s : Set α} (hsC : μ s ≠ 0 ∨ C ≠ ∞) {dimDom holderExp dimImg : ℝ} {μBall : ℝ≥0∞}
    (holderExp_pos : 0 < holderExp)
    (hμ_dim : ∀ x (r : ℝ≥0), μ (closedBall x r) = r ^ dimDom * μBall)
    (hμball₀ : μBall ≠ 0) (hμball : μBall ≠ ∞)
    (hdim : dimDom ≤ holderExp * dimImg)
    (hdimDom : 0 ≤ dimDom)
    (h : ∀ x ∈ s, ∀ ε > 0,
      ∀ᶠ y in 𝓝[s] x, edist (f y) (f x) ≤ (C + ε) * edist y x ^ holderExp) :
    μH[dimImg] (f '' s) ≤ ((2 * C) ^ dimImg / μBall) * μ s := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp
  rcases hdimDom.eq_or_lt with rfl | hdimDom
  · rw [mul_nonneg_iff_of_pos_left holderExp_pos] at hdim
    rcases hsne.exists_eq_singleton_or_nontrivial with ⟨a, rfl⟩ | ⟨a, ha, b, hb, hne⟩
    · rw [image_singleton, ← closedBall_zero (x := a), ← NNReal.coe_zero, hμ_dim]
      rcases hdim.eq_or_lt with rfl | hdimImg_pos
      · simp [ENNReal.inv_mul_cancel, *]
      · have := MeasureTheory.Measure.noAtoms_hausdorff X hdimImg_pos
        simp
    · have := calc
        μBall + μBall = μ {a} + μ {b} := by
          simp only [← closedBall_zero, ← NNReal.coe_zero, hμ_dim]
          simp
        _ = μ {a, b} := by
          rw [← singleton_union, measure_union]
          · simpa
          · exact measurableSet_singleton b
        _ ≤ μ (closedBall a (nndist a b)) := by
          gcongr
          simp [insert_subset_iff, dist_comm]
        _ = μBall := by rw [hμ_dim]; simp
      refine absurd ?_ this.not_gt
      exact ENNReal.lt_add_right hμball hμball₀
  · exact hasudorffMeasure_image_le_mul' hsC holderExp_pos hμ_dim hμball₀ hμball hdim hdimDom h
