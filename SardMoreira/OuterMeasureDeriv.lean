import Mathlib.MeasureTheory.Covering.Besicovitch

namespace Besicovitch

open scoped ENNReal NNReal Topology
open Metric Set Filter Fin MeasureTheory TopologicalSpace Besicovitch.TauPackage

universe u

variable {α : Type*} [MetricSpace α] {β : Type u} [SecondCountableTopology α] [MeasurableSpace α]
  [OpensMeasurableSpace α] [HasBesicovitchCovering α]

lemma outerMeasure_le_mul_of_sfinite {μ : Measure α} [SFinite μ] [μ.OuterRegular]
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

lemma outerMeasure_le_mul {μ : Measure α} [SigmaFinite μ] [μ.OuterRegular]
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
      refine outerMeasure_le_mul_of_sfinite (by simp) (.inr ?_) fun x hx ↦ (h x hx.1).mono ?_
      · exact (measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top ..) |>.ne
      · exact fun _ ↦ le_trans <| by gcongr; apply inter_subset_left
    _ = 0 * μ s := by simp
  · exact outerMeasure_le_mul_of_sfinite hsC (.inl hC) h

/-- Suppose that `ν (s ∩ closedBall x r) = O(μ (closedBall x r))` at all points of a set `s`
and `ν (s ∩ closedBall x r) = o(μ (closedBall x r))` at a.e. points of the set.
Then `ν s = 0`.

The actual statement can't use `Asymptotics.IsBigO` and `Asymptotics.IsLittleO`,
because the LHS and the RHS are in `ℝ≥0∞`, not `ℝ`.

Note that we do not assume measurability of `s` or `C`. -/
lemma outerMeasure_null_of_forall_le_mul_ae_null {μ : Measure α} [SigmaFinite μ] [μ.OuterRegular]
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
lemma outerMeasure_image_le_mul {f : α → β} {μ : Measure α} [SigmaFinite μ] [μ.OuterRegular]
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
    [μ.OuterRegular] {ν : Measure β} {C : ℝ≥0∞} {s : Set α} (hsC : μ s ≠ 0 ∨ C ≠ ∞)
    (h : ∀ x ∈ s, ∃ᶠ εr : ℝ≥0∞ × ℝ in 𝓝[>] 0 ×ˢ 𝓝[>] 0,
      ν (f '' (s ∩ closedBall x εr.2)) ≤ (C + εr.1) * μ (closedBall x εr.2)) :
    ν (f '' s) ≤ C * μ s :=
  outerMeasure_image_le_mul hsC h

lemma outerMeasure_le_lintegral {μ : Measure α} [SigmaFinite μ] [μ.OuterRegular]
    {ν : OuterMeasure α} {g : α → ℝ≥0} {s : Set α}
    (hg : Measurable g)
    (h : ∀ x ∈ s, ∀ C > g x, ∃ᶠ r : ℝ in 𝓝[>] 0,
      ν (s ∩ closedBall x r) ≤ C * μ (closedBall x r)) :
    ν s ≤ ∫⁻ x in s, g x ∂μ := by
  sorry
