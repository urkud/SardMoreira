import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder

open scoped unitInterval Topology
open Asymptotics Filter MeasureTheory

section NormedField

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

-- more general version of the first sorry
-- lemma aux_hmeas {a b : ℝ} (h : a ≤ b) : volume (Set.Icc a b) = b - a := sorry

-- XXX: is this in mathlib already?
lemma measure_finite_of_subset {α : Type*} [MeasurableSpace α] {μ : Measure α} {s t : Set α}
    (ht : μ t < ⊤) (hst : s ⊆ t) : μ s < ⊤ :=
  (measure_mono hst).trans_lt ht

-- Lemma 8 in the blueprint: the statement might be slightly off, check carefully!
lemma cdh_at_sub_affine_le_of_meas {f : E → F} {a b : E} {C r : NNReal} {δ : ℝ} (hδ : δ ∈ (Set.Ioo (0 : ℝ) 1))
    (hf : DifferentiableOn ℝ f (segment ℝ a b))
    (hf' : ∀ t : ℝ, t ∈ I →
      ‖lineDeriv ℝ f (a + t • (b - a)) (b - a)‖ ≤ C * (t ^ r.toReal) * ‖b - a‖₊ ^ (1 + r).toReal)
    {s : Set ℝ} (hsmeas : 1 - δ ≤ (volume (I ∩ s)).toReal)
    (hs' : ∀ t : ℝ, t ∈ s → lineDeriv ℝ f (a + t • (b - a)) (b - a) = 0) :
    ‖f b - f a‖ ≤ C * δ * (‖b - a‖₊ ^ (1 + r).toReal) := by

  have aux₁ : volume I = 1 := sorry -- surely in mathlib
  have finIinterS : volume (I ∩ s) < ⊤ := measure_finite_of_subset (by simp) Set.inter_subset_left
    -- trans (volume I + 1); swap; simp
    -- suffices hyp: volume (I ∩ s) ≤ volume I by calc
    --   _ ≤ volume I := hyp
    --   _ < volume I + 1 := by norm_num
    -- apply volume.mono Set.inter_subset_left
  have finIinterScompl : volume (I ∩ sᶜ) < ⊤ := measure_finite_of_subset (by simp) Set.inter_subset_left
  have aux₂ := calc (volume (I ∩ s)).toReal + (volume (I ∩ sᶜ)).toReal
    _ ≤ (volume ((I ∩ s) ∪ (I ∩ sᶜ))).toReal := by
      have h2' : volume (I ∩ s) + volume (I ∩ sᶜ) < ⊤ := sorry -- add finIinterS and finIinterScompl
      have h3 : volume ((I ∩ s) ∪ (I ∩ sᶜ)) < ⊤ := by
        have : (I ∩ s) ∪ (I ∩ sᶜ) ⊆ I := by simp
        apply measure_finite_of_subset (by simp) this
      rw [← ENNReal.toReal_add finIinterS.ne finIinterScompl.ne,
        ENNReal.toReal_le_toReal h2'.ne h3.ne]
      let aux := MeasureTheory.measure_union_le (I ∩ s) (I ∩ sᶜ) (μ := volume)
      -- |aux| is the other direction: need to use disjointness of these sets
      sorry
    _ = (volume I).toReal := by congr; simp
    _ = 1 := by rw [aux₁]; simp
  have hscompl : (volume (I ∩ sᶜ)).toReal ≤ δ := calc (volume (I ∩ sᶜ)).toReal
    _ ≤ 1 - (volume (I ∩ s)).toReal := by linarith [aux₂]
    _ ≤ 1 - (1 - δ) := by gcongr
    _ = δ := by ring

  -- occurs twice as a side goal: perhaps this is not needed if using lintegral instead
  have : MeasurableSet s := by -- if not automatic, add as assumption
    by_contra! h
    have : volume s = 0 := by sorry -- follows from choice of junk value, right?
    have : volume (I ∩ s) = 0 := measure_inter_null_of_null_right I this
    simp [this] at hsmeas
    exact (lt_self_iff_false 1).mp (by linarith [hδ.2, hsmeas])
  have hsmeasurable : MeasurableSet (I ∩ sᶜ) := by measurability

  calc ‖f b - f a‖
    _ = ‖∫ t in I, lineDeriv ℝ f (a + t • (b - a)) (b - a)‖ := by
      sorry -- standard form of MVT, surely somewhere in mathlib

    -- XXX: use MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae for the next few steps,
    -- move part of these steps into showing the hypothesis
    _ = ‖∫ t in I ∩ sᶜ, lineDeriv ℝ f (a + t • (b - a)) (b - a)‖ := by
      congr 1
      apply setIntegral_eq_of_subset_of_forall_diff_eq_zero (measurableSet_Icc) (by simp)
      intro x hx
      have : x ∈ I ∩ s := by simpa using hx
      exact hs' _ this.2
    _ ≤ ∫ t in I ∩ sᶜ, ‖lineDeriv ℝ f (a + t • (b - a)) (b - a)‖ := by
      apply norm_integral_le_integral_norm
    _ ≤ ∫ t in I ∩ sᶜ, C * (t ^ r.toReal) * ‖b - a‖₊ ^ (1 + r).toReal := by
      -- XXX: is using the Lebesgue integral nicer, here and below?
      apply setIntegral_mono_on
      · sorry -- integrability hypothesis
      · sorry -- integrability hypothesis
      · exact hsmeasurable
      exact fun x hx ↦ hf' _ hx.1
    _ = C * ‖b - a‖₊ ^ (1 + r).toReal * ∫ t in I ∩ sᶜ, (t ^ r.toReal) := sorry -- easy; re-order steps
    -- the following estimate is not ideal, but good enough
    _ ≤ C * ‖b - a‖₊ ^ (1 + r).toReal * (volume (I ∩ sᶜ)).toReal := by
      gcongr
      calc ∫ (t : ℝ) in I ∩ sᶜ, t ^ r.toReal
        _ ≤ ∫ (t : ℝ) in I ∩ sᶜ, 1 := by
          apply MeasureTheory.setIntegral_mono_on
          · sorry -- integrability hypothesis; follows since continuous
          · rw [MeasureTheory.integrableOn_const]
            right; exact finIinterScompl
          · exact hsmeasurable
          intro x hx
          -- XXX: is there a nicer proof of this? is this result already in mathlib?
          rw [show 1 = (1 : ℝ) ^ r.toReal by norm_num]
          exact (NNReal.monotone_rpow_of_nonneg (by positivity)) (a := ⟨x, hx.1.1⟩) (b := 1) hx.1.2
        _ = (volume (I ∩ sᶜ)).toReal := by
          have aux := setIntegral_const (s := I ∩ sᶜ) (c := (1 : ℝ)) (μ := volume)
          rw [aux]
          simp
    _ ≤ C * ‖b - a‖₊ ^ (1 + r).toReal * δ := by gcongr
    _ = C * δ * ‖b - a‖₊ ^ (1 + r).toReal := by ring
