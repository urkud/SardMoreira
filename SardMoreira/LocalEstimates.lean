import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Integral.SetIntegral

open scoped unitInterval Topology
open Asymptotics Filter

section NormedField

variable {𝕜 E F G : Type*} --[NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
--  [NormedAddCommGroup G] [NormedSpace 𝕜 G]


open scoped Convex
open MeasureTheory

-- Lemma 8 in the blueprint: the statement might be slightly off, check carefully!
lemma cdh_at_sub_affine_le_of_meas {f : E → F} {a b : E} {C r : NNReal} {δ : ℝ} (hδ : δ ∈ (Set.Ioo (0 : ℝ) 1))
    (hf : DifferentiableOn ℝ f [a -[ℝ] b])
    (hf' : ∀ t : ℝ, t ∈ I →
      ‖lineDeriv ℝ f (a + t • (b - a)) (b - a)‖ ≤ C * (t ^ r.toReal) * ‖b - a‖₊ ^ (1 + r).toReal)
    {s : Set ℝ} (hsmeas : 1 - δ ≤ (volume (I ∩ s)).toReal)
    (hs' : ∀ t : ℝ, t ∈ s → lineDeriv ℝ f (a + t • (b - a)) (b - a) = 0) :
    ‖f b - f a‖ ≤ C * δ * (‖b - a‖₊ ^ (1 + r).toReal) := by

  have aux₁ : volume I = 1 := sorry -- surely in mathlib
  have asdf := calc (volume (I ∩ sᶜ)).toReal + (volume (I ∩ s)).toReal
        _ ≤ (volume ((I ∩ sᶜ) ∪ (I ∩ s))).toReal := by
          let asdf := MeasureTheory.measure_union_le (I ∩ sᶜ) (I ∩ s) (μ := volume)
          have : volume (I ∩ s) < ⊤ := by
            trans 1; swap; simp
            rw [← aux₁]
            have : I ∩ s ⊆ I := by exact Set.inter_subset_left
            sorry -- let asdf := volume.mono this
          -- similarly for the other sets, hence asdf should imply the claim
          -- (or, better idea: see if one can choose the numbers more wisely to avoid this hassle)
          sorry
        _ = (volume I).toReal := by
          congr
          -- the following is surely in mathlib
          have : ∀ a b c : Set ℝ, (a ∩ b) ∪ (a ∩ c) = a ∩ (b ∪ c) := by
            intro a b c
            ext x
            simp
            aesop
          have : I ∩ sᶜ ∪ I ∩ s = (I ∩ (s ∪ sᶜ)) := by rw [Set.union_comm s]; exact this I sᶜ s
          rw [this, Set.union_compl_self s, Set.inter_univ]
        _ = 1 := by rw [aux₁]; simp
  have hscompl : (volume (I ∩ sᶜ)).toReal ≤ δ := calc (volume (I ∩ sᶜ)).toReal
    _ ≤ 1 - (volume (I ∩ s)).toReal := by linarith [asdf]
    _ ≤ 1 - (1 - δ) := by gcongr
    _ = δ := by ring

  calc ‖f b - f a‖
    _ = ‖∫ t in I, lineDeriv ℝ f (a + t • (b - a)) (b - a)‖ := by
      sorry -- standard form of MVT, somewhere in mathlib

    -- use MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae for the next few steps,
    -- move part of these steps into showing the hypothesis
    _ = ‖∫ t in I ∩ sᶜ, lineDeriv ℝ f (a + t • (b - a)) (b - a)‖ := by
      -- everywhere else, is zero
      -- like setIntegral_eq_integral_of_forall_compl_eq_zero, but with set integrals...
      sorry
    _ ≤ ∫ t in I ∩ sᶜ, ‖lineDeriv ℝ f (a + t • (b - a)) (b - a)‖ := by
      sorry --exact?--sorry
    _ ≤ ∫ t in I ∩ sᶜ, C * (t ^ r.toReal) * ‖b - a‖₊ ^ (1 + r).toReal := by
      sorry
    _ = C * ‖b - a‖₊ ^ (1 + r).toReal * ∫ t in I ∩ sᶜ, (t ^ r.toReal) := sorry
    -- the following estimate is not ideal, but good enough
    _ ≤ C * ‖b - a‖₊ ^ (1 + r).toReal * (volume (I ∩ sᶜ)).toReal := by
      gcongr
      calc ∫ (t : ℝ) in I ∩ sᶜ, t ^ r.toReal
        _ ≤ ∫ (t : ℝ) in I ∩ sᶜ, 1 := by
          apply MeasureTheory.setIntegral_mono_on -- XXX: is using the Lebesgue integral nicer?
          · sorry -- integrability hypothesis; follows since continuous
          · have aux := MeasureTheory.integrableOn_const (E := ℝ) (s := I ∩ sᶜ) (C := (1 : ℝ)) (μ := volume)
            rw [aux]
            right
            sorry -- ≤ δ is proven in hscompl
          · have : MeasurableSet s := by -- if not automatic, add as assumption
              by_contra! h
              have : volume s = 0 := by sorry -- follows by junk value, right?
              have : volume (I ∩ s) = 0 := measure_inter_null_of_null_right I this
              simp [this] at hsmeas
              exact (lt_self_iff_false 1).mp (by linarith [hδ.2, hsmeas])
            measurability
          intro x hx
          have : x ∈ I := hx.1
          -- remain: 0 ≤ x ≤ 1 implies x ^ r is at most 1
          -- not hard (e.g. use that this function is increasing on I); in mathlib?
          sorry
        _ = (volume (I ∩ sᶜ)).toReal := by
          have aux := setIntegral_const (s := I ∩ sᶜ) (c := (1 : ℝ)) (μ := volume)
          rw [aux]
          simp
    _ ≤ C * ‖b - a‖₊ ^ (1 + r).toReal * δ := by gcongr
    _ = C * δ * ‖b - a‖₊ ^ (1 + r).toReal := by ring
