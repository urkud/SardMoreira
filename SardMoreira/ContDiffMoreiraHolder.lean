module

public import Mathlib
public import SardMoreira.ContDiff
public import SardMoreira.ContinuousMultilinearMap

@[expose] public section

open scoped unitInterval Topology NNReal
open Asymptotics Filter Set

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace ContDiffPointwiseHolderAt

theorem fderiv₂ {f : E × F → G} {a : E × F} {k l : ℕ} {α : I}
    (hf : ContDiffPointwiseHolderAt k α f a) (hl : l < k) :
    ContDiffPointwiseHolderAt l α (fun b ↦ fderiv ℝ (fun y ↦ f (b.1, y)) b.2) a := by
  refine hf.fderiv hl |>.continuousLinearMap_comp (.precomp G (.inr ℝ E F))
    |>.congr_of_eventuallyEq ?_
  refine hf.contDiffAt.eventually (by simp) |>.mono fun x hx ↦ ?_
  simp [fderiv_comp_prodMk' (hx.differentiableAt <| mod_cast Nat.ne_zero_of_lt hl)]

end ContDiffPointwiseHolderAt

theorem OpenPartialHomeomorph.contDiffPointwiseHolderAt_symm [CompleteSpace E] {k : ℕ} {α : I}
    (f : OpenPartialHomeomorph E F) {a : F} (ha : a ∈ f.target)
    (hf' : (fderiv ℝ f (f.symm a)).IsInvertible)
    (hf : ContDiffPointwiseHolderAt k α f (f.symm a)) :
    ContDiffPointwiseHolderAt k α f.symm a where
  contDiffAt := contDiffAt_symm' f ha hf' hf.contDiffAt
  isBigO := by
    have hrpow : (‖· - a‖) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) :=
      (IsBigO.id_rpow_of_le_one α.2.2).comp_tendsto <| tendsto_norm_sub_self_nhdsGE _
    have hsymm_isBigO : (f.symm · - f.symm a) =O[𝓝 a] (· - a) := by
      simpa using f.hasFDerivAt_symm ha hf'.hasFDerivAt |>.isBigO_sub
    rcases eq_or_ne k 0 with rfl | hk₀
    · calc
        _ =O[𝓝 a] fun x ↦ f.symm x - f.symm a := by
          refine .of_norm_left ?_
          simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
            LinearIsometryEquiv.norm_map, isBigO_norm_left]
          exact isBigO_refl _ _
        _ =O[𝓝 a] fun x ↦ x - a := hsymm_isBigO
        _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := .of_norm_left hrpow
    · have hinv : ∀ᶠ x in 𝓝 (f.symm a), (fderiv ℝ f x).IsInvertible :=
        (hf.contDiffAt.continuousAt_fderiv <| mod_cast hk₀).eventually <|
           ContinuousLinearEquiv.isOpen.mem_nhds hf'
      have hinv' : ∀ᶠ x in 𝓝 a, (fderiv ℝ f (f.symm x)).IsInvertible :=
        f.continuousAt_symm ha |>.eventually hinv
      have hfderiv_isBigO :
          (fun x ↦ fderiv ℝ f.symm x - fderiv ℝ f.symm a) =O[𝓝 a]
            fun x ↦ fderiv ℝ f (f.symm x) - fderiv ℝ f (f.symm a) := by
        refine EventuallyEq.trans_isBigO ?_
          (ContinuousLinearMap.isBigO_inverse_sub_inverse hinv' ?_ ?_ ?_)
        · filter_upwards [f.continuousAt_symm ha hinv, f.open_target.mem_nhds ha] with x hfx hx
          rw [f.fderiv_symm hx hfx, f.fderiv_symm ha hf']
        · refine f.contDiffAt_symm' ha hf' hf.contDiffAt |>.continuousAt_fderiv (mod_cast hk₀)
            |>.norm |>.isBoundedUnder_le |>.mono_le ?_
          filter_upwards [hinv', f.open_target.mem_nhds ha] with x hfx hx
          simp [f.fderiv_symm hx hfx]
        · simp [hinv.self_of_nhds]
        · apply isBoundedUnder_const
      have hsymm_rpow_isBigO : (‖f.symm · - f.symm a‖ ^ (α : ℝ)) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) :=
        hsymm_isBigO.norm_norm.rpow α.2.1 (by simp [EventuallyLE])
      obtain rfl | hk₁ : k = 1 ∨ 1 < k := by grind
      · calc
          _ =O[𝓝 a] fun x ↦ fderiv ℝ f.symm x - fderiv ℝ f.symm a :=
            .of_norm_left <| by simp [iteratedFDeriv_one_eq, ← map_sub, isBigO_refl]
          _ =O[𝓝 a] fun x ↦ fderiv ℝ f (f.symm x) - fderiv ℝ f (f.symm a) := hfderiv_isBigO
          _ =O[𝓝 a] fun x ↦ ‖f.symm x - f.symm a‖ ^ (α : ℝ) := by
            simpa [iteratedFDeriv_one_eq, ← map_sub, Function.comp_def]
              using hf.isBigO.comp_tendsto (f.continuousAt_symm ha) |>.norm_left
          _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := hsymm_rpow_isBigO
      · calc
          (fun x ↦ iteratedFDeriv ℝ k f.symm x - iteratedFDeriv ℝ k f.symm a)
            =ᶠ[𝓝 a] fun x ↦
              (FormalMultilinearSeries.id ℝ E (f.symm x) k -
                ∑ c ≠ OrderedFinpartition.atomic k,
                  c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length f.symm x)
                    (fun m ↦ iteratedFDeriv ℝ (c.partSize m) f (f.symm x))).compContinuousLinearMap
                      (fun _ ↦ fderiv ℝ f.symm x) -
              (FormalMultilinearSeries.id ℝ E (f.symm a) k -
                ∑ c ≠ OrderedFinpartition.atomic k,
                  c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length f.symm a)
                    (fun m ↦ iteratedFDeriv ℝ (c.partSize m) f (f.symm a))).compContinuousLinearMap
                      (fun _ ↦ fderiv ℝ f.symm a) := by
            rw [← f.symm.symm_map_nhds_eq ha, f.symm_symm, eventuallyEq_map]
            filter_upwards [hf.contDiffAt.eventually (by simp),
              f.open_source.mem_nhds (f.mapsTo_symm ha), hinv]
              with x hx hfx hinv
            simp only [Function.comp_apply]
            rw [f.iteratedFDeriv_symm_eq_rec ha hf.contDiffAt le_rfl (fun _ ↦ hf'),
              f.iteratedFDeriv_symm_eq_rec (f.mapsTo hfx) (by simpa [hfx]) le_rfl (by simp [*])]
          _ = fun x ↦
            -∑ c ≠ OrderedFinpartition.atomic k,
              ((c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length f.symm x)
                (fun m ↦ iteratedFDeriv ℝ (c.partSize m) f (f.symm x))).compContinuousLinearMap
                  (fun _ ↦ fderiv ℝ f.symm x) -
                (c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length f.symm a)
                  (fun m ↦ iteratedFDeriv ℝ (c.partSize m) f (f.symm a))).compContinuousLinearMap
                    (fun _ ↦ fderiv ℝ f.symm a)) := by
            simp only [hk₁, FormalMultilinearSeries.id_apply_of_one_lt, zero_sub, neg_sub_neg,
              Finset.sum_sub_distrib, ContinuousMultilinearMap.compContinuousLinearMap_neg_left,
              ContinuousMultilinearMap.compContinuousLinearMap_sum_left, neg_sub]
          _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := .neg_left <| .fun_sum fun c hc ↦ ?_
        simp only [OrderedFinpartition.compContinuousLinearMap_compAlongOrderedFinpartition_left]
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, ← c.length_lt_iff] at hc
        apply c.compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_isBigO
        · exact f.contDiffAt_symm' ha hf' hf.contDiffAt
            |>.continuousAt_iteratedFDeriv (mod_cast hc.le) |>.norm |>.isBoundedUnder_le
        · refine .trans (.norm_right ?_) hrpow
          exact f.contDiffAt_symm' ha hf' hf.contDiffAt
            |>.differentiableAt_iteratedFDeriv (mod_cast hc) |>.isBigO_sub
        · intro m
          refine (ContinuousAt.tendsto <| .norm ?_).isBoundedUnder_le
          simp only [← ContinuousMultilinearMap.compContinuousLinearMapL_apply]
          refine .clm_apply ?_ ?_
          · refine map_continuous
              (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ _ _ _)
              |>.continuousAt.comp ?_
            refine continuousAt_pi.2 fun _ ↦ ?_
            exact f.contDiffAt_symm' ha hf' hf.contDiffAt |>.continuousAt_fderiv (mod_cast hk₀)
          · refine hf.contDiffAt.continuousAt_iteratedFDeriv (mod_cast c.partSize_le _) |>.comp ?_
            exact f.continuousAt_symm ha
        · exact fun _ ↦ isBoundedUnder_const
        · intro m
          apply ContinuousMultilinearMap.compContinuousLinearMap_sub_compContinuousLinearMap_isBigO
          · apply isBoundedUnder_const
          · exact (hf.of_order_le (c.partSize_le m) |>.isBigO |>.comp_tendsto <|
              f.continuousAt_symm ha) |>.trans hsymm_rpow_isBigO
          · intro i
            exact f.contDiffAt_symm' ha hf' hf.contDiffAt |>.continuousAt_fderiv (mod_cast hk₀)
              |>.norm |>.isBoundedUnder_le
          · exact fun _ ↦ isBoundedUnder_const
          · refine fun i ↦ hfderiv_isBigO.trans (.trans (.trans ?_ hsymm_isBigO.norm_right) hrpow)
            exact hf.contDiffAt.fderiv_right (mod_cast hk₁) |>.differentiableAt one_ne_zero
              |>.isBigO_sub |>.comp_tendsto <| f.continuousAt_symm ha
