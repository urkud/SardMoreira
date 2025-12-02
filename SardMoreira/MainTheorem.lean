import Mathlib
import SardMoreira.ContDiffMoreiraHolder
import SardMoreira.ImplicitFunction
import SardMoreira.LinearAlgebra

open scoped unitInterval NNReal Topology
open MeasureTheory Measure
open Module (finrank)

/-- Moreira's upper estimate on the Hausdorff dimension of the image of the set of points $x$
such that `fderiv ℝ f x` has rank at most `p < min n m`,
provided that `f` is a $$C^{k+(\alpha)}$$-map
from an `n`-dimensional space to an `m`-dimensional space.

Note that the estimate does not depend on `m`. -/
noncomputable def sardMoreiraBound (n k : ℕ) (α : I) (p : ℕ) : ℝ≥0 :=
  p + (n - p) / (k + ⟨α, α.2.1⟩)

theorem monotone_sardMoreiraBound (n : ℕ) {k : ℕ} (hk : k ≠ 0) (α : I) :
    Monotone (sardMoreiraBound n k α) := by
  apply monotone_nat_of_le_succ
  intro p
  rcases α with ⟨α, hα₀, hα₁⟩
  simp only [sardMoreiraBound, field]
  rw [← NNReal.coe_le_coe]
  push_cast [tsub_add_eq_tsub_tsub]
  grw [@NNReal.coe_sub_def _ 1, ← le_max_left, ← sub_nonneg]
  push_cast
  linarith only [hα₀, show (1 : ℝ) ≤ k by norm_cast; grind]

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {k p : ℕ} {α : I}

namespace Moreira2001

theorem hausdorffMeasure_image_piProd_fst_null_of_fderiv_comp_inr_zero
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace G] [BorelSpace G]
    [Nontrivial F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    {f : E × F → G} {s U : Set (E × F)} (hf : ContDiffMoreiraHolderOn k α f s U) (hk : k ≠ 0)
    (hs : ∀ x ∈ s, fderiv ℝ f x ∘L .inr ℝ E F = 0) :
    μH[sardMoreiraBound (finrank ℝ E + finrank ℝ F) k α (finrank ℝ E)]
      (Pi.prod Prod.fst f '' s) = 0 := by
  admit

theorem hausdorffMeasure_image_piProd_fst_null_of_finrank_eq
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace G] [BorelSpace G]
    [Nontrivial F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    {f : E × F → G} {s U : Set (E × F)} (hf : ContDiffMoreiraHolderOn k α f s U) (hk : k ≠ 0)
    (hs : ∀ x ∈ s, finrank ℝ (LinearMap.range <| fderiv ℝ (Pi.prod Prod.fst f) x) = finrank ℝ E) :
    μH[sardMoreiraBound (finrank ℝ E + finrank ℝ F) k α (finrank ℝ E)]
      (Pi.prod Prod.fst f '' s) = 0 := by
  apply hausdorffMeasure_image_piProd_fst_null_of_fderiv_comp_inr_zero hf hk
  intro x hx
  rw [← ContinuousLinearMap.finrank_range_prod_fst_iff_comp_inr_eq_zero, ← hs x hx]
  suffices fderiv ℝ (Pi.prod Prod.fst f) x = .prod (.fst ℝ E F) (fderiv ℝ f x) by
    -- TODO: introduce&use `ContinuousLinearMap.rank`/`ContinuousLinearMap.finrank`?
    generalize H : fderiv ℝ (Pi.prod Prod.fst f) x = f'
    rw [H] at this
    subst f'
    rfl
  unfold Pi.prod
  rw [DifferentiableAt.fderiv_prodMk (by fun_prop), fderiv_fst]
  exact hf.contDiffMoreiraHolderAt hx |>.differentiableAt hk

theorem hausdorffMeasure_image_nhdsWithin_null_of_finrank_eq [MeasurableSpace F] [BorelSpace F]
    (hp_dom : p < finrank ℝ E) (hp_cod : p < finrank ℝ F) (hk : k ≠ 0) {f : E → F} {s U : Set E}
    (hf : ContDiffMoreiraHolderOn k α f s U)
    (hs : ∀ x ∈ s, finrank ℝ (LinearMap.range <| fderiv ℝ f x) = p) {x : E} (hx : x ∈ s) :
    ∃ t ∈ 𝓝[s] x, μH[sardMoreiraBound (finrank ℝ E) k α p] (f '' t) = 0 := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by grind)
  have : FiniteDimensional ℝ F := .of_finrank_pos (Nat.zero_lt_of_lt hp_cod)
  rcases hf.exists_openPartialHomeomorph_conj_piProd_fst hk hx
    (ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range (fderiv ℝ f x))
    (Submodule.ClosedComplemented.of_finiteDimensional (LinearMap.range (fderiv ℝ f x)))
    with ⟨p, q, r, epq, epr, g, hx_epq, hepqU, hepq, hepq_symm, heqOn⟩
  use s ∩ epq.source, inter_mem_nhdsWithin _ (epq.open_source.mem_nhds hx_epq)
  set t := epq.target ∩ epq.symm ⁻¹' s
  have heqOn_g : Set.EqOn (Prod.snd ∘ epr ∘ f ∘ epq.symm) g epq.target := heqOn.comp_left
  have hg : ContDiffMoreiraHolderOn k α g t epq.target := by
    refine .congr_eqOn ?_ heqOn_g
    refine .continuousLinearMap_comp ?_ (.snd ℝ p r)
    refine .continuousLinearMap_comp ?_ (epr : F →L[ℝ] p × r)
    refine hf.comp hepq_symm (epq.symm_mapsTo.mono_right hepqU) ?_ hk
    exact (Set.mapsTo_preimage _ _).mono_left Set.inter_subset_right
  have := hausdorffMeasure_image_piProd_fst_null_of_finrank_eq hg
  sorry

theorem hausdorffMeasure_image_null_of_finrank_eq [MeasurableSpace F] [BorelSpace F]
    (hp_dom : p < finrank ℝ E)
    (hp_cod : p < finrank ℝ F) (hk : k ≠ 0) {f : E → F} {s U : Set E}
    (hf : ContDiffMoreiraHolderOn k α f s U)
    (hs : ∀ x ∈ s, finrank ℝ (LinearMap.range <| fderiv ℝ f x) = p) :
    μH[sardMoreiraBound (finrank ℝ E) k α p] (f '' s) = 0 := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by grind)
  rw [← coe_toOuterMeasure, ← OuterMeasure.comap_apply]
  refine measure_null_of_locally_null _ fun x hx ↦ ?_
  apply hausdorffMeasure_image_nhdsWithin_null_of_finrank_eq <;> assumption

end Moreira2001

theorem hausdorffMeasure_sardMoreiraBound_image_null_of_finrank_le
    [MeasurableSpace F] [BorelSpace F]
    (hp_dom : p < finrank ℝ E)
    (hp_cod : p < finrank ℝ F) (hk : k ≠ 0) {f : E → F} {s U : Set E}
    (hf : ContDiffMoreiraHolderOn k α f s U)
    (hs : ∀ x ∈ s, finrank ℝ (LinearMap.range <| fderiv ℝ f x) ≤ p) :
    μH[sardMoreiraBound (finrank ℝ E) k α p] (f '' s) = 0 := by
  -- Apply the Moreira2001 theorem to each of the sets where the rank is exactly `p' ≤ p`.
  have h_apply : ∀ p' ≤ p,
      μH[sardMoreiraBound (finrank ℝ E) k α p']
        (f '' {x ∈ s | finrank ℝ (LinearMap.range (fderiv ℝ f x)) = p'}) = 0 := by
    intro p' hp'
    apply Moreira2001.hausdorffMeasure_image_null_of_finrank_eq
      (by grind) (by grind) hk (U := U)
    · exact hf.subset_left Set.inter_subset_left
    · simp
  -- Since $s$ is the union of the sets where the rank is exactly $p'$ for $p' \leq p$,
  -- we can use the countable subadditivity of the Hausdorff measure.
  have h_union :
      f '' s = ⋃ p' ≤ p, f '' {x ∈ s | finrank ℝ (LinearMap.range (fderiv ℝ f x)) = p'} := by
    ext y
    simp only [Set.mem_image, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    exact ⟨fun ⟨x, hx, hx'⟩ ↦ ⟨_, hs x hx, x, ⟨hx, rfl⟩, hx'⟩,
      fun ⟨i, hi, x, hx, hx'⟩ ↦ ⟨x, hx.1, hx'⟩⟩
  simp only [h_union, measure_iUnion_null_iff]
  intro p' hp'
  rw [← nonpos_iff_eq_zero, ← h_apply p' hp']
  apply hausdorffMeasure_mono
  exact monotone_sardMoreiraBound _ hk _ hp'

theorem dimH_image_le_sardMoreiraBound_of_finrank_le
    (hp_dom : p < finrank ℝ E)
    (hp_cod : p < finrank ℝ F) (hk : k ≠ 0) {f : E → F} {s U : Set E}
    (hf : ContDiffMoreiraHolderOn k α f s U)
    (hs : ∀ x ∈ s, finrank ℝ (LinearMap.range <| fderiv ℝ f x) ≤ p) :
    dimH (f '' s) ≤ sardMoreiraBound (finrank ℝ E) k α p := by
  borelize F
  apply dimH_le_of_hausdorffMeasure_ne_top
  simp [hausdorffMeasure_sardMoreiraBound_image_null_of_finrank_le hp_dom hp_cod hk hf hs]
