import Mathlib
import SardMoreira.ContDiffMoreiraHolder

open scoped unitInterval NNReal
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

theorem hausdorffMeasure_setOf_finrank_eq [MeasurableSpace F] [BorelSpace F]
    (hp_dom : p < finrank ℝ E)
    (hp_cod : p < finrank ℝ F) (hk : k ≠ 0) {f : E → F} {s U : Set E}
    (hf : ContDiffMoreiraHolderOn k α f s U)
    (hs : ∀ x ∈ s, finrank ℝ (LinearMap.range <| fderiv ℝ f x) = p) :
    μH[sardMoreiraBound (finrank ℝ E) k α p] (f '' s) = 0 := by
  sorry

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
    apply Moreira2001.hausdorffMeasure_setOf_finrank_eq (by grind) (by grind) hk (U := U)
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
