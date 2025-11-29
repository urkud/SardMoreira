import Mathlib

open Function
open Module (finrank)

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G]
  [AddCommGroup H] [Module ℝ H]


theorem LinearMap.finrank_eq_finrank_iff_comp_eq_zero_of_comp_surjective
    [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ G]
    [FiniteDimensional ℝ H]
    (f : E × F →ₗ[ℝ] G × H) (hsurj : Surjective (.fst ℝ G H ∘ₗ f))
    (hzero : .fst ℝ G H ∘ₗ f ∘ₗ .inr ℝ E F = 0) :
    finrank ℝ (range f) = finrank ℝ G ↔ snd ℝ G H ∘ₗ f ∘ₗ .inr ℝ E F = 0 := by
  sorry

theorem LinearMap.finrank_range_prod_fst_iff_comp_inr_eq_zero
    [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ G]
    (f : E × F →ₗ[ℝ] G) :
    finrank ℝ (range (prod (fst ℝ E F) f)) = finrank ℝ E ↔ f ∘ₗ inr ℝ E F = 0 := by
  rw [finrank_eq_finrank_iff_comp_eq_zero_of_comp_surjective]
  · simp [DFunLike.ext_iff]
  · simp [Prod.fst_surjective]
  · simp [DFunLike.ext_iff]
