module

public import Mathlib

@[expose] public section

open Function
open Module (finrank)

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G]
  [AddCommGroup H] [Module ℝ H]


namespace LinearMap

theorem rank_prod_fst (f : E × F →ₗ[ℝ] G) :
    rank (prod (fst ℝ E F) f) = (Module.rank ℝ E).lift + (f ∘ₗ inr ℝ E F).rank.lift := by
  -- The range of the product map is isomorphic
  -- to the direct sum of the ranges of the first projection and the function f.
  have h_range : range (prod (fst ℝ E F) f) ≃ₗ[ℝ] E × range (f ∘ₗ (inr ℝ E F)) := by
    refine LinearEquiv.ofBijective ?_ ⟨?_, ?_⟩;
    · refine prod (fst ℝ _ _ ∘ₗ Submodule.subtype _)
        (codRestrict _ ((snd _ _ _ - f ∘ₗ inl _ _ _ ∘ₗ fst _ _ _) ∘ₗ Submodule.subtype _) ?_)
      rintro ⟨_, ⟨x, y⟩, rfl⟩
      simp [← map_sub]
    · rintro ⟨_, ⟨x, y⟩, rfl⟩ ⟨_, ⟨x', y'⟩, rfl⟩ h
      obtain rfl : x = x' := by simpa using congr($h |>.1)
      simp_all [← Subtype.val_inj]
    · rintro ⟨x, _, y, rfl⟩
      refine ⟨⟨_, (x, y), rfl⟩, ?_⟩
      simp [← Subtype.val_inj, ← map_sub]
  simpa using h_range.lift_rank_eq

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem finrank_range_prod_fst (f : E × F →ₗ[ℝ] G) :
    finrank ℝ (range <| prod (fst ℝ E F) f) =
      Module.finrank ℝ E + finrank ℝ (range <| f ∘ₗ inr ℝ E F) := by
  rw [Module.finrank, ← LinearMap.rank, rank_prod_fst, Cardinal.toNat_add] <;>
    simp [finrank, Module.rank_lt_aleph0]

theorem finrank_range_prod_fst_iff_comp_inr_eq_zero (f : E × F →ₗ[ℝ] G) :
    finrank ℝ (range (prod (fst ℝ E F) f)) = finrank ℝ E ↔ f ∘ₗ inr ℝ E F = 0 := by
  simp [finrank_range_prod_fst, range_eq_bot]

end LinearMap

-- TODO: generalize to semilinear maps
protected noncomputable def ContinuousLinearMap.finrank {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    (f : M →L[R] N) : ℕ :=
  Module.finrank R f.range

theorem ContinuousLinearMap.finrank_comp_eq_left_of_surjective {R M N P : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [AddCommMonoid P] [Module R P] [TopologicalSpace P]
    (g : N →L[R] P) {f : M →L[R] N} (hf : Function.Surjective f) :
    (g ∘L f).finrank = g.finrank := by
  -- Since $f$ is surjective, the image of $g \circ f$ is the same as the image of $g$.
  have h_range : (g.comp f).range = g.range :=
    SetLike.coe_injective <| hf.range_comp g
  rw [ContinuousLinearMap.finrank, ContinuousLinearMap.finrank, h_range]

theorem ContinuousLinearMap.finrank_comp_eq_right_of_injective {R M N P : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [AddCommMonoid P] [Module R P] [TopologicalSpace P]
    {g : N →L[R] P} (hg : Function.Injective g) (f : M →L[R] N) :
    (g ∘L f).finrank = f.finrank := by
  -- Since $g$ is injective, the range of $g \circ f$ is isomorphic to the range of $f$.
  rw [ContinuousLinearMap.finrank, ContinuousLinearMap.finrank,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective (g : N →ₗ[R] P) hg _).finrank_eq.symm

@[simp]
theorem ContinuousLinearEquiv.finrank_comp_left {R M N N' : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [AddCommMonoid N'] [Module R N'] [TopologicalSpace N']
    (e : N ≃L[R] N') (f : M →L[R] N) : (e ∘L f : M →L[R] N').finrank = f.finrank := by
  apply ContinuousLinearMap.finrank_comp_eq_right_of_injective
  exact e.injective

@[simp]
theorem ContinuousLinearEquiv.finrank_comp_right {R M M' N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [AddCommMonoid M'] [Module R M'] [TopologicalSpace M']
    (f : M →L[R] N) (e : M' ≃L[R] M) : (f ∘L e : M' →L[R] N).finrank = f.finrank := by
  apply ContinuousLinearMap.finrank_comp_eq_left_of_surjective
  exact e.surjective
