import Mathlib
import SardMoreira.ToMathlib.ContinuousLinearMap

open scoped Asymptotics BigOperators

namespace ContinuousMultilinearMap

section AddMonoid

variable {ι R : Type*} {E : ι → Type*} {F G : Type*}
    [Semiring R] [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)] [∀ i, TopologicalSpace (E i)]
    [AddCommMonoid F] [Module R F] [TopologicalSpace F]
    [AddCommMonoid G] [Module R G] [TopologicalSpace G]

theorem prod_add_prod [ContinuousAdd F] [ContinuousAdd G] (f₁ f₂ : ContinuousMultilinearMap R E F)
    (g₁ g₂ : ContinuousMultilinearMap R E G) :
    f₁.prod g₁ + f₂.prod g₂ = (f₁ + f₂).prod (g₁ + g₂) :=
  rfl

theorem compContinuousLinearMap_sum_left {E' : ι → Type*} [∀ i, AddCommMonoid (E' i)]
    [∀ i, Module R (E' i)] [∀ i, TopologicalSpace (E' i)] [ContinuousAdd F]
    {ι' : Type*} (s : Finset ι')
    (f : ι' → ContinuousMultilinearMap R E F) (g : ∀ i, E' i →L[R] E i) :
    (∑ i ∈ s, f i).compContinuousLinearMap g = ∑ i ∈ s, (f i).compContinuousLinearMap g := by
  ext; simp

end AddMonoid

section AddCommGroup

variable {ι R : Type*} {E : ι → Type*} {F G : Type*}
    [Ring R] [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)] [∀ i, TopologicalSpace (E i)]
    [AddCommGroup F] [Module R F] [TopologicalSpace F]
    [AddCommGroup G] [Module R G] [TopologicalSpace G]

theorem prod_sub_prod [IsTopologicalAddGroup F] [IsTopologicalAddGroup G]
     (f₁ f₂ : ContinuousMultilinearMap R E F) (g₁ g₂ : ContinuousMultilinearMap R E G) :
    f₁.prod g₁ - f₂.prod g₂ = (f₁ - f₂).prod (g₁ - g₂) :=
  rfl

@[simp]
theorem compContinuousLinearMap_neg_left {E' : ι → Type*} [∀ i, AddCommGroup (E' i)]
    [∀ i, Module R (E' i)] [∀ i, TopologicalSpace (E' i)] [IsTopologicalAddGroup F]
    (f : ContinuousMultilinearMap R E F) (g : ∀ i, E' i →L[R] E i) :
    (-f).compContinuousLinearMap g = -f.compContinuousLinearMap g := by
  ext; simp

theorem compContinuousLinearMap_sub {E' : ι → Type*} [∀ i, AddCommGroup (E' i)]
    [∀ i, Module R (E' i)] [∀ i, TopologicalSpace (E' i)] [IsTopologicalAddGroup F]
    (f g : ContinuousMultilinearMap R E F) (h : ∀ i, E' i →L[R] E i) :
    (f - g).compContinuousLinearMap h =
      f.compContinuousLinearMap h - g.compContinuousLinearMap h := by
  ext; simp

end AddCommGroup

variable {ι α 𝕜 : Type*} {E F : ι → Type*} {G H : Type*}
  [NontriviallyNormedField 𝕜] [Fintype ι]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace 𝕜 (F i)]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H]

theorem const_apply_sub_const_apply_isBigO (f : ContinuousMultilinearMap 𝕜 E G)
    {g₁ g₂ : α → ∀ i, E i} {B : α → H} {l : Filter α}
    (hg₁ : ∀ i, l.IsBoundedUnder (· ≤ ·) (‖g₁ · i‖))
    (hg₂ : ∀ i, l.IsBoundedUnder (· ≤ ·) (‖g₂ · i‖))
    (hsub : ∀ i, (fun a ↦ g₁ a i - g₂ a i) =O[l] B) :
    (fun a ↦ f (g₁ a) - f (g₂ a)) =O[l] B := by
  refine .trans (.of_norm_le fun _ ↦ norm_image_sub_le _ _ _) ?_
  simp only [← Asymptotics.isBigO_one_iff ℝ, ← Asymptotics.isBigO_pi] at *
  simpa using hg₁.prod_left hg₂ |>.norm_left |>.pow (Fintype.card ι - 1)
    |>.const_mul_left (‖f‖ * Fintype.card ι) |>.mul hsub.norm_norm

@[simp]
theorem compContinuousLinearMapContinuousMultilinear_apply (f : ∀ i, E i →L[𝕜] F i) :
    compContinuousLinearMapContinuousMultilinear 𝕜 E F G f = compContinuousLinearMapL f :=
  rfl

theorem compContinuousLinearMap_sub_compContinuousLinearMap_isBigO
    {f₁ f₂ : α → ContinuousMultilinearMap 𝕜 F G} {g₁ g₂ : α → ∀ i, E i →L[𝕜] F i}
    {l : Filter α} {B : α → H}
    (hf₂_bdd : l.IsBoundedUnder (· ≤ ·) (‖f₂ ·‖))
    (hf_sub : (fun a ↦ f₁ a - f₂ a) =O[l] B)
    (hg₁_bdd : ∀ i, l.IsBoundedUnder (· ≤ ·) (‖g₁ · i‖))
    (hg₂_bdd : ∀ i, l.IsBoundedUnder (· ≤ ·) (‖g₂ · i‖))
    (hg_sub : ∀ i, (fun a ↦ g₁ a i - g₂ a i) =O[l] B) :
    (fun a ↦ (f₁ a).compContinuousLinearMap (g₁ a) -
      (f₂ a).compContinuousLinearMap (g₂ a)) =O[l] B := by
  simp only [← compContinuousLinearMapL_apply, ← compContinuousLinearMapContinuousMultilinear_apply]
  apply ContinuousLinearMap.apply_sub_apply_isBigO
  · simp only [compContinuousLinearMapContinuousMultilinear_apply]
    refine .mono_le ?_ (.of_forall fun _ ↦ norm_compContinuousLinearMapL_le _ _)
    simp only [← Asymptotics.isBigO_one_iff ℝ] at hg₁_bdd
    simpa using Asymptotics.IsBigO.finsetProd fun i (_ : i ∈ Finset.univ) ↦ (hg₁_bdd i).norm_left
  · apply const_apply_sub_const_apply_isBigO
    · exact hg₁_bdd
    · exact hg₂_bdd
    · exact hg_sub
  · exact hf₂_bdd
  · exact hf_sub

end ContinuousMultilinearMap
