/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib

/-!
# Auxiliary theorems about `ContinuousLinearMap`

Mostly about `ContinuousLinearMap.IsInvertible` and `ContinuousLinearMap.inverse`.
-/

open Filter Function Asymptotics Topology

namespace ContinuousLinearMap

namespace IsInvertible

section TVS

variable {R E F : Type*} [Semiring R] [AddCommMonoid E] [Module R E] [AddCommMonoid F] [Module R F]
  [TopologicalSpace E] [TopologicalSpace F] {f : E →L[R] F}

@[simp]
theorem self_comp_inverse (hf : f.IsInvertible) : f ∘L f.inverse = .id _ _ := by
  rcases hf with ⟨e, rfl⟩
  simp

@[simp]
theorem inverse_comp_self (hf : f.IsInvertible) : f.inverse ∘L f = .id _ _ := by
  rcases hf with ⟨e, rfl⟩
  simp

protected theorem bijective (hf : f.IsInvertible) : Bijective f := by
  rcases hf with ⟨e, rfl⟩
  simp [ContinuousLinearEquiv.bijective]

protected theorem injective (hf : f.IsInvertible) : Injective f :=
  hf.bijective.injective

protected theorem surjective (hf : f.IsInvertible) : Surjective f :=
  hf.bijective.surjective

protected theorem inverse (hf : f.IsInvertible) : f.inverse.IsInvertible := by
  rcases hf with ⟨e, rfl⟩
  simp

protected theorem of_isInvertible_inverse (hf : f.inverse.IsInvertible) : f.IsInvertible := by
  by_contra H
  rw [inverse, dif_neg H, isInvertible_zero_iff] at hf
  cases hf
  obtain rfl : f = 0 := Subsingleton.elim _ _
  simp_all [isInvertible_zero_iff]

@[simp]
theorem _root_.ContinuousLinearMap.isInvertible_inverse_iff :
    f.inverse.IsInvertible ↔ f.IsInvertible :=
  ⟨.of_isInvertible_inverse, .inverse⟩

end TVS

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {α : Type*} {l : Filter α}

/-- If a family of continuous linear maps converges to an invertible continuous linear map,
then the maps are eventually invertible as well. -/
protected theorem eventually [CompleteSpace E]
    {f₀ : E →L[𝕜] F} {f : α → E →L[𝕜] F} (hf₀ : f₀.IsInvertible) (hf : Tendsto f l (𝓝 f₀)) :
    ∀ᶠ x in l, (f x).IsInvertible :=
  hf.eventually <| ContinuousLinearEquiv.isOpen.mem_nhds hf₀

end IsInvertible

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {α : Type*} {l : Filter α}

/-- Consider two families of continuous linear maps, `f a` and `g a`.

Suppose that both of them are eventually invertible along a filter `l`,
and the norms of their inverses are bounded.
Then $$f^{-1}_a - g^{-1}_a = O(f_a - g_a)$$. -/
theorem isBigO_inverse_sub_inverse
    {l : Filter α} {f g : α → E →L[𝕜] F}
    (hf_inv : ∀ᶠ a in l, (f a).IsInvertible)
    (hf_bdd : IsBoundedUnder (· ≤ ·) l (fun a ↦ ‖(f a).inverse‖))
    (hg_inv : ∀ᶠ a in l, (g a).IsInvertible)
    (hg_bdd : IsBoundedUnder (· ≤ ·) l (fun a ↦ ‖(g a).inverse‖)) :
    (fun a ↦ (f a).inverse - (g a).inverse) =O[l] (fun a ↦ f a - g a) := calc
  _ =ᶠ[l] fun a ↦ (f a).inverse ∘L (g a - f a) ∘L (g a).inverse := by
    filter_upwards [hf_inv, hg_inv] with a hfa hga
    simp [hfa, hga, ← comp_assoc]
  _ =O[l] fun a ↦ ‖(f a).inverse‖ * ‖g a - f a‖ * ‖(g a).inverse‖ := .of_norm_le fun a ↦ by
    grw [opNorm_comp_le, opNorm_comp_le, mul_assoc]
  _ =O[l] (fun a ↦ f a - g a) := by
    simpa [norm_sub_rev] using (hf_bdd.isBigO_one ℝ).norm_left.mul
      (isBigO_refl (fun a ↦ ‖g a - f a‖) _) |>.mul (hg_bdd.isBigO_one ℝ).norm_left

end ContinuousLinearMap
