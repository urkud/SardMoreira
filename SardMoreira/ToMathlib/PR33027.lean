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

end IsInvertible

end ContinuousLinearMap
