import Mathlib.Topology.Algebra.Module.Multilinear.Basic

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

end AddMonoid


variable {ι R : Type*} {E : ι → Type*} {F G : Type*}
    [Ring R] [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)] [∀ i, TopologicalSpace (E i)]
    [AddCommGroup F] [Module R F] [TopologicalSpace F]
    [AddCommGroup G] [Module R G] [TopologicalSpace G]

theorem prod_sub_prod [IsTopologicalAddGroup F] [IsTopologicalAddGroup G]
     (f₁ f₂ : ContinuousMultilinearMap R E F) (g₁ g₂ : ContinuousMultilinearMap R E G) :
    f₁.prod g₁ - f₂.prod g₂ = (f₁ - f₂).prod (g₁ - g₂) :=
  rfl

end ContinuousMultilinearMap
