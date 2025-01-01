import Mathlib.Topology.Algebra.Module.Multilinear.Basic

namespace ContinuousMultilinearMap

section AddMonoid

variable {ι R : Type*} {E : ι → Type*} {F G : Type*}
    [Semiring R] [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)] [∀ i, TopologicalSpace (E i)]
    [AddCommMonoid F] [Module R F] [TopologicalSpace F]
    [AddCommMonoid G] [Module R G] [TopologicalSpace G]

theorem prod_ext_iff {f g : ContinuousMultilinearMap R E (F × G)} :
    f = g ↔ (ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap f =
      (ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap g ∧
      (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap f =
      (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap g := by
  simp [DFunLike.ext_iff, Prod.ext_iff, forall_and]

theorem prod_ext {f g : ContinuousMultilinearMap R E (F × G)}
    (h₁ : (ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap f =
      (ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap g)
    (h₂ : (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap f =
      (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap g) : f = g :=
  prod_ext_iff.mpr ⟨h₁, h₂⟩

theorem eq_prod_iff {f : ContinuousMultilinearMap R E (F × G)}
    {g : ContinuousMultilinearMap R E F} {h : ContinuousMultilinearMap R E G} :
    f = g.prod h ↔ (ContinuousLinearMap.fst _ _ _).compContinuousMultilinearMap f = g ∧
      (ContinuousLinearMap.snd _ _ _).compContinuousMultilinearMap f = h :=
  prod_ext_iff

theorem prod_add_prod [ContinuousAdd F] [ContinuousAdd G] (f₁ f₂ : ContinuousMultilinearMap R E F)
    (g₁ g₂ : ContinuousMultilinearMap R E G) :
    f₁.prod g₁ + f₂.prod g₂ = (f₁ + f₂).prod (g₁ + g₂) :=
  rfl

end AddMonoid


variable {ι R : Type*} {E : ι → Type*} {F G : Type*}
    [Ring R] [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)] [∀ i, TopologicalSpace (E i)]
    [AddCommGroup F] [Module R F] [TopologicalSpace F]
    [AddCommGroup G] [Module R G] [TopologicalSpace G]

theorem prod_sub_prod [TopologicalAddGroup F] [TopologicalAddGroup G]
     (f₁ f₂ : ContinuousMultilinearMap R E F) (g₁ g₂ : ContinuousMultilinearMap R E G) :
    f₁.prod g₁ - f₂.prod g₂ = (f₁ - f₂).prod (g₁ - g₂) :=
  rfl

end ContinuousMultilinearMap
