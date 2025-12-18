import Mathlib

open scoped Topology

@[simps! -fullyApplied apply_coe symm_apply_coe_coe]
def Submodule.continuousEquivSubtypeMap {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [TopologicalSpace M] (p : Submodule R M) (q : Submodule R p) :
    q ≃L[R] q.map p.subtype where
  toLinearEquiv := p.equivSubtypeMap q
  continuous_toFun := .codRestrict (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := .codRestrict (.codRestrict continuous_subtype_val _) _

@[simps!]
def Submodule.topContinuousEquiv {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [TopologicalSpace M] :
    (⊤ : Submodule R M) ≃L[R] M where
  toLinearEquiv := topEquiv
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem ContinuousLinearEquiv.map_nhdsWithin_eq {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    (e : M ≃L[R] N) (s : Set M) (x : M) :
    (𝓝[s] x).map e = 𝓝[e '' s] (e x) :=
  e.toHomeomorph.isInducing.map_nhdsWithin_eq _ _

theorem ContinuousLinearEquiv.map_nhdsWithin_preimage_eq {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    (e : M ≃L[R] N) (s : Set N) (x : M) :
    (𝓝[e ⁻¹' s] x).map e = 𝓝[s] (e x) := by
  rw [e.map_nhdsWithin_eq, e.surjective.image_preimage]

namespace Submodule

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

def prodEquiv
    (s : Submodule R M) (t : Submodule R N) : s.prod t ≃ₗ[R] s × t :=
  { (Equiv.Set.prod (s : Set M) (t : Set N)) with
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

@[simp]
theorem rank_prod_eq_lift [StrongRankCondition R] (s : Submodule R M) (t : Submodule R N)
    [Module.Free R s] [Module.Free R t] :
    Module.rank R (s.prod t) = (Module.rank R s).lift + (Module.rank R t).lift := by
  simp [(s.prodEquiv t).rank_eq]

@[simp]
theorem finrank_prod [StrongRankCondition R] (s : Submodule R M) (t : Submodule R N)
    [Module.Free R s] [Module.Free R t] [Module.Finite R s] [Module.Finite R t] :
    Module.finrank R (s.prod t) = Module.finrank R s + Module.finrank R t := by
  simp [(s.prodEquiv t).finrank_eq]

end Submodule
