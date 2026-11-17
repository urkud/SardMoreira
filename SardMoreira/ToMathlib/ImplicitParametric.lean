/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib

/-!
# Implicit function theorem for a parametric family of functions

This file contains material from the `implicit-param` branch of `urkud/mathlib4`
that is not yet in Mathlib `master`:
additions to `Mathlib/LinearAlgebra/Prod.lean`, `Mathlib/Analysis/Calculus/FDeriv/Prod.lean`,
and the new file `Mathlib/Analysis/Calculus/ImplicitFunction/Parametric.lean`.

Implicit function theorem says that a strictly differentiable function
with a surjective Fréchet derivative is conjugate
to a linear projection along the kernel of the derivative.
The smoothness of the conjugating map is the same as the smoothness of the original function.

In Mathlib, the theorem is formalized using an auxiliary structure `ImplicitFunctionData`
that allows us to explicitly choose a linear projection of the domain
onto the kernel of the derivative.

In this file we provide a constructor for `ImplicitFunctionData` that works well
for parametrized families of functions.

Namely, let `f : E × F → G` be a function such that `∂f/∂y` is surjective,
where `∂f/∂y` is defined as the derivative of `fun y ↦ f (x, y)` for a fixed `x`.
Then one can find an implicit function that preserves the first coordinate.

In these settings, we think about this function as a family of functions indexed by `x : X`,
so we can think about this construction as simultaneous application of the implicit function theorem
to all the functions `fun y ↦ f (x, y)` with some extra guarantees
about dependency on the parameter.
-/

@[expose] public noncomputable section

open scoped Topology

/-! ### Additions to `Mathlib/LinearAlgebra/Prod.lean` -/

namespace LinearMap

open Submodule

variable {R M M₂ M₃ : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [Module R M] [Module R M₂] [Module R M₃]

theorem coprod_def (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) :
    f.coprod g = f.comp (fst _ _ _) + g.comp (snd _ _ _) :=
  rfl

section AddCommGroup

variable {N P : Type*} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

theorem map_fst_comap_coprod (f : M →ₗ[R] P) (g : N →ₗ[R] P) (q : Submodule R P) :
    map (fst R M N) (comap (f.coprod g) q) = comap f (g.range ⊔ q) := by
  ext m
  suffices (∃ n, f m + g n ∈ q) ↔ ∃ n, ∃ z ∈ q, g n + z = f m by simpa [mem_sup]
  exact ⟨fun ⟨n, hn⟩ ↦ ⟨-n, f m + g n, hn, by simp⟩,
    fun ⟨n, z, hz, h⟩ ↦ ⟨-n, by simpa [← h] using hz⟩⟩

theorem map_fst_comap (f : M × N →ₗ[R] P) (q : Submodule R P) :
    map (fst R M N) (comap f q) = comap (f ∘ₗ inl R M N) ((f ∘ₗ inr R M N).range ⊔ q) := by
  rw [← map_fst_comap_coprod, coprod_comp_inl_inr]

theorem map_fst_ker (f : M × N →ₗ[R] P) :
    map (fst R M N) f.ker = comap (f ∘ₗ inl R M N) (f ∘ₗ inr R M N).range := by
  rw [ker, map_fst_comap, sup_bot_eq]

theorem map_fst_ker_eq_top {f : M × N →ₗ[R] P} :
    map (fst R M N) f.ker = ⊤ ↔ (f ∘ₗ inl R M N).range ≤ (f ∘ₗ inr R M N).range := by
  rw [map_fst_ker, eq_top_iff, ← map_le_iff_le_comap, Submodule.map_top]

end AddCommGroup

end LinearMap

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

section AddCommMonoid

variable {N : Type*} [AddCommMonoid N] [Module R N]
  {p : Submodule R (M × N)} {q : Submodule R M} {r : Submodule R N}

theorem disjoint_prod_right (hq : Disjoint (p.map (.fst R M N)) q)
    (hr : Disjoint (p.comap (.inr R M N)) r) : Disjoint p (q.prod r) := by
  simp only [disjoint_def, mem_map, mem_comap, mem_prod, LinearMap.fst_apply,
    LinearMap.inr_apply] at *
  rintro ⟨a, b⟩ habp ⟨haq, hbr⟩
  obtain rfl : a = 0 := hq a ⟨(a, b), habp, rfl⟩ haq
  simp [hr b habp hbr]

end AddCommMonoid

section AddCommGroup

variable {N : Type*} [AddCommGroup N] [Module R N]
  {p : Submodule R (M × N)} {q : Submodule R M} {r : Submodule R N}

theorem codisjoint_prod_right (hpq : Codisjoint (p.map (.fst R M N)) q)
    (hpr : Codisjoint (p.comap (.inr R M N)) r) : Codisjoint p (q.prod r) := by
  simp only [Submodule.codisjoint_iff_exists_add_eq, mem_map, mem_comap, mem_prod,
    LinearMap.fst_apply, LinearMap.inr_apply] at *
  rintro ⟨x, y⟩
  rcases hpq x with ⟨_a, c, ⟨⟨a, b⟩, hab, rfl⟩, hcS, rfl⟩
  rcases hpr (y - b) with ⟨d, e, hdp, heq, hde⟩
  use (a, b) + (0, d), (c, e), add_mem hab hdp
  simp [hcS, heq, add_assoc, hde]

theorem isCompl_prod_right (hpq : IsCompl (p.map (.fst R M N)) q)
    (hpr : IsCompl (p.comap (.inr R M N)) r) : IsCompl p (q.prod r) :=
  ⟨disjoint_prod_right hpq.1 hpr.1, codisjoint_prod_right hpq.2 hpr.2⟩

end AddCommGroup

end Submodule

/-! ### Addition to `Mathlib/Analysis/Calculus/FDeriv/Prod.lean` -/

section FDeriv

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem fderiv_fun_comp_prodMk {f : E × F → G} {a : E} {b : F} (hdf : DifferentiableAt 𝕜 f (a, b)) :
    fderiv 𝕜 (fun y ↦ f (a, y)) b = fderiv 𝕜 f (a, b) ∘L .inr 𝕜 E F :=
  hdf.hasFDerivAt.comp b (.prodMk (hasFDerivAt_const _ _) (hasFDerivAt_id _)) |>.fderiv

end FDeriv

/-! ### `Mathlib/Analysis/Calculus/ImplicitFunction/Parametric.lean` -/

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

namespace ImplicitFunctionData

/-- A constructor for `ImplicitFunctionData` that allows us to simultaneously apply the theorem
to an indexed family of functions. -/
@[simps -fullyApplied leftFun leftDeriv pt, simps -isSimp rightFun rightDeriv]
def parametric
    (f : E × F → G) (a : E × F)
    (hfa : HasStrictFDerivAt f (fderiv 𝕜 f a) a)
    (hdf : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).range = ⊤)
    (projKer : F →L[𝕜] (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker)
    (hprojKer : ∀ x : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker, projKer x = x) :
    ImplicitFunctionData 𝕜 (E × F) G (E × (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker) where
  leftFun := f
  leftDeriv := fderiv 𝕜 f a
  hasStrictFDerivAt_leftFun := hfa
  rightFun := Prod.map id projKer
  rightDeriv := .prodMap (.id 𝕜 E) projKer
  hasStrictFDerivAt_rightFun := ContinuousLinearMap.hasStrictFDerivAt (.prodMap (.id 𝕜 E) projKer)
  pt := a
  range_leftDeriv := by
    rw [← top_le_iff, ← hdf, fderiv_fun_comp_prodMk, ContinuousLinearMap.toLinearMap_comp]
    · exact LinearMap.range_comp_le_range _ _
    · exact hfa.hasFDerivAt.differentiableAt
  range_rightDeriv := by simp [LinearMap.range_eq_of_proj hprojKer]
  isCompl_ker := by
    have H : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2 : F →ₗ[𝕜] G) = fderiv 𝕜 f a ∘ₗ .inr 𝕜 E F := by
      simp [fderiv_fun_comp_prodMk hfa.hasFDerivAt.differentiableAt]
    suffices IsCompl (fderiv 𝕜 f a).ker (.prod ⊥ projKer.ker) by simpa [LinearMap.ker_prodMap]
    apply Submodule.isCompl_prod_right
    · convert isCompl_top_bot
      rw [LinearMap.map_fst_ker_eq_top, ← H, hdf]
      apply le_top
    · simpa [H, LinearMap.ker_comp] using projKer.isCompl_of_proj hprojKer

theorem rightDeriv_parametric_apply_ker' {f : E × F → G} {a : E × F}
    (hfa : HasStrictFDerivAt f (fderiv 𝕜 f a) a)
    (hdf : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).range = ⊤)
    (projKer : F →L[𝕜] (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker)
    (hprojKer : ∀ x : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker, projKer x = x)
    (x : E) {y : F} (hy : fderiv 𝕜 (fun z ↦ f (a.1, z)) a.2 y = 0) :
    (parametric f a hfa hdf projKer hprojKer).rightDeriv (x, y) = (x, ⟨y, hy⟩) := by
  simpa [parametric] using hprojKer ⟨y, _⟩

theorem rightDeriv_parametric_apply_ker {f : E × F → G} {a : E × F}
    (hfa : HasStrictFDerivAt f (fderiv 𝕜 f a) a)
    (hdf : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).range = ⊤)
    (projKer : F →L[𝕜] (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker)
    (hprojKer : ∀ x : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker, projKer x = x)
    (x : E) {y : F} (hy : fderiv 𝕜 f a (0, y) = 0) :
    (parametric f a hfa hdf projKer hprojKer).rightDeriv (x, y) =
      (x, ⟨y, by simpa [fderiv_fun_comp_prodMk hfa.hasFDerivAt.differentiableAt]⟩) :=
  rightDeriv_parametric_apply_ker' hfa hdf projKer hprojKer x _

theorem fst_implicitFunction_parametric_eventuallyEq_fst_snd {f : E × F → G} {a : E × F}
    (hfa : HasStrictFDerivAt f (fderiv 𝕜 f a) a)
    (hdf : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).range = ⊤)
    (projKer : F →L[𝕜] (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker)
    (hprojKer : ∀ x : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker, projKer x = x) :
    letI φ := (parametric f a hfa hdf projKer hprojKer).implicitFunction
    (fun z ↦ (φ z.1 z.2).fst) =ᶠ[𝓝 (f a, a.1, projKer a.2)] fun z ↦ z.2.1 := by
  simpa [Filter.EventuallyEq, parametric_rightFun, Prod.map_apply']
    using Filter.EventuallyEq.fun_comp
      (parametric f a hfa hdf projKer hprojKer).rightFun_implicitFunction (·.1)

theorem fst_implicitFunction_parametric_eventuallyEq_fst {f : E × F → G} {a : E × F}
    (hfa : HasStrictFDerivAt f (fderiv 𝕜 f a) a)
    (hdf : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).range = ⊤)
    (projKer : F →L[𝕜] (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker)
    (hprojKer : ∀ x : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker, projKer x = x) :
    letI φ := (parametric f a hfa hdf projKer hprojKer).implicitFunction
    (fun z ↦ (φ (f a) z).fst) =ᶠ[𝓝 (a.1, projKer a.2)] Prod.fst :=
  fst_implicitFunction_parametric_eventuallyEq_fst_snd hfa hdf projKer hprojKer
    |>.comp_tendsto (tendsto_const_nhds.prodMk_nhds Filter.tendsto_id)

theorem apply_implicitFunction_parametric_eventuallyEq_fst {f : E × F → G} {a : E × F}
    (hfa : HasStrictFDerivAt f (fderiv 𝕜 f a) a)
    (hdf : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).range = ⊤)
    (projKer : F →L[𝕜] (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker)
    (hprojKer : ∀ x : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker, projKer x = x) :
    letI φ := (parametric f a hfa hdf projKer hprojKer).implicitFunction
    (fun z ↦ f (φ z.1 z.2)) =ᶠ[𝓝 (f a, a.1, projKer a.2)] Prod.fst := by
  simpa [Filter.EventuallyEq, parametric_rightFun, Prod.map_apply']
    using (parametric f a hfa hdf projKer hprojKer).leftFun_implicitFunction

theorem apply_implicitFunction_parametric_eventuallyEq_const {f : E × F → G} {a : E × F}
    (hfa : HasStrictFDerivAt f (fderiv 𝕜 f a) a)
    (hdf : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).range = ⊤)
    (projKer : F →L[𝕜] (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker)
    (hprojKer : ∀ x : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker, projKer x = x) :
    letI φ := (parametric f a hfa hdf projKer hprojKer).implicitFunction
    (fun z ↦ f (φ (f a) z)) =ᶠ[𝓝 (a.1, projKer a.2)] fun _ ↦ f a :=
  apply_implicitFunction_parametric_eventuallyEq_fst hfa hdf projKer hprojKer
    |>.comp_tendsto (tendsto_const_nhds.prodMk_nhds Filter.tendsto_id)

end ImplicitFunctionData
