import Mathlib
import SardMoreira.ImplicitFunction

open scoped unitInterval Topology NNReal
open Asymptotics Filter Set Metric Function

local notation "dim" => Module.finrank ℝ

namespace ImplicitFunctionData

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

theorem differentiableAt_implicitFunction (φ : ImplicitFunctionData 𝕜 E F G) :
    DifferentiableAt 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt) :=
  φ.hasStrictFDerivAt.to_localInverse.comp (φ.rightFun φ.pt)
    ((hasStrictFDerivAt_const _ _).prodMk (hasStrictFDerivAt_id _))
    |>.hasFDerivAt |>.differentiableAt

theorem fderiv_implicitFunction_apply_eq_iff (φ : ImplicitFunctionData 𝕜 E F G) {x : G} {y : E} :
    fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt) x = y ↔
      φ.leftDeriv y = 0 ∧ φ.rightDeriv y = x := by
  unfold implicitFunction Function.curry toOpenPartialHomeomorph
  simp only [← HasStrictFDerivAt.localInverse_def]
  rw [φ.hasStrictFDerivAt.to_localInverse.comp (φ.rightFun φ.pt)
    ((hasStrictFDerivAt_const _ _).prodMk (hasStrictFDerivAt_id _)) |>.hasFDerivAt |>.fderiv]
  simp [ContinuousLinearEquiv.symm_apply_eq, @eq_comm _ (φ.leftDeriv _),
    @eq_comm _ (φ.rightDeriv _)]

@[simp]
theorem leftDeriv_fderiv_implicitFunction (φ : ImplicitFunctionData 𝕜 E F G) (x : G) :
    φ.leftDeriv (fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt) x) = 0 := by
  exact φ.fderiv_implicitFunction_apply_eq_iff.mp rfl |>.left

@[simp]
theorem rightDeriv_fderiv_implicitFunction (φ : ImplicitFunctionData 𝕜 E F G) (x : G) :
    φ.rightDeriv (fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt) x) = x := by
  exact φ.fderiv_implicitFunction_apply_eq_iff.mp rfl |>.right

theorem map_implicitFunction_nhdsWithin_preimage (φ : ImplicitFunctionData 𝕜 E F G)
    (s : Set E) :
    (𝓝[φ.implicitFunction (φ.leftFun φ.pt) ⁻¹' s] (φ.rightFun φ.pt)).map
      (φ.implicitFunction (φ.leftFun φ.pt)) = 𝓝[s ∩ φ.leftFun ⁻¹' {φ.leftFun φ.pt}] φ.pt := by
  sorry

end ImplicitFunctionData

@[simp]
theorem ContinuousLinearMap.range_eq_bot {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    {f : M →L[R] N} :
    LinearMap.range f = ⊥ ↔ f = 0 :=
  (f : M →ₗ[R] N).range_eq_bot.trans <| by norm_cast -- TODO: make `simp` solve it too

@[simp]
theorem ContinuousLinearMap.ker_prodMap {R M N M' N' : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [AddCommMonoid M'] [Module R M'] [TopologicalSpace M']
    [AddCommMonoid N'] [Module R N'] [TopologicalSpace N']
    (f : M →L[R] N) (g : M' →L[R] N') :
    LinearMap.ker (f.prodMap g) = (LinearMap.ker f).prod (LinearMap.ker g) := by
  ext ⟨_, _⟩; simp

@[simp]
theorem ContinuousLinearMap.range_prodMap {R M N M' N' : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [AddCommMonoid M'] [Module R M'] [TopologicalSpace M']
    [AddCommMonoid N'] [Module R N'] [TopologicalSpace N']
    (f : M →L[R] N) (g : M' →L[R] N') :
    LinearMap.range (f.prodMap g) = (LinearMap.range f).prod (LinearMap.range g) := by
  ext ⟨_, _⟩; simp

@[simp]
theorem ContinuousLinearMap.finrank_range_add_finrank_ker {R M N : Type*} [DivisionRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [FiniteDimensional R M]
    [AddCommGroup N] [Module R N] [TopologicalSpace N]
    (f : M →L[R] N) :
    Module.finrank R (LinearMap.range f) + Module.finrank R (LinearMap.ker f) =
      Module.finrank R M :=
  f.toLinearMap.finrank_range_add_finrank_ker

@[simp]
theorem ContinuousLinearMap.range_id {R M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M] :
    LinearMap.range (ContinuousLinearMap.id R M) = ⊤ := by
  ext; simp

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

namespace Moreira2001

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {k : ℕ} {α : I} {s : Set (E × F)} {a : E × F}  {f : E × F → ℝ}

-- This def almost hits the max heartbeats limit. In fact, I've adjusted the proof to avoid it.
-- Idk what makes the proof so slow.
@[irreducible]
noncomputable def chartImplicitData (f : E × F → ℝ) (a : E × F)
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0) :
    ImplicitFunctionData ℝ (E × F) ℝ (E × LinearMap.ker (fderiv ℝ f a ∘L .inr ℝ E F)) where
  leftFun := f
  leftDeriv := fderiv ℝ f a
  left_has_deriv := hfa.contDiffAt.hasStrictFDerivAt <| by
    simpa only [Nat.one_le_cast, Nat.one_le_iff_ne_zero]
  rightFun := _
  rightDeriv := .prodMap (.id _ _) (Submodule.ClosedComplemented.of_finiteDimensional _).choose
  right_has_deriv := ContinuousLinearMap.hasStrictFDerivAt _
  pt := a
  left_range := by
    refine IsSimpleOrder.eq_bot_or_eq_top _ |>.resolve_left ?_
    rw [ContinuousLinearMap.range_eq_bot]
    contrapose! hdf
    rw [hdf, ContinuousLinearMap.zero_comp]
  right_range := by
    have : LinearMap.range (Submodule.ClosedComplemented.of_finiteDimensional <|
        LinearMap.ker (fderiv ℝ f a ∘L .inr ℝ E F)).choose = ⊤ :=
      LinearMap.range_eq_of_proj (Exists.choose_spec (_ : Submodule.ClosedComplemented _))
    rw [ContinuousLinearMap.range_prodMap, this]
    simp
  isCompl_ker := by
    have H : (LinearMap.ker (fderiv ℝ f a ∘L .inr ℝ E F)).ClosedComplemented :=
      .of_finiteDimensional _
    constructor
    · suffices ∀ x y, fderiv ℝ f a (x, y) = 0 → x = 0 → H.choose y = 0 → y = 0 by
        simpa +contextual only [Subtype.forall, LinearMap.mem_ker, ContinuousLinearMap.coe_comp',
          comp_apply, ContinuousLinearMap.inr_apply, ContinuousLinearMap.ker_prodMap,
          Submodule.disjoint_def, Submodule.mem_prod, ContinuousLinearMap.coe_id', id_eq, and_imp,
          Prod.forall, Prod.mk_eq_zero, true_and]
      rintro _ y hdf rfl hy
      lift y to LinearMap.ker (fderiv ℝ f a ∘L .inr ℝ E F) using by simp [hdf]
      simpa only [H.choose_spec, ZeroMemClass.coe_eq_zero] using hy
    · rw [Submodule.codisjoint_iff_exists_add_eq]
      rintro ⟨x, y⟩
      obtain ⟨z, hz⟩ : ∃ z : F, fderiv ℝ f a (x, z) = 0 := by
        have : LinearMap.range (fderiv ℝ f a ∘L .inr ℝ _ _) = ⊤ := by
          refine IsSimpleOrder.eq_bot_or_eq_top _ |>.resolve_left ?_
          rwa [ContinuousLinearMap.range_eq_bot]
        rw [Submodule.eq_top_iff'] at this
        refine this (-fderiv ℝ f a (x, 0)) |>.imp fun z hz ↦ ?_
        rw [← (x, z).fst_add_snd, map_add]
        simpa [eq_neg_iff_add_eq_zero, add_comm] using hz
      rcases Submodule.codisjoint_iff_exists_add_eq.mp
        (LinearMap.isCompl_of_proj H.choose_spec).codisjoint (y - z)
        with ⟨w, t, hw, ht, hsub⟩
      refine ⟨(x, w + z), (0, t), ?ker, by simpa using ht, ?add⟩
      case ker =>
        rwa [← zero_add x, ← Prod.mk_add_mk, LinearMap.mem_ker, map_add, hz, add_zero]
      case add =>
        rw [Prod.mk_add_mk, add_zero, add_right_comm w z t, hsub, sub_add_cancel]

@[simp]
theorem chartImplicitData_leftFun {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0) :
    (chartImplicitData f a hfa hk hdf).leftFun = f := by
  simp [chartImplicitData]

@[simp]
theorem chartImplicitData_leftDeriv {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0) :
    (chartImplicitData f a hfa hk hdf).leftDeriv = fderiv ℝ f a := by
  simp [chartImplicitData]

@[simp]
theorem chartImplicitData_pt {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0) :
    (chartImplicitData f a hfa hk hdf).pt = a := by
  simp [chartImplicitData]

theorem chartImplicitData_rightDeriv_apply_ker {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0)
    (x : E) {y : F} (hy : fderiv ℝ f a (0, y) = 0) :
    (chartImplicitData f a hfa hk hdf).rightDeriv (x, y) = (x, ⟨y, by simpa⟩) := by
  simpa [chartImplicitData] using
    Submodule.ClosedComplemented.of_finiteDimensional (LinearMap.ker (fderiv ℝ f a ∘L .inr ℝ E F))
      |>.choose_spec ⟨y, by simpa⟩

theorem fderiv_implicitFunction_chartImplicitData_apply_mk_zero {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0)
    (y : LinearMap.ker ((fderiv ℝ f a).comp (ContinuousLinearMap.inr ℝ E F))) :
    fderiv ℝ ((chartImplicitData f a hfa hk hdf).implicitFunction (f a))
      ((chartImplicitData f a hfa hk hdf).rightFun a) (0, y) = (0, y.1) := by
  convert (chartImplicitData f a hfa hk hdf).fderiv_implicitFunction_apply_eq_iff.mpr _
  · simp
  · simp
  · simp
  · constructor
    · cases y with | mk y hy => simpa using hy
    · apply chartImplicitData_rightDeriv_apply_ker
      cases y with | mk y hy => simpa using hy

@[simp]
theorem fderiv_implicitFunction_chartImplicitData_comp_inr {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0) :
    fderiv ℝ ((chartImplicitData f a hfa hk hdf).implicitFunction (f a))
      ((chartImplicitData f a hfa hk hdf).rightFun a) ∘L .inr ℝ E _ =
      .inr ℝ E F ∘L Submodule.subtypeL _ := by
  ext1 x
  simp [fderiv_implicitFunction_chartImplicitData_apply_mk_zero]

theorem fst_implicitFunction_chartImplicitData_eventuallyEq {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0) :
    Prod.fst ∘ (chartImplicitData f a hfa hk hdf).implicitFunction (f a)
      =ᶠ[𝓝 ((chartImplicitData f a hfa hk hdf).rightFun a)] Prod.fst := by
  sorry

theorem exists_chart_ker
    (hfk : ∀ᶠ x in 𝓝[s] a, ContDiffMoreiraHolderAt k α f x) (hf₀ : f =ᶠ[𝓝[s] a] 0)
    (hk : k ≠ 0) (has : a ∈ s) :
    ∃ p : Submodule ℝ F, p = LinearMap.ker (fderiv ℝ f a ∘L .inr ℝ E F) ∧
      ∃ (g : E × p → F) (t : Set (E × p)) (b : E × p),
        (𝓝[t] b).map (Pi.prod Prod.fst g) = 𝓝[s] a ∧
        (∀ᶠ x in 𝓝[t] b, ContDiffMoreiraHolderAt k α g x) ∧
        fderiv ℝ g b ∘L .inr ℝ E p = p.subtypeL := by
  by_cases hdf : fderiv ℝ f a ∘L .inr ℝ E F = 0
  · set p : Submodule ℝ F := ⊤
    refine ⟨p, by ext; simp [p, hdf], p.subtypeL ∘L .snd ℝ _ _,
      (Prod.map id (↑)) ⁻¹' s, (a.1, ⟨a.2, by simp [p]⟩), ?_, ?_, ?_⟩
    · rw [Topology.IsInducing.map_nhdsWithin_eq]
      · simp [Set.image, Prod.ext_iff, p]
      · exact .prodMap .id .subtypeVal
    · refine .of_forall fun x ↦ ?_
      refine ContDiffAt.contDiffMoreiraHolderAt (n := ⊤) ?_ (by simp) α
      exact ((⊤ : Submodule ℝ F).subtypeL ∘L .snd ℝ E (⊤ : Submodule ℝ F)).contDiff.contDiffAt
    · rw [ContinuousLinearMap.fderiv]
      ext
      simp
  · set p := LinearMap.ker (fderiv ℝ f a ∘L .inr ℝ E F)
    use p, rfl
    set ψ := chartImplicitData f a (hfk.self_of_nhdsWithin has) hk hdf
    set b : E × p := ψ.rightFun a
    set g : E × p → F := Prod.snd ∘ ψ.implicitFunction 0
    have hfa₀ : f a = 0 := hf₀.self_of_nhdsWithin has
    have hg_eq : Pi.prod Prod.fst g =ᶠ[𝓝 b] ψ.implicitFunction 0 := by
      refine fst_implicitFunction_chartImplicitData_eventuallyEq
        (hfk.self_of_nhdsWithin has) hk hdf |>.symm |>.mono fun x hx ↦ ?_
      simpa [Prod.ext_iff, b, g, ψ, hfa₀] using hx
    have hnhds : 𝓝[Pi.prod Prod.fst g ⁻¹' s] b = 𝓝[ψ.implicitFunction 0 ⁻¹' s] b := by
      sorry
    refine ⟨g, (Pi.prod Prod.fst g) ⁻¹' s, b, ?_, ?_, ?_⟩
    · sorry
    · sorry
    · simp only [g]
      rw [fderiv_comp, fderiv_snd, ContinuousLinearMap.comp_assoc, ← hfa₀,
        fderiv_implicitFunction_chartImplicitData_comp_inr]
      · ext; simp [p]
      · fun_prop
      · simpa [ψ, hfa₀] using ψ.differentiableAt_implicitFunction
