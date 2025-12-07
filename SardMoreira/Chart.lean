import Mathlib
import SardMoreira.ImplicitFunction

noncomputable section

open scoped unitInterval Topology NNReal
open Asymptotics Filter Set Metric Function

local notation "dim" => Module.finrank ℝ

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
  have H : φ.implicitFunction (φ.leftFun φ.pt) =
      φ.toOpenPartialHomeomorph.symm ∘ (φ.leftFun φ.pt, ·) := rfl
  rw [H, ← Filter.map_map, (isInducing_prodMkRight _).map_nhdsWithin_eq, ← singleton_prod,
    OpenPartialHomeomorph.map_nhdsWithin_eq, ← prodFun_apply, ← toOpenPartialHomeomorph_coe,
    φ.toOpenPartialHomeomorph.leftInvOn φ.pt_mem_toOpenPartialHomeomorph_source,
    OpenPartialHomeomorph.image_source_inter_eq']
  · conv_rhs =>
      rw [← φ.toOpenPartialHomeomorph.nhdsWithin_source_inter
        φ.pt_mem_toOpenPartialHomeomorph_source]
    congr 1
    ext x
    suffices x ∈ φ.toOpenPartialHomeomorph.source → φ.leftFun x = φ.leftFun φ.pt →
        (φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, φ.rightFun x) ∈ s ↔ x ∈ s) by
      simpa [@and_comm (_ = _)]
    intro hxs hx_eq
    rw [← hx_eq, ← prodFun_apply, ← toOpenPartialHomeomorph_coe,
      φ.toOpenPartialHomeomorph.leftInvOn hxs]
  · exact φ.toOpenPartialHomeomorph.mapsTo φ.pt_mem_toOpenPartialHomeomorph_source

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

@[simp]
theorem ContinuousLinearMap.snd_comp_inr {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N] :
    snd R M N ∘L inr R M N = .id R N :=
  rfl

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

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {k : ℕ} {α : I} {s : Set (E × F)} {a : E × F}  {f : E × F → ℝ}

-- This def almost hits the max heartbeats limit. In fact, I've adjusted the proof to avoid it.
-- Idk what makes the proof so slow.
@[irreducible]
def chartImplicitData (f : E × F → ℝ) (a : E × F)
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
theorem fst_rightFun_chartImplicitData {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0)
    (x : E × F) : ((chartImplicitData f a hfa hk hdf).rightFun x).1 = x.1 := by
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
  have := (continuousAt_const.prodMk continuousAt_id).eventually
    (chartImplicitData f a hfa hk hdf).right_map_implicitFunction
  rw [chartImplicitData_pt] at this
  filter_upwards [this] with x hx
  simpa using congr($hx |>.1)

theorem map_implicitFunction_chartImplicitData_nhdsWithin_preimage {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0)
    (s : Set (E × F)) (hfs : f =ᶠ[𝓝[s] a] 0) (ha : a ∈ s) :
    letI ψ := chartImplicitData f a hfa hk hdf
    (𝓝[ψ.implicitFunction 0 ⁻¹' s] (ψ.rightFun a)).map (ψ.implicitFunction 0) = 𝓝[s] a := by
  set ψ := chartImplicitData f a hfa hk hdf
  convert ψ.map_implicitFunction_nhdsWithin_preimage s using 1
  · simp [ψ, hfs.self_of_nhdsWithin ha]
  · rw [nhdsWithin_inter', inf_of_le_left]
    · congr 1
      simp [ψ]
    · rw [le_principal_iff, chartImplicitData_pt]
      filter_upwards [hfs] with x hx
      simp [ψ, hx, hfs.self_of_nhdsWithin ha]

def IsLargeAt (k : ℕ) (α : I) (s : Set (E × F)) (a : E × F) : Prop :=
  ∀ f : E × F → ℝ, (∀ᶠ x in 𝓝[s] a, ContDiffMoreiraHolderAt k α f x) → f =ᶠ[𝓝[s] a] 0 →
    fderiv ℝ f a ∘L .inr ℝ E F = 0

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
theorem IsLargeAt.comp_continuousLinearEquiv (h : IsLargeAt k α s a) (e : G ≃L[ℝ] F) :
    IsLargeAt k α (Prod.map id e ⁻¹' s) (Prod.map id e.symm a) := by
  intro f hfk hf₀
  set e' := (ContinuousLinearEquiv.refl ℝ E).prodCongr e
  specialize h (f ∘ e'.symm) ?_ ?_
  · rw [← e'.apply_symm_apply a, ← e'.map_nhdsWithin_preimage_eq, eventually_map]
    filter_upwards [hfk] with x hfx
    rw [← e'.symm_apply_apply x] at hfx
    exact hfx.comp' e'.symm.contDiffMoreiraHolderAt (.inr e'.symm.differentiableAt)
  · rw [← e'.apply_symm_apply a, ← e'.map_nhdsWithin_preimage_eq, eventuallyEq_map]
    filter_upwards [hf₀]
    simp
  · rw [e'.symm.comp_right_fderiv] at h
    simpa [DFunLike.ext_iff, e.symm.surjective.forall, e'] using h

structure ChartStep (k : ℕ) (α : I) (s : Set (E × F)) (a : E × F) (ha : a ∈ s) where
  dom : Submodule ℝ F
  pt : E × dom
  toFun : E × dom → E × F
  apply_pt : toFun pt = a
  fst_comp_toFun_eventuallyEq : Prod.fst ∘ toFun =ᶠ[𝓝 pt] Prod.fst
  contDiffMoreiraHolderAt : ∀ᶠ x in 𝓝[toFun ⁻¹' s] pt, ContDiffMoreiraHolderAt k α toFun x
  map_toFun_nhdsWithin : (𝓝[toFun ⁻¹' s] pt).map toFun = 𝓝[s] (toFun pt)
  snd_comp_fderiv_comp_inr : .snd ℝ E F ∘L fderiv ℝ toFun pt ∘L .inr ℝ E dom = dom.subtypeL

namespace ChartStep

attribute [coe] toFun
attribute [simp] apply_pt

instance (ha : a ∈ s) : CoeFun (ChartStep k α s a ha) fun ψ ↦ E × ψ.dom → E × F where
  coe := toFun

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem pt_mem_preimage {ha : a ∈ s} (f : ChartStep k α s a ha) : f.pt ∈ f ⁻¹' s := by
  simpa

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem contDiffMoreiraHolderAt_pt {ha} (f : ChartStep k α s a ha) :
    ContDiffMoreiraHolderAt k α f f.pt :=
  f.contDiffMoreiraHolderAt.self_of_nhdsWithin f.pt_mem_preimage

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem continuousAt_pt {ha} (f : ChartStep k α s a ha) :
    ContinuousAt f f.pt :=
  f.contDiffMoreiraHolderAt_pt.continuousAt

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem differentiableAt_pt {ha} (f : ChartStep k α s a ha) (hk : k ≠ 0) :
    DifferentiableAt ℝ f f.pt :=
  f.contDiffMoreiraHolderAt_pt.differentiableAt hk

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp]
theorem fst_fderiv_apply {ha} (f : ChartStep k α s a ha) (hk : k ≠ 0) (x : E × f.dom) :
    (fderiv ℝ f f.pt x).fst = x.fst := by
  simpa [fderiv_comp, f.differentiableAt_pt hk, fderiv_fst]
    using congr($(f.fst_comp_toFun_eventuallyEq.fderiv_eq (𝕜 := ℝ)) x)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp]
theorem fderiv_mk_zero {ha} (f : ChartStep k α s a ha) (x : f.dom) :
    fderiv ℝ f f.pt (0, x) = (0, x.1) := by
  ext
  · by_cases hdf : DifferentiableAt ℝ f f.pt
    · simpa [fderiv_comp, hdf, fderiv_fst]
        using congr($(f.fst_comp_toFun_eventuallyEq.fderiv_eq (𝕜 := ℝ)) (0, x))
    · simp [fderiv_zero_of_not_differentiableAt hdf]
  · simpa using congr($(f.snd_comp_fderiv_comp_inr) x)

def top (a : E × F) (ha : a ∈ s) : ChartStep k α s a ha where
  dom := ⊤
  pt := (a.1, ⟨a.2, by simp⟩)
  toFun := ContinuousLinearEquiv.prodCongr (.refl ℝ E) Submodule.topContinuousEquiv
  apply_pt := rfl
  fst_comp_toFun_eventuallyEq := .rfl
  contDiffMoreiraHolderAt := .of_forall fun _ ↦ ContinuousLinearEquiv.contDiffMoreiraHolderAt _
  map_toFun_nhdsWithin := by
    rw [← ContinuousLinearEquiv.coe_toHomeomorph, (Homeomorph.isInducing _).map_nhdsWithin_eq,
      Homeomorph.image_preimage]
  snd_comp_fderiv_comp_inr := by
    rw [ContinuousLinearEquiv.fderiv]
    ext
    simp

private theorem kerOfCompInrNeZero_aux₁
    (hfk : ∀ᶠ x in 𝓝[s] a, ContDiffMoreiraHolderAt k α f x) (hf₀ : f =ᶠ[𝓝[s] a] 0)
    (hk : k ≠ 0) (has : a ∈ s) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0) :
    (chartImplicitData f a (hfk.self_of_nhdsWithin has) hk hdf).implicitFunction 0
      ((chartImplicitData f a (hfk.self_of_nhdsWithin has) hk hdf).rightFun a) = a := by
  simpa [hf₀.self_of_nhdsWithin has]
    using chartImplicitData f a (hfk.self_of_nhdsWithin has) hk hdf
      |>.implicitFunction_apply_image.self_of_nhds

def kerOfCompInrNeZero (k : ℕ) (α : I) (s : Set (E × F)) (a : E × F) (f : E × F → ℝ)
    (hfk : ∀ᶠ x in 𝓝[s] a, ContDiffMoreiraHolderAt k α f x) (hf₀ : f =ᶠ[𝓝[s] a] 0)
    (hk : k ≠ 0) (has : a ∈ s) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0) :
    ChartStep k α s a has where
  dom := LinearMap.ker (fderiv ℝ f a ∘L .inr ℝ E F)
  pt := (chartImplicitData f a (hfk.self_of_nhdsWithin has) hk hdf).rightFun a
  toFun := (chartImplicitData f a (hfk.self_of_nhdsWithin has) hk hdf).implicitFunction 0
  apply_pt := kerOfCompInrNeZero_aux₁ hfk hf₀ _ has _
  fst_comp_toFun_eventuallyEq := by
    simpa [hf₀.self_of_nhdsWithin has]
      using fst_implicitFunction_chartImplicitData_eventuallyEq (hfk.self_of_nhdsWithin has) hk hdf
  contDiffMoreiraHolderAt := by
    have := map_implicitFunction_chartImplicitData_nhdsWithin_preimage (hfk.self_of_nhdsWithin has)
      hk hdf s hf₀ has |>.le
    set ψ := chartImplicitData f a (hfk.self_of_nhdsWithin has) hk hdf
    set g := ψ.implicitFunction 0
    have H₀ := map_implicitFunction_chartImplicitData_nhdsWithin_preimage
      (hfk.self_of_nhdsWithin has) hk hdf s hf₀ has
    have H₁ : ∀ᶠ x in 𝓝[g ⁻¹' s] ψ.rightFun a, (0, x) ∈ ψ.toOpenPartialHomeomorph.target := by
      refine .filter_mono inf_le_left ?_
      refine ψ.toOpenPartialHomeomorph.open_target.preimage (by fun_prop) |>.mem_nhds ?_
      simpa [ψ, hf₀.self_of_nhdsWithin has] using ψ.map_pt_mem_toOpenPartialHomeomorph_target
    have H₂ : ∀ᶠ x in 𝓝[s] a, (fderiv ℝ ψ.toOpenPartialHomeomorph x).IsInvertible := by
      refine .filter_mono inf_le_left ?_
      apply ContDiffAt.eventually_isInvertible_fderiv _ _ (n := k) (mod_cast hk)
      · have := hfk.self_of_nhdsWithin has |>.contDiffAt
        simp +unfoldPartialApp [ImplicitFunctionData.prodFun, ψ, chartImplicitData]
        fun_prop
      · have := ψ.hasStrictFDerivAt.hasFDerivAt.fderiv
        rw [chartImplicitData_pt] at this
        rw [ψ.toOpenPartialHomeomorph_coe, this]
        exact ContinuousLinearMap.isInvertible_equiv
    rw [← H₀, eventually_map] at hfk H₂
    filter_upwards [H₁, hfk, H₂] with x hx₁ hx₂ hx₃
    refine (ψ.toOpenPartialHomeomorph.contDiffMoreiraHolderAt_symm hx₁ hx₃ ?_).comp
      (ContDiffAt.contDiffMoreiraHolderAt (by fun_prop) (WithTop.coe_lt_top _) α) hk
    refine .prodMk (by simpa [ψ] using hx₂) ?_
    simp only [ψ, chartImplicitData]
    exact ContDiffAt.contDiffMoreiraHolderAt (by fun_prop) (WithTop.coe_lt_top _) α
  map_toFun_nhdsWithin := by
    set ψ := chartImplicitData f a (hfk.self_of_nhdsWithin has) hk hdf
    rw [map_implicitFunction_chartImplicitData_nhdsWithin_preimage, kerOfCompInrNeZero_aux₁]
    all_goals assumption
  snd_comp_fderiv_comp_inr := by
    have : f a = 0 := hf₀.self_of_nhdsWithin has
    rw [← this, fderiv_implicitFunction_chartImplicitData_comp_inr,
      ← ContinuousLinearMap.comp_assoc, ContinuousLinearMap.snd_comp_inr,
      ContinuousLinearMap.id_comp]

@[simp]
theorem kerOfCompInrNeZero_apply_pt
    (hfk : ∀ᶠ x in 𝓝[s] a, ContDiffMoreiraHolderAt k α f x) (hf₀ : f =ᶠ[𝓝[s] a] 0)
    (hk : k ≠ 0) (has : a ∈ s) (hdf : fderiv ℝ f a ∘L .inr ℝ E F ≠ 0) :
    kerOfCompInrNeZero k α s a f hfk hf₀ hk has hdf
      (kerOfCompInrNeZero k α s a f hfk hf₀ hk has hdf).pt = a := by
  apply kerOfCompInrNeZero_aux₁ <;> assumption

protected def comp {ha} (g : ChartStep k α s a ha)
    (f : ChartStep k α (g ⁻¹' s) g.pt g.pt_mem_preimage) (hk : k ≠ 0) :
    ChartStep k α s a ha := by
  set e := (ContinuousLinearEquiv.refl ℝ E).prodCongr (g.dom.continuousEquivSubtypeMap f.dom)
  have he₁ : ∀ x, (e x).fst = x.fst := fun _ ↦ rfl
  refine
    { dom := f.dom.map g.dom.subtype
      pt := e f.pt
      toFun := g ∘ f ∘ e.symm
      apply_pt := ?_
      fst_comp_toFun_eventuallyEq := ?_
      contDiffMoreiraHolderAt := ?_
      map_toFun_nhdsWithin := ?_
      snd_comp_fderiv_comp_inr := ?_ }
  · simp
  · rw [← e.map_nhds_eq, eventuallyEq_map]
    have hg : Prod.fst ∘ g ∘ f =ᶠ[𝓝 f.pt] Prod.fst ∘ f := by
      have := g.fst_comp_toFun_eventuallyEq
      rw [← f.apply_pt] at this
      exact f.continuousAt_pt.eventually this
    filter_upwards [f.fst_comp_toFun_eventuallyEq, hg] with x hfx hgx
    simp_all
  · simp only [← e.map_nhdsWithin_preimage_eq, eventually_map]
    have hg := g.contDiffMoreiraHolderAt
    rw [← f.apply_pt] at hg
    filter_upwards [f.contDiffMoreiraHolderAt,
      (f.continuousAt_pt.continuousWithinAt.tendsto_nhdsWithin <| by simp [MapsTo]).eventually hg]
      with x hfx hgx
    rw [← e.symm_apply_apply x] at hfx hgx
    exact hgx.comp hfx hk |>.comp e.symm.contDiffMoreiraHolderAt hk
  · rw [← Filter.map_map, ← Filter.map_map, e.symm.map_nhdsWithin_eq, preimage_comp, preimage_comp,
      e.symm.surjective.image_preimage, e.symm_apply_apply, f.map_toFun_nhdsWithin, f.apply_pt,
      g.map_toFun_nhdsWithin]
    simp
  · ext x
    rw [fderiv_comp, ContinuousLinearEquiv.comp_right_fderiv]
    · have : e.symm (0, x) = (0, (g.dom.continuousEquivSubtypeMap f.dom).symm x) := rfl
      simp [this]
    · simpa using g.differentiableAt_pt hk
    · exact f.differentiableAt_pt hk |>.comp _ e.symm.differentiableAt

theorem exists_isLargeAt {k : ℕ} (α : I) {s : Set (E × F)} {a : E × F} (hk : k ≠ 0) (ha : a ∈ s) :
    ∃ f : ChartStep k α s a ha, IsLargeAt k α (f ⁻¹' s) f.pt := by
  induction hF : dim F using Nat.strongRecOn generalizing F with | ind d ihd => ?_
  by_cases hlarge : IsLargeAt k α s a
  · exact ⟨.top a ha, hlarge.comp_continuousLinearEquiv Submodule.topContinuousEquiv⟩
  · rw [IsLargeAt] at hlarge
    push_neg at hlarge
    rcases hlarge with ⟨f, hfk, hf₀, hdf⟩
    set ψ := kerOfCompInrNeZero k α s a f hfk hf₀ hk ha hdf
    have : dim ψ.dom < d := by
      simpa only [ψ, kerOfCompInrNeZero, ← hF,
        ← (fderiv ℝ f a ∘L .inr ℝ E F).finrank_range_add_finrank_ker, lt_add_iff_pos_left,
        pos_iff_ne_zero, ne_eq, Submodule.finrank_eq_zero, ContinuousLinearMap.range_eq_bot]
    rcases ihd (dim ψ.dom) this ψ.pt_mem_preimage rfl with ⟨g, hg_large⟩
    use ψ.comp g hk
    exact hg_large.comp_continuousLinearEquiv (ψ.dom.continuousEquivSubtypeMap g.dom).symm

def ofLE {ha} (ψ : ChartStep k α s a ha) (l : ℕ) (hl : l ≤ k) : ChartStep l α s a ha where
  __ := ψ
  contDiffMoreiraHolderAt := ψ.contDiffMoreiraHolderAt.mono fun _x hx ↦ hx.of_le hl

theorem isBigO_sub_rev {ha} (ψ : ChartStep k α s a ha) (hk : k ≠ 0) :
    (fun x ↦ x.1 - x.2) =O[𝓝 (ψ.pt, ψ.pt)] (fun x ↦ ψ x.1 - ψ x.2) := by
  set ψ' := fderiv ℝ ψ ψ.pt
  suffices Injective ψ' by
    rcases ψ'.antilipschitz_of_injective_of_isClosed_range this
      (LinearMap.coe_range ψ' ▸ Submodule.closed_of_finiteDimensional _) with ⟨C, hC⟩
    have : (fun x ↦ x.1 - x.2) =O[𝓝 (ψ.pt, ψ.pt)] (fun x ↦ ψ' (x.1 - x.2)) := by
      refine .of_bound C <| .of_forall fun x ↦ ?_
      convert ZeroHomClass.bound_of_antilipschitz ψ' hC (x.1 - x.2)
    refine this.trans ?_
    refine ψ.contDiffMoreiraHolderAt_pt.contDiffAt.hasStrictFDerivAt
      (by simpa [Nat.one_le_iff_ne_zero])
      |>.isLittleO |>.trans_isBigO this |>.right_isBigO_add |>.congr (fun _ ↦ rfl) ?_
    simp [ψ']
  rw [injective_iff_map_eq_zero]
  rintro ⟨x, y⟩ h
  obtain rfl : x = 0 := by simpa [ψ', hk] using congr(Prod.fst $h)
  simpa [ψ'] using h

theorem isBigO_sub_rev_of_tendsto {β : Type*} {l : Filter β} {ha} (ψ : ChartStep k α s a ha)
    (hk : k ≠ 0) {f g : β → E × ψ.dom} (hf : Tendsto f l (𝓝 ψ.pt)) (hg : Tendsto g l (𝓝 ψ.pt)) :
    (fun x ↦ f x - g x) =O[l] (fun x ↦ ψ (f x) - ψ (g x)) := by
  exact ψ.isBigO_sub_rev hk |>.comp_tendsto (hf.prodMk_nhds hg)

end ChartStep

def chartChain {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (k : ℕ) (hk : k ≠ 0) (α : I) (s : Set (E × F)) (a : E × F) (ha : a ∈ s) :
    ChartStep 1 α s a ha :=
  match k, hk with
  | 1, _ =>
    (ChartStep.exists_isLargeAt α one_ne_zero ha).choose
  | l + 2, hl =>
    have H := ChartStep.exists_isLargeAt α hl ha
    let ψ := H.choose
    let φ := chartChain (l + 1) l.succ_ne_zero α (ψ ⁻¹' s) ψ.pt ψ.pt_mem_preimage
    (ψ.ofLE _ (by simp)).comp φ one_ne_zero
