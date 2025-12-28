import Mathlib
import SardMoreira.ImplicitFunction
import SardMoreira.LocalEstimates

noncomputable section

open scoped unitInterval Topology NNReal
open Asymptotics Filter Set Metric Function

local notation "dim" => Module.finrank ℝ

@[simp]
theorem ContinuousLinearMap.coe_eq_zero {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N] {f : M →L[R] N} :
    (f : M →ₗ[R] N) = 0 ↔ f = 0 := by
  norm_cast

@[simp]
theorem LinearMap.range_prodMap {R M N M' N' : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    [AddCommMonoid M'] [Module R M']
    [AddCommMonoid N'] [Module R N']
    (f : M →ₗ[R] N) (g : M' →ₗ[R] N') :
    (f.prodMap g).range = f.range.prod g.range := by
  ext ⟨_, _⟩; simp

theorem Submodule.isCompl_bot_prod_right {R E F : Type*}
    [Semiring R] [AddCommMonoid E] [Module R E] [AddCommGroup F] [Module R F]
    (p : Submodule R (E × F)) (q : Submodule R F)
    (hp_left : p.map (.fst R E F) = ⊤)
    (hpq : IsCompl (p.comap (.inr R E F)) q) : IsCompl p (.prod ⊥ q) := by
  constructor
  · rcases hpq with ⟨hpq, -⟩
    aesop (add simp Submodule.disjoint_def)
  · rw [Submodule.codisjoint_iff_exists_add_eq]
    replace hp_left : ∀ (x : E), ∃ y, (x, y) ∈ p := by simpa [Submodule.eq_top_iff'] using hp_left
    rintro ⟨x, y⟩
    rcases hp_left x with ⟨z, hz⟩
    rcases Submodule.codisjoint_iff_exists_add_eq.mp hpq.2 (y - z) with ⟨w, t, hw, ht, hwt⟩
    rw [Submodule.mem_comap, LinearMap.inr_apply] at hw
    use (x, z) + (0, w), (0, t), add_mem hz hw
    simp [ht, add_assoc, hwt]

theorem LinearMap.map_fst_ker_eq_top {R E F G : Type*}
    [Semiring R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G] {f : E × F →ₗ[R] G} :
    f.ker.map (.fst R E F) = ⊤ ↔ (f ∘ₗ .inl R E F).range ≤ (f ∘ₗ .inr R E F).range := by
  simp [Submodule.eq_top_iff', SetLike.le_def]
  rw [neg_surjective.forall]
  simp only [← sub_eq_zero (b := f _), ← map_sub]
  simp

@[simps -fullyApplied leftFun leftDeriv pt]
def ImplicitFunctionData.parametric {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
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
    rw [← top_le_iff, ← hdf, fderiv_comp_prodMk', ContinuousLinearMap.coe_comp]
    · exact LinearMap.range_comp_le_range _ _
    · exact hfa.hasFDerivAt.differentiableAt
  range_rightDeriv := by
    have projKer_range : projKer.range = ⊤ :=
      LinearMap.range_eq_of_proj hprojKer
    simp [projKer_range]
  isCompl_ker := by
    have H := congr($(fderiv_comp_prodMk' hfa.hasFDerivAt.differentiableAt).toLinearMap)
    push_cast at H
    suffices IsCompl (fderiv 𝕜 f a).ker (.prod ⊥ projKer.ker) by simpa [LinearMap.ker_prodMap]
    apply Submodule.isCompl_bot_prod_right
    · rw [LinearMap.map_fst_ker_eq_top, ← H, hdf]
      apply le_top
    · simpa [H] using projKer.isCompl_of_proj hprojKer

theorem ImplicitFunctionData.rightDeriv_parametric_apply_ker'
    {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
    (f : E × F → G) (a : E × F)
    (hfa : HasStrictFDerivAt f (fderiv 𝕜 f a) a)
    (hdf : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).range = ⊤)
    (projKer : F →L[𝕜] (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker)
    (hprojKer : ∀ x : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker, projKer x = x)
    (x : E) {y : F} (hy : fderiv 𝕜 (fun z ↦ f (a.1, z)) a.2 y = 0) :
    (parametric f a hfa hdf projKer hprojKer).rightDeriv (x, y) = (x, ⟨y, hy⟩) := by
  simpa [parametric] using hprojKer ⟨y, _⟩

theorem ImplicitFunctionData.rightDeriv_parametric_apply_ker
    {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
    (f : E × F → G) (a : E × F)
    (hfa : HasStrictFDerivAt f (fderiv 𝕜 f a) a)
    (hdf : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).range = ⊤)
    (projKer : F →L[𝕜] (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker)
    (hprojKer : ∀ x : (fderiv 𝕜 (fun y ↦ f (a.1, y)) a.2).ker, projKer x = x)
    (x : E) {y : F} (hy : fderiv 𝕜 f a (0, y) = 0) :
    (parametric f a hfa hdf projKer hprojKer).rightDeriv (x, y) =
      (x, ⟨y, by simpa [fderiv_comp_prodMk' hfa.hasFDerivAt.differentiableAt]⟩) :=
  rightDeriv_parametric_apply_ker' f a hfa hdf projKer hprojKer x _

namespace Moreira2001

section
universe x u v w
variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {k : ℕ} {α : I} {s : Set (E × F)} {a : E × F}  {f : E × F → ℝ}

@[simps! -fullyApplied leftFun leftDeriv rightFun_fst pt]
def chartImplicitData (f : E × F → ℝ) (a : E × F)
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0)
    (hdf : fderiv ℝ (fun y ↦ f (a.1, y)) a.2 ≠ 0) :
    ImplicitFunctionData ℝ (E × F) ℝ (E × (fderiv ℝ (fun y ↦ f (a.1, y)) a.2).ker) := by
  refine .parametric f a (hfa.contDiffAt.hasStrictFDerivAt (mod_cast hk)) ?_
    (Submodule.ClosedComplemented.of_finiteDimensional _).choose
    (Submodule.ClosedComplemented.of_finiteDimensional _).choose_spec
  refine (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left ?_
  simpa [LinearMap.range_eq_bot]

theorem chartImplicitData_rightDeriv_apply_ker {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0)
    (hdf : fderiv ℝ (fun y ↦ f (a.1, y)) a.2 ≠ 0) (x : E) {y : F} (hy : fderiv ℝ f a (0, y) = 0) :
    (chartImplicitData f a hfa hk hdf).rightDeriv (x, y) =
      (x, ⟨y, by simpa [fderiv_comp_prodMk' (hfa.differentiableAt hk)]⟩) := by
  apply ImplicitFunctionData.rightDeriv_parametric_apply_ker
  exact hy

theorem fderiv_implicitFunction_chartImplicitData_apply_mk_zero {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0)
    (hdf : fderiv ℝ (fun y ↦ f (a.1, y)) a.2 ≠ 0)
    (y : (fderiv ℝ (fun y ↦ f (a.1, y)) a.2).ker) :
    fderiv ℝ ((chartImplicitData f a hfa hk hdf).implicitFunction (f a))
      ((chartImplicitData f a hfa hk hdf).rightFun a) (0, y) = (0, y.1) := by
  convert (chartImplicitData f a hfa hk hdf).fderiv_implicitFunction_apply_eq_iff.mpr _
  suffices fderiv ℝ f a (0, y) = 0 by
    simpa [chartImplicitData, ImplicitFunctionData.rightDeriv_parametric_apply_ker']
  simpa [fderiv_comp_prodMk' (hfa.differentiableAt hk)] using y.2

@[simp]
theorem fderiv_implicitFunction_chartImplicitData_comp_inr {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ (fun y ↦ f (a.1, y)) a.2 ≠ 0) :
    fderiv ℝ ((chartImplicitData f a hfa hk hdf).implicitFunction (f a))
      ((chartImplicitData f a hfa hk hdf).rightFun a) ∘L .inr ℝ E _ =
      .inr ℝ E F ∘L Submodule.subtypeL _ := by
  ext1 x
  have := fderiv_implicitFunction_chartImplicitData_apply_mk_zero hfa hk hdf x
  simp_all -- Need a `simp_all` because `simp` simplifies in the type of `x`

theorem fst_implicitFunction_chartImplicitData_eventuallyEq {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ (fun y ↦ f (a.1, y)) a.2 ≠ 0) :
    Prod.fst ∘ (chartImplicitData f a hfa hk hdf).implicitFunction (f a)
      =ᶠ[𝓝 ((chartImplicitData f a hfa hk hdf).rightFun a)] Prod.fst := by
  have := (continuousAt_const.prodMk continuousAt_id).eventually
    (chartImplicitData f a hfa hk hdf).right_map_implicitFunction
  rw [chartImplicitData_pt] at this
  filter_upwards [this] with x hx
  simpa using congr($hx |>.1)

theorem map_implicitFunction_chartImplicitData_nhdsWithin_preimage {f : E × F → ℝ} {a : E × F}
    (hfa : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) (hdf : fderiv ℝ (fun y ↦ f (a.1, y)) a.2 ≠ 0)
    (s : Set (E × F)) (hfs : f =ᶠ[𝓝[s] a] 0) (ha : a ∈ s) :
    letI ψ := chartImplicitData f a hfa hk hdf
    (𝓝[ψ.implicitFunction 0 ⁻¹' s] (ψ.rightFun a)).map (ψ.implicitFunction 0) = 𝓝[s] a := by
  set ψ := chartImplicitData f a hfa hk hdf
  convert ψ.map_implicitFunction_nhdsWithin_preimage s using 1
  · simp [ψ, hfs.self_of_nhdsWithin ha]
  · rw [nhdsWithin_inter', inf_of_le_left, chartImplicitData_pt]
    rw [le_principal_iff, chartImplicitData_pt]
    filter_upwards [hfs] with x hx
    simp [ψ, hx, hfs.self_of_nhdsWithin ha]

def IsLargeAt (k : ℕ) (α : I) (s : Set (E × G)) (a : E × G) : Prop :=
  ∀ f : E × G → ℝ, (∀ᶠ x in 𝓝[s] a, ContDiffMoreiraHolderAt k α f x) → f =ᶠ[𝓝[s] a] 0 →
    fderiv ℝ (fun y ↦ f (a.1, y)) a.2 = 0

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
/-- Definition of `IsLargeAt` talks about `f : E × F → ℝ` only,
but it implies a similar statement for any codomain. -/
theorem IsLargeAt.fderiv_comp_prodMk_eq_zero (h : IsLargeAt k α s a) {f : E × F → G}
    (hf : ∀ᶠ x in 𝓝[s] a, ContDiffMoreiraHolderAt k α f x) (hf₀ : f =ᶠ[𝓝[s] a] 0) :
    fderiv ℝ (fun y ↦ f (a.1, y)) a.2 = 0 := by
  by_cases hfa : DifferentiableAt ℝ (fun y ↦ f (a.1, y)) a.2
  · unfold IsLargeAt at h
    contrapose! h
    rcases ContinuousLinearMap.exists_ne_zero h with ⟨x, hx⟩
    rcases exists_dual_vector ℝ _ hx with ⟨g, hg₁, hgx⟩
    refine ⟨g ∘ f, hf.mono fun x hx ↦ hx.continuousLinearMap_comp g,
      hf₀.mono <| by simp +contextual, ?_⟩
    rw [Function.comp_def, fderiv_comp' _ (by fun_prop) hfa]
    apply ne_of_apply_ne (· x)
    simp_all
  · simp [fderiv_zero_of_not_differentiableAt hfa]

structure Chart (k : ℕ) (α : I) (s : Set (E × F)) where
  Dom : Type v
  [instNormedAddCommGroupDom : NormedAddCommGroup Dom]
  [instNormedSpaceDom : NormedSpace ℝ Dom]
  [instFiniteDimensional : FiniteDimensional ℝ Dom]
  toFun : E × Dom → E × F
  set : Set (E × Dom)
  fst_apply (x) : (toFun x).fst = x.fst
  contDiffMoreiraHolderAt {x} : x ∈ set → ContDiffMoreiraHolderAt k α toFun x
  injective_fderiv {x} : x ∈ set → Injective (fderiv ℝ toFun x)
  finrank_le : dim Dom ≤ dim F
  mapsTo : MapsTo toFun set s

namespace Chart

attribute [instance] instNormedAddCommGroupDom instNormedSpaceDom instFiniteDimensional
attribute [coe] toFun
attribute [simp] fst_apply

instance : CoeFun (Chart k α s) fun ψ ↦ E × ψ.Dom → E × F where
  coe := toFun

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp] theorem prodMk_fst_snd_apply (φ : Chart k α s) (x : E × φ.Dom) :
    (x.1, (φ x).2) = φ x := by
  ext <;> simp

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp] theorem prodMk_snd_apply_mk (φ : Chart k α s) (x : E) (y : φ.Dom) :
    (x, (φ (x, y)).snd) = φ (x, y) := by
  ext <;> simp

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem continuousAt (f : Chart k α s) {x : E × f.Dom} (hx : x ∈ f.set) :
    ContinuousAt f x :=
  f.contDiffMoreiraHolderAt hx |>.continuousAt

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem contDiffAt (f : Chart k α s) {x : E × f.Dom} (hx : x ∈ f.set) :
    ContDiffAt ℝ k f x :=
  f.contDiffMoreiraHolderAt hx |>.contDiffAt

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem eventually_differentiableAt (f : Chart k α s) {x : E × f.Dom} (hx : x ∈ f.set)
      (hk : k ≠ 0) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
  f.contDiffAt hx |>.eventually (by simp) |>.mono fun y hy ↦
    hy.differentiableAt (by simpa [Nat.one_le_iff_ne_zero])

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem differentiableAt (f : Chart k α s) (hk : k ≠ 0) {x : E × f.Dom} (hx : x ∈ f.set) :
    DifferentiableAt ℝ f x :=
  f.contDiffMoreiraHolderAt hx |>.differentiableAt hk

@[simps -fullyApplied]
protected def id : Chart k α s where
  Dom := F
  toFun := id
  set := s
  fst_apply _ := rfl
  contDiffMoreiraHolderAt _ := .id
  injective_fderiv := by simp [injective_id]
  finrank_le := le_rfl
  mapsTo := mapsTo_id _

instance : Inhabited (Chart k α s) := ⟨.id⟩

theorem exists_dim_lt_map_nhdsWithin_eq (hs : ¬IsLargeAt k α s a)
    (hk : k ≠ 0) (has : a ∈ s) :
    ∃ (ψ : Chart k α s) (pt : E × ψ.Dom),
      dim ψ.Dom < dim F ∧ pt ∈ ψ.set ∧ map ψ (𝓝[ψ.set] pt) = 𝓝[s] a := by
  unfold IsLargeAt at hs
  push_neg at hs
  rcases hs with ⟨f, hfk, hf₀, hdf⟩
  set ψ := chartImplicitData f a (hfk.self_of_nhdsWithin has) hk hdf
  set g := ψ.implicitFunction 0
  have hae : a ∈ ψ.toOpenPartialHomeomorph.source := by
    simpa [ψ] using ψ.pt_mem_toOpenPartialHomeomorph_source
  have hfa₀ : f a = 0 := hf₀.self_of_nhdsWithin has
  have hfka : ContDiffMoreiraHolderAt k α f a := hfk.self_of_nhdsWithin has
  have hga : g (ψ.rightFun a) = a := by
    simpa [g, ψ, hfa₀] using ψ.implicitFunction_apply_image.self_of_nhds
  have hg_tendsto : Tendsto g (𝓝 (ψ.rightFun a)) (𝓝 a) := by
    convert ψ.differentiableAt_implicitFunction.continuousAt.tendsto
    · simp [ψ, hfa₀]
    · simpa [ψ] using ψ.implicitFunction_apply_image.self_of_nhds.symm
  have Hmem_target : ∀ᶠ x in 𝓝 (ψ.rightFun a), (0, x) ∈ ψ.toOpenPartialHomeomorph.target := by
    refine (ψ.toOpenPartialHomeomorph.open_target.preimage (by fun_prop)).eventually_mem ?_
    simpa [ψ, hfa₀] using ψ.toOpenPartialHomeomorph.mapsTo hae
  have Hfst : ∀ᶠ x in 𝓝 (ψ.rightFun a), (g x).fst = x.fst := by
    simpa [g, ψ, EventuallyEq, hfa₀]
      using fst_implicitFunction_chartImplicitData_eventuallyEq hfka hk hdf
  have Hderiv_right : ∀ᶠ x in 𝓝 (ψ.rightFun a), fderiv ℝ (fun y ↦ f ((g x).1, y)) (g x).2 ≠ 0 := by
    apply Filter.Tendsto.eventually_ne _ hdf
    refine .comp (g := fun z ↦ fderiv ℝ (fun y ↦ f (z.1, y)) z.2) ?_ hg_tendsto
    exact hfka.fderiv₂ (Nat.pos_iff_ne_zero.mpr hk) |>.continuousAt
  have HisInvertible : ∀ᶠ x in 𝓝 (ψ.rightFun a), (fderiv ℝ ψ.prodFun (g x)).IsInvertible := by
    suffices (fderiv ℝ ψ.prodFun ψ.pt).IsInvertible by
      simp only [ψ, chartImplicitData_pt] at this
      apply this.eventually
      refine (ContDiffAt.continuousAt_fderiv ?_ (n := k) (mod_cast hk)).tendsto.comp hg_tendsto
      simp +unfoldPartialApp only [ψ, ImplicitFunctionData.prodFun, chartImplicitData]
      exact hfka.contDiffAt.prodMk (by fun_prop)
    rw [ψ.hasStrictFDerivAt.hasFDerivAt.fderiv]
    apply ContinuousLinearMap.isInvertible_equiv
  have HcontDiff : ∀ᶠ x in 𝓝 (ψ.rightFun a), (g x ∈ s → ContDiffMoreiraHolderAt k α g x) := by
    rw [← map_implicitFunction_chartImplicitData_nhdsWithin_preimage hfka hk hdf s hf₀ has,
      eventually_map, eventually_nhdsWithin_iff] at hfk
    filter_upwards [Hmem_target, HisInvertible, hfk] with x hx₁ hx₂ hx₃ hgx
    suffices ContDiffMoreiraHolderAt k α ψ.toOpenPartialHomeomorph.symm (0, x) from
      this.comp (.prodMk .const .id) hk
    apply OpenPartialHomeomorph.contDiffMoreiraHolderAt_symm _ hx₁ hx₂
    convert (hx₃ hgx).prodMk _ using 4
    exact ψ.rightDeriv.contDiffMoreiraHolderAt
  rcases _root_.eventually_nhds_iff.mp (Hmem_target.and <| Hfst.and <| Hderiv_right.and <|
    HisInvertible.and HcontDiff) with ⟨U, hU, hUo, hUmem⟩
  choose hU_target hU_fst hUcomp_inr hUinv hUk using hU
  refine ⟨⟨_, fun x ↦ (x.1, (g x).2), U ∩ g ⁻¹' s, fun _ ↦ rfl, ?_, ?_, ?_, ?_⟩, ψ.rightFun a,
    ?_, ?_, ?_⟩
  · rintro x ⟨hxU, hxs⟩
    exact .prodMk .fst <| .comp .snd (hUk _ hxU hxs) hk
  · rintro x ⟨hxU, hgx⟩
    have : (fun y ↦ (y.1, (g y).2)) =ᶠ[𝓝 x] g := by
      filter_upwards [hUo.eventually_mem hxU] with y hyU
      rw [← hU_fst y hyU]
    rw [this.fderiv_eq]
    have : fderiv ℝ g x = _ :=
      ψ.toOpenPartialHomeomorph.hasFDerivAt_symm_inverse (hU_target x hxU) (hUinv x hxU)
      |>.comp x
        (ContinuousLinearMap.inr ℝ ℝ (E × (fderiv ℝ (fun y ↦ f (a.1, y)) a.2).ker)).hasFDerivAt
        |>.fderiv
    rw [this, ContinuousLinearMap.coe_comp']
    apply Injective.comp
    · exact (hUinv _ hxU).inverse.injective
    · simp [Injective]
  · exact Submodule.finrank_le _
  · rintro x ⟨hxU, hgx⟩
    simpa only [← hU_fst x hxU]
  · apply Submodule.finrank_lt
    simpa [SetLike.ext_iff, DFunLike.ext_iff] using hdf
  · simp [*]
  · simp only
    rw [← map_implicitFunction_chartImplicitData_nhdsWithin_preimage hfka hk hdf _ hf₀ has,
      nhdsWithin_inter_of_mem]
    · apply Filter.map_congr
      filter_upwards [mem_nhdsWithin_of_mem_nhds <| hUo.mem_nhds hUmem] with x hxU
      rw [← hU_fst x hxU]
    · exact mem_nhdsWithin_of_mem_nhds <| hUo.mem_nhds hUmem

@[simps -fullyApplied]
protected def comp (g : Chart k α s) (f : Chart k α g.set) (hk : k ≠ 0) :
    Chart k α s where
  Dom := f.Dom
  toFun := g ∘ f
  set := f.set
  fst_apply := by simp
  contDiffMoreiraHolderAt {x} hx :=
    g.contDiffMoreiraHolderAt (f.mapsTo hx) |>.comp (f.contDiffMoreiraHolderAt hx) hk
  injective_fderiv {x} hx := by
    rw [fderiv_comp]
    · exact (g.injective_fderiv (f.mapsTo hx)).comp <| f.injective_fderiv hx
    · exact g.differentiableAt hk (f.mapsTo hx)
    · exact f.differentiableAt hk hx
  finrank_le := f.finrank_le.trans g.finrank_le
  mapsTo := g.mapsTo.comp f.mapsTo

@[simps -fullyApplied]
def restr (f : Chart k α s) (t : Set (E × f.Dom)) : Chart k α s where
  Dom := f.Dom
  toFun := f
  set := f.set ∩ t
  fst_apply := by simp
  contDiffMoreiraHolderAt hx := f.contDiffMoreiraHolderAt hx.1
  injective_fderiv hx := f.injective_fderiv hx.1
  finrank_le := f.finrank_le
  mapsTo := f.mapsTo.mono_left inter_subset_left

@[simps -fullyApplied]
def ofLE (ψ : Chart k α s) (l : ℕ) (hl : l ≤ k) : Chart l α s where
  __ := ψ
  contDiffMoreiraHolderAt hx := ψ.contDiffMoreiraHolderAt hx |>.of_le hl

end Chart

structure Atlas (k : ℕ) (α : I) (s : Set (E × F)) where
  charts : Set (Chart k α s)
  countable : charts.Countable
  subset_biUnion_isLargeAt : s ⊆ ⋃ f ∈ charts, f '' {x ∈ f.set | IsLargeAt k α f.set x}

theorem nonempty_atlas {k : ℕ} (hk : k ≠ 0) (α : I) (s : Set (E × F)) :
    Nonempty (Atlas k α s) := by
  induction hF : dim F using Nat.strongRecOn generalizing F with | _ n ihn
  subst n
  set t := {x | IsLargeAt k α s x}
  choose! f pt hdim_lt hpt_mem hf_map
    using fun x (hx : x ∈ s \ t) ↦ Chart.exists_dim_lt_map_nhdsWithin_eq hx.2 hk hx.1
  have hf_mem : ∀ x ∈ s \ t, f x '' (f x).set ∈ 𝓝[s \ t] x := fun x hx ↦ by
    apply nhdsWithin_mono _ diff_subset
    rw [← hf_map x hx]
    exact image_mem_map self_mem_nhdsWithin
  rcases TopologicalSpace.countable_cover_nhdsWithin hf_mem with ⟨u, hut, huc, htu⟩
  have Ψ : ∀ x ∈ u, Atlas k α (f x).set := fun x hx ↦
    Classical.choice (ihn _ (hdim_lt x <| hut hx) _ rfl)
  refine
    ⟨insert .id (⋃ (x) (hx : x ∈ u), (fun g ↦ (f x).comp g hk) '' (Ψ x hx).charts),
    (huc.biUnion fun x hx ↦ (Ψ x hx).countable.image _).insert _, ?_⟩
  rw [biUnion_insert]
  intro x hx
  by_cases hxt : IsLargeAt k α s x
  · left
    simp [hx, hxt]
  · right
    simp only [biUnion_iUnion, biUnion_image, Chart.comp]
    rcases mem_iUnion₂.mp (htu ⟨hx, hxt⟩) with ⟨i, hiu, y, hy, rfl⟩
    rcases mem_iUnion₂.mp ((Ψ i hiu).subset_biUnion_isLargeAt hy) with ⟨g, hgS, z, hz, rfl⟩
    refine mem_iUnion_of_mem i <| mem_iUnion_of_mem hiu <| mem_biUnion hgS ?_
    apply mem_image_of_mem
    exact hz

end

namespace Atlas

universe x u v w

def choice {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (k : ℕ) (α : I) (s : Set (E × F)) : Atlas (k + 1) α s :=
  Classical.choice (nonempty_atlas k.succ_ne_zero α s)

-- TODO: If the variables are still there, then Lean uses them.
set_option linter.unusedVariables false in
def main {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∀ {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (k : ℕ) (α : I) (s : Set (E × F)), Atlas 1 α s
  | _, _, _, _, 0, α, s => choice 0 α s
  | _, _, _, _, k + 1, α, s =>
    let Ψ := choice k α s
    { charts := ⋃ ψ ∈ Ψ.charts,
        (fun φ ↦
          ((ψ.ofLE 1 (by simp)).restr {x | IsLargeAt (k + 1) α ψ.set x}).comp φ one_ne_zero) ''
          (main k α {x ∈ ψ.set | IsLargeAt (k + 1) α ψ.set x}).charts
      countable := Ψ.countable.biUnion fun _ _ ↦ (main _ _ _).countable.image _
      subset_biUnion_isLargeAt := by
        refine Ψ.subset_biUnion_isLargeAt.trans ?_
        simp only [biUnion_iUnion, biUnion_image]
        gcongr with ψ hψ
        rintro _ ⟨x, hx, rfl⟩
        rcases mem_iUnion₂.mp
          ((main k α {x ∈ ψ.set | IsLargeAt (k + 1) α ψ.set x}).subset_biUnion_isLargeAt hx)
          with ⟨φ, hφ, y, hy, rfl⟩
        refine mem_biUnion hφ ?_
        aesop }

end Atlas
