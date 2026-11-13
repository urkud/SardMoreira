module

public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Topology.Algebra.Module.Complement

/-!
# Local normal form of a map with complemented kernel and range of the derivative

Let `f : E → F` be a map that is strictly differentiable at `a` with derivative `f'`.
Given continuous linear maps `P : F →L[𝕜] R` and `Q : E →L[𝕜] K`
such that `(P ∘L f').prod Q : E →L[𝕜] R × K` is invertible,
the map `x ↦ (P (f x), Q x)` is a local homeomorphism near `a`,
see `HasStrictFDerivAt.toOpenPartialHomeomorphProd`.

The main example is the case when `P` is a projection to the range of `f'`
and `Q` is a projection to the kernel of `f'`,
see `HasStrictFDerivAt.toOpenPartialHomeomorphRangeProdKer`.
In this case, `f` written in this chart (in the domain)
and the decomposition `F ≃ f'.range × C` (in the codomain)
takes the form `(y, z) ↦ (y, g (y, z))`, where `g` has zero derivative at `(P (f a), Q a)`.

This is the first step in the proofs of the constant rank theorem,
the immersion theorem, and the Lyapunov-Schmidt reduction.

Unlike `HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented`,
we do not assume that `f'` is surjective.
-/

@[expose] public section

noncomputable section

open scoped Topology

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace ContinuousLinearMap

/-- A map `x ↦ (f x, g x)` is invertible iff `f` and `g` are surjective
and their kernels are complementary subspaces. -/
theorem isInvertible_prod_iff [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    {f : E →L[𝕜] F} {g : E →L[𝕜] G} :
    (f.prod g).IsInvertible ↔ f.range = ⊤ ∧ g.range = ⊤ ∧ IsCompl f.ker g.ker := by
  refine ⟨fun h ↦ ?_, fun ⟨hf, hg, hfg⟩ ↦ ⟨equivProdOfSurjectiveOfIsCompl f g hf hg hfg, rfl⟩⟩
  have hb := h.bijective
  refine ⟨LinearMap.range_eq_top.2 fun y ↦ ?_, LinearMap.range_eq_top.2 fun z ↦ ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hb.2 (y, 0)
    exact ⟨x, congr_arg Prod.fst hx⟩
  · obtain ⟨x, hx⟩ := hb.2 (0, z)
    exact ⟨x, congr_arg Prod.snd hx⟩
  · rw [Submodule.disjoint_def]
    intro x hxf hxg
    apply hb.1
    simp_all
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    obtain ⟨u, hu⟩ := hb.2 (f x, 0)
    simp only [prod_apply, Prod.mk.injEq] at hu
    exact Submodule.mem_sup.2 ⟨x - u, by simp [hu.1], u, by simp [hu.2], sub_add_cancel x u⟩

/-- If `C` is a topological complement of the range of `f'`
and `D` is a topological complement of its kernel,
then the map `x ↦ (projection of f' x to f'.range along C, projection of x to f'.ker along D)`
is invertible. -/
theorem isInvertible_projectionOntoL_comp_prod_projectionOntoL [CompleteSpace E]
    {f' : E →L[𝕜] F} [CompleteSpace f'.range] {C : Submodule 𝕜 F} {D : Submodule 𝕜 E}
    (hC : f'.range.IsTopCompl C) (hD : f'.ker.IsTopCompl D) :
    ((f'.range.projectionOntoL C hC ∘L f').prod (f'.ker.projectionOntoL D hD)).IsInvertible := by
  have hker : (f'.range.projectionOntoL C hC ∘L f').ker = f'.ker := by
    ext x
    simp only [LinearMap.mem_ker, coe_coe, comp_apply, Submodule.projectionOntoL_apply_eq_zero_iff]
    refine ⟨fun h ↦ Submodule.disjoint_def.1 hC.isCompl.disjoint _ ⟨x, rfl⟩ h, fun h ↦ ?_⟩
    rw [h]
    exact C.zero_mem
  refine isInvertible_prod_iff.2 ⟨?_, Submodule.range_projectionOntoL _, ?_⟩
  · rw [LinearMap.range_eq_top]
    rintro ⟨_, x, rfl⟩
    exact ⟨x, Submodule.projectionOntoL_apply_left hC ⟨f' x, _⟩⟩
  · rw [hker, Submodule.ker_projectionOntoL]
    exact hD.isCompl

end ContinuousLinearMap

namespace ImplicitFunctionData

variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]

/-- Implicit function data given by two maps `f` and `g`
with strict derivatives `f'` and `g'` at `a`
such that `x ↦ (f' x, g' x)` is invertible. -/
@[simps]
def ofIsInvertible {f : E → F} {g : E → G} {f' : E →L[𝕜] F} {g' : E →L[𝕜] G} {a : E}
    (hf : HasStrictFDerivAt f f' a) (hg : HasStrictFDerivAt g g' a)
    (hfg : (f'.prod g').IsInvertible) : ImplicitFunctionData 𝕜 E F G where
  leftFun := f
  leftDeriv := f'
  rightFun := g
  rightDeriv := g'
  pt := a
  hasStrictFDerivAt_leftFun := hf
  hasStrictFDerivAt_rightFun := hg
  range_leftDeriv := (ContinuousLinearMap.isInvertible_prod_iff.1 hfg).1
  range_rightDeriv := (ContinuousLinearMap.isInvertible_prod_iff.1 hfg).2.1
  isCompl_ker := (ContinuousLinearMap.isInvertible_prod_iff.1 hfg).2.2

end ImplicitFunctionData

namespace HasStrictFDerivAt

variable [CompleteSpace E] {R K : Type*}
  [NormedAddCommGroup R] [NormedSpace 𝕜 R] [CompleteSpace R]
  [NormedAddCommGroup K] [NormedSpace 𝕜 K] [CompleteSpace K]
  {f : E → F} {f' : E →L[𝕜] F} {a : E}

section Prod

variable (f f') in
/-- Let `f : E → F` be a map with strict derivative `f'` at `a`.
Let `P : F →L[𝕜] R` and `Q : E →L[𝕜] K` be continuous linear maps
such that `x ↦ (P (f' x), Q x)` is invertible.
Then `x ↦ (P (f x), Q x)` is an open partial homeomorphism near `a`.

Typically, `P` is a projection to the range of `f'` and `Q` is a projection to its kernel,
see `HasStrictFDerivAt.toOpenPartialHomeomorphRangeProdKer`. -/
def toOpenPartialHomeomorphProd (hf : HasStrictFDerivAt f f' a) (P : F →L[𝕜] R) (Q : E →L[𝕜] K)
    (hPQ : ((P ∘L f').prod Q).IsInvertible) : OpenPartialHomeomorph E (R × K) :=
  (ImplicitFunctionData.ofIsInvertible (P.hasStrictFDerivAt.comp a hf) Q.hasStrictFDerivAt
    hPQ).toOpenPartialHomeomorph

variable (hf : HasStrictFDerivAt f f' a) (P : F →L[𝕜] R) (Q : E →L[𝕜] K)
  (hPQ : ((P ∘L f').prod Q).IsInvertible)

@[simp]
theorem coe_toOpenPartialHomeomorphProd :
    ⇑(hf.toOpenPartialHomeomorphProd f f' P Q hPQ) = fun x ↦ (P (f x), Q x) := by
  ext x <;> simp [toOpenPartialHomeomorphProd]

theorem toOpenPartialHomeomorphProd_apply (x : E) :
    hf.toOpenPartialHomeomorphProd f f' P Q hPQ x = (P (f x), Q x) := by
  simp

@[simp]
theorem mem_toOpenPartialHomeomorphProd_source :
    a ∈ (hf.toOpenPartialHomeomorphProd f f' P Q hPQ).source :=
  ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source _

@[simp]
theorem mem_toOpenPartialHomeomorphProd_target :
    (P (f a), Q a) ∈ (hf.toOpenPartialHomeomorphProd f f' P Q hPQ).target := by
  simpa using (hf.toOpenPartialHomeomorphProd f f' P Q hPQ).map_source <|
    hf.mem_toOpenPartialHomeomorphProd_source P Q hPQ

theorem toOpenPartialHomeomorphProd_symm_apply_self :
    (hf.toOpenPartialHomeomorphProd f f' P Q hPQ).symm (P (f a), Q a) = a := by
  simpa using (hf.toOpenPartialHomeomorphProd f f' P Q hPQ).left_inv <|
    hf.mem_toOpenPartialHomeomorphProd_source P Q hPQ

/-- In the chart `hf.toOpenPartialHomeomorphProd f f' P Q hPQ`,
the map `P ∘ f` becomes the projection to the first coordinate. -/
theorem apply_apply_toOpenPartialHomeomorphProd_symm {p : R × K}
    (hp : p ∈ (hf.toOpenPartialHomeomorphProd f f' P Q hPQ).target) :
    P (f ((hf.toOpenPartialHomeomorphProd f f' P Q hPQ).symm p)) = p.1 := by
  simpa using congr_arg Prod.fst <| (hf.toOpenPartialHomeomorphProd f f' P Q hPQ).right_inv hp

theorem apply_toOpenPartialHomeomorphProd_symm {p : R × K}
    (hp : p ∈ (hf.toOpenPartialHomeomorphProd f f' P Q hPQ).target) :
    Q ((hf.toOpenPartialHomeomorphProd f f' P Q hPQ).symm p) = p.2 := by
  simpa using congr_arg Prod.snd <| (hf.toOpenPartialHomeomorphProd f f' P Q hPQ).right_inv hp

theorem hasStrictFDerivAt_toOpenPartialHomeomorphProd :
    HasStrictFDerivAt (hf.toOpenPartialHomeomorphProd f f' P Q hPQ) ((P ∘L f').prod Q) a := by
  rw [coe_toOpenPartialHomeomorphProd]
  exact (P.hasStrictFDerivAt.comp a hf).prodMk Q.hasStrictFDerivAt

theorem isInvertible_fderiv_toOpenPartialHomeomorphProd :
    (fderiv 𝕜 (hf.toOpenPartialHomeomorphProd f f' P Q hPQ) a).IsInvertible := by
  rwa [(hf.hasStrictFDerivAt_toOpenPartialHomeomorphProd P Q hPQ).hasFDerivAt.fderiv]

theorem hasStrictFDerivAt_toOpenPartialHomeomorphProd_symm :
    HasStrictFDerivAt (hf.toOpenPartialHomeomorphProd f f' P Q hPQ).symm
      ((P ∘L f').prod Q).inverse (P (f a), Q a) := by
  rcases id hPQ with ⟨e, he⟩
  rw [show ((P ∘L f').prod Q).inverse = e.symm by rw [← he, ContinuousLinearMap.inverse_equiv]]
  apply OpenPartialHomeomorph.hasStrictFDerivAt_symm
  · exact hf.mem_toOpenPartialHomeomorphProd_target P Q hPQ
  · rw [toOpenPartialHomeomorphProd_symm_apply_self, he]
    exact hf.hasStrictFDerivAt_toOpenPartialHomeomorphProd P Q hPQ

/-- If `P' : F →L[𝕜] G` vanishes on the range of `f'`,
then `P' ∘ f` written in the chart `hf.toOpenPartialHomeomorphProd f f' P Q hPQ`
has zero strict derivative at the image of `a`.

Typically, `P'` is the projection to a complement of the range of `f'`. -/
theorem hasStrictFDerivAt_comp_toOpenPartialHomeomorphProd_symm (P' : F →L[𝕜] G)
    (hP' : P' ∘L f' = 0) :
    HasStrictFDerivAt (fun p ↦ P' (f ((hf.toOpenPartialHomeomorphProd f f' P Q hPQ).symm p)))
      (0 : R × K →L[𝕜] G) (P (f a), Q a) := by
  have h := P'.hasStrictFDerivAt.comp a hf
  rw [hP', ← hf.toOpenPartialHomeomorphProd_symm_apply_self P Q hPQ] at h
  simpa using h.comp _ (hf.hasStrictFDerivAt_toOpenPartialHomeomorphProd_symm P Q hPQ)

end Prod

section RangeProdKer

variable [CompleteSpace f'.range] {C : Submodule 𝕜 F} {D : Submodule 𝕜 E}

variable (f f') in
/-- Let `f : E → F` be a map with strict derivative `f'` at `a`.
Let `C` and `D` be topological complements of `f'.range` and `f'.ker`, respectively.
Then `x ↦ (projection of f x to f'.range along C, projection of x to f'.ker along D)`
is an open partial homeomorphism near `a`.

In this chart, the map `f` takes the form `(y, z) ↦ y + g(y, z)`,
where `g` takes values in `C` and has zero derivative at the image of `a`, see
`HasStrictFDerivAt.prodEquivOfIsTopCompl_symm_apply_toOpenPartialHomeomorphRangeProdKer_symm`
and `HasStrictFDerivAt.hasStrictFDerivAt_projectionOntoL_toOpenPartialHomeomorphRangeProdKer_symm`.
-/
def toOpenPartialHomeomorphRangeProdKer (hf : HasStrictFDerivAt f f' a)
    (hC : f'.range.IsTopCompl C) (hD : f'.ker.IsTopCompl D) :
    OpenPartialHomeomorph E (f'.range × f'.ker) :=
  hf.toOpenPartialHomeomorphProd f f' (f'.range.projectionOntoL C hC)
    (f'.ker.projectionOntoL D hD)
    (ContinuousLinearMap.isInvertible_projectionOntoL_comp_prod_projectionOntoL hC hD)

variable (hf : HasStrictFDerivAt f f' a) (hC : f'.range.IsTopCompl C) (hD : f'.ker.IsTopCompl D)

theorem toOpenPartialHomeomorphRangeProdKer_eq_prod :
    hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD =
      hf.toOpenPartialHomeomorphProd f f' (f'.range.projectionOntoL C hC)
        (f'.ker.projectionOntoL D hD)
        (ContinuousLinearMap.isInvertible_projectionOntoL_comp_prod_projectionOntoL hC hD) :=
  rfl

@[simp]
theorem coe_toOpenPartialHomeomorphRangeProdKer :
    ⇑(hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD) =
      fun x ↦ (f'.range.projectionOntoL C hC (f x), f'.ker.projectionOntoL D hD x) :=
  hf.coe_toOpenPartialHomeomorphProd ..

theorem toOpenPartialHomeomorphRangeProdKer_apply (x : E) :
    hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD x =
      (f'.range.projectionOntoL C hC (f x), f'.ker.projectionOntoL D hD x) := by
  simp

theorem toOpenPartialHomeomorphRangeProdKer_apply_fst (x : E) :
    (hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD x).1 =
      f'.range.projectionOntoL C hC (f x) := by
  simp

theorem toOpenPartialHomeomorphRangeProdKer_apply_snd (x : E) :
    (hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD x).2 = f'.ker.projectionOntoL D hD x := by
  simp

@[simp]
theorem mem_toOpenPartialHomeomorphRangeProdKer_source :
    a ∈ (hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD).source :=
  hf.mem_toOpenPartialHomeomorphProd_source ..

theorem hasStrictFDerivAt_toOpenPartialHomeomorphRangeProdKer :
    HasStrictFDerivAt (hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD)
      ((f'.range.projectionOntoL C hC ∘L f').prod (f'.ker.projectionOntoL D hD)) a :=
  hf.hasStrictFDerivAt_toOpenPartialHomeomorphProd ..

theorem isInvertible_fderiv_toOpenPartialHomeomorphRangeProdKer :
    (fderiv 𝕜 (hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD) a).IsInvertible :=
  hf.isInvertible_fderiv_toOpenPartialHomeomorphProd ..

/-- In the chart `hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD` in the domain
and the decomposition `F ≃ f'.range × C` in the codomain,
the first component of `f` is the identity map. -/
theorem prodEquivOfIsTopCompl_symm_apply_toOpenPartialHomeomorphRangeProdKer_symm
    {p : f'.range × f'.ker} (hp : p ∈ (hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD).target) :
    (Submodule.prodEquivOfIsTopCompl _ _ hC).symm
        (f ((hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD).symm p)) =
      (p.1, C.projectionOntoL f'.range hC.symm
        (f ((hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD).symm p))) := by
  rw [Submodule.prodEquivOfIsTopCompl_symm_apply, Prod.mk.injEq]
  exact ⟨hf.apply_apply_toOpenPartialHomeomorphProd_symm _ _ _ hp, rfl⟩

/-- In the chart `hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD`,
the projection of `f` to `C` along `f'.range` has zero strict derivative at the image of `a`. -/
theorem hasStrictFDerivAt_projectionOntoL_toOpenPartialHomeomorphRangeProdKer_symm :
    HasStrictFDerivAt (fun p ↦ C.projectionOntoL f'.range hC.symm
        (f ((hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD).symm p)))
      (0 : f'.range × f'.ker →L[𝕜] C) (hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD a) := by
  rw [coe_toOpenPartialHomeomorphRangeProdKer]
  apply hasStrictFDerivAt_comp_toOpenPartialHomeomorphProd_symm
  ext x
  simp

end RangeProdKer

end HasStrictFDerivAt
