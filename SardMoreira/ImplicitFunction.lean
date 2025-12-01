import SardMoreira.ContDiffMoreiraHolder
import SardMoreira.LinearAlgebra

noncomputable section

open scoped Topology unitInterval

namespace HasStrictFDerivAt

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

@[irreducible, simps +simpRhs pt]
def implicitFunctionDataOfComplementedKerRange (f : E → F) (f' : E →L[𝕜] F) {a : E}
    (hf : HasStrictFDerivAt f f' a) (hker : (LinearMap.ker f').ClosedComplemented)
    (hrange : (LinearMap.range f').ClosedComplemented) :
    have := hrange.isClosed.completeSpace_coe
    ImplicitFunctionData 𝕜 E (LinearMap.range f') (LinearMap.ker f') := by
  haveI := hrange.isClosed.completeSpace_coe
  have hrange_apply (x) : hrange.choose (f' x) = ⟨f' x, by simp⟩ :=
    hrange.choose_spec ⟨f' x, by simp⟩
  have hker_eq : LinearMap.ker (hrange.choose ∘L f') = LinearMap.ker f' := by
    ext x
    simp_all
  have hrange_eq : LinearMap.range (hrange.choose ∘L f') = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨_, x, rfl⟩
    use x
    simp_all
  let φ := implicitFunctionDataOfComplemented (hrange.choose ∘ f) (hrange.choose ∘L f')
    (hrange.choose.hasStrictFDerivAt.comp a hf) hrange_eq (by rwa [hker_eq])
  refine
    { __ := φ,
      rightFun := hker.choose
      rightDeriv := hker.choose
      right_range := LinearMap.range_eq_of_proj (Classical.choose_spec hker)
      right_has_deriv := hker.choose.hasStrictFDerivAt
      isCompl_ker := ?_ }
  simpa only [φ, implicitFunctionDataOfComplemented, hker_eq]
    using LinearMap.isCompl_of_proj hker.choose_spec

def implicitToOpenPartialHomeomorphOfComplementedKerRange (f : E → F) (f' : E →L[𝕜] F) {a : E}
    (hf : HasStrictFDerivAt f f' a) (hker : (LinearMap.ker f').ClosedComplemented)
    (hrange : (LinearMap.range f').ClosedComplemented) :
    OpenPartialHomeomorph E (LinearMap.range f' × LinearMap.ker f') :=
  have := hrange.isClosed.completeSpace_coe
  (hf.implicitFunctionDataOfComplementedKerRange f f' hker hrange).toOpenPartialHomeomorph
    
theorem implicitToOpenPartialHomeomorphOfComplementedKerRange_apply {f : E → F} {f' : E →L[𝕜] F}
    {a : E} (hf : HasStrictFDerivAt f f' a) (hker : (LinearMap.ker f').ClosedComplemented)
    (hrange : (LinearMap.range f').ClosedComplemented) (x : E) :
    implicitToOpenPartialHomeomorphOfComplementedKerRange f f' hf hker hrange x =
      (hrange.choose (f x), hker.choose x) := by
  -- `simp [implicitToOpenPartialHomeomorphOfComplementedKerRange,
  --  implicitFunctionDataOfComplementedKerRange]` works but it's much slower
  simp only [implicitToOpenPartialHomeomorphOfComplementedKerRange,
    implicitFunctionDataOfComplementedKerRange, implicitFunctionDataOfComplemented,
    Function.comp_apply, ImplicitFunctionData.toOpenPartialHomeomorph_apply]

theorem coe_implicitToOpenPartialHomeomorphOfComplementedKerRange {f : E → F} {f' : E →L[𝕜] F}
    {a : E} (hf : HasStrictFDerivAt f f' a) (hker : (LinearMap.ker f').ClosedComplemented)
    (hrange : (LinearMap.range f').ClosedComplemented) :
    implicitToOpenPartialHomeomorphOfComplementedKerRange f f' hf hker hrange =
      fun x ↦ (hrange.choose (f x), hker.choose x) :=
  funext <| implicitToOpenPartialHomeomorphOfComplementedKerRange_apply hf hker hrange

theorem implicitToOpenPartialHomeomorphOfComplementedKerRange_apply_fst {f : E → F} {f' : E →L[𝕜] F}
    {a : E} (hf : HasStrictFDerivAt f f' a) (hker : (LinearMap.ker f').ClosedComplemented)
    (hrange : (LinearMap.range f').ClosedComplemented) (x : E) :
    (implicitToOpenPartialHomeomorphOfComplementedKerRange f f' hf hker hrange x).fst =
      hrange.choose (f x) := by
  simp [implicitToOpenPartialHomeomorphOfComplementedKerRange_apply]

end HasStrictFDerivAt

@[simp]
theorem OpenPartialHomeomorph.coe_restrOpen {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {U : Set X} (hU : IsOpen U) :
    ⇑(e.restrOpen U hU) = e :=
  rfl

@[simp]
theorem OpenPartialHomeomorph.coe_restrOpen_symm {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y) {U : Set X} (hU : IsOpen U) :
    ⇑(e.restrOpen U hU).symm = e.symm :=
  rfl

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem ContDiffMoreiraHolderOn.exists_openPartialHomeomorph_conj_piProd_fst
    {f : E → F} {s U : Set E} {k : ℕ} {α : I} {x : E} (h : ContDiffMoreiraHolderOn k α f s U)
    (hk : k ≠ 0) (hx : x ∈ s)
    (hker : (LinearMap.ker (fderiv ℝ f x)).ClosedComplemented)
    (hrange : (LinearMap.range (fderiv ℝ f x)).ClosedComplemented) :
    ∃ (p : Submodule ℝ F) (q : Submodule ℝ E) (r : Submodule ℝ F)
      (epq : OpenPartialHomeomorph E (p × q)) (epr : F ≃L[ℝ] (p × r)) (g : p × q → r),
      epq.source ⊆ U ∧
      ContDiffMoreiraHolderOn k α epq (epq.source ∩ s) epq.source ∧
      ContDiffMoreiraHolderOn k α epq.symm (epq.target ∩ epq.symm ⁻¹' s) epq.target ∧
      Set.EqOn (epr ∘ f ∘ epq.symm) (Pi.prod Prod.fst g) epq.target := by
  set f' := fderiv ℝ f x
  have hf' : HasStrictFDerivAt f f' x :=
    (h.contDiffMoreiraHolderAt hx).contDiffAt.hasStrictFDerivAt (by norm_cast; grind)
  set p := LinearMap.range f'
  set q := LinearMap.ker f'
  set r := LinearMap.ker hrange.choose
  set epr : F ≃L[ℝ] (p × r) :=
    .equivOfRightInverse hrange.choose (Submodule.subtypeL _) hrange.choose_spec
  set epq' : OpenPartialHomeomorph E (p × q) :=
    hf'.implicitToOpenPartialHomeomorphOfComplementedKerRange f f' hker hrange
  obtain ⟨V, hVo, hxV, hVU, hVd⟩ :
      ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ x' ∈ V, (fderiv ℝ epq' x').IsInvertible := by
    suffices ∀ᶠ x' in 𝓝 x, x' ∈ U ∧ (fderiv ℝ epq' x').IsInvertible by
      rcases eventually_nhds_iff.mp this with ⟨V, hV, hVo, hxV⟩
      exact ⟨V, hVo, hxV, fun x' hx' ↦ (hV x' hx').1, fun x' hx' ↦ (hV x' hx').2⟩
    have hinv : (fderiv ℝ epq' x).IsInvertible := by
      have := hrange.isClosed.completeSpace_coe
      have := hf'.implicitFunctionDataOfComplementedKerRange f f' hker hrange |>.hasStrictFDerivAt
        |>.hasFDerivAt |>.fderiv
      simp_all +unfoldPartialApp [epq',
        HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplementedKerRange,
        funext (ImplicitFunctionData.toOpenPartialHomeomorph_apply _),
        ImplicitFunctionData.prodFun]
    have hcontDiff : ContDiffAt ℝ k epq' x := by
      rw [HasStrictFDerivAt.coe_implicitToOpenPartialHomeomorphOfComplementedKerRange]
      refine .prodMk ?_ hker.choose.contDiff.contDiffAt
      exact hrange.choose.contDiff.contDiffAt.comp _ <|
        h.contDiffOn.contDiffAt <| h.isOpen.mem_nhds <| h.subset hx
    exact Filter.inter_mem (h.isOpen.mem_nhds (h.subset hx))
      (hcontDiff.continuousAt_fderiv (mod_cast hk) (ContinuousLinearEquiv.isOpen.mem_nhds hinv))
  set epq := epq'.restrOpen V hVo
  use p, q, r, epq, epr, Prod.snd ∘ epr ∘ f ∘ epq.symm, Set.inter_subset_right.trans hVU
  have heUV : ContDiffMoreiraHolderOn k α epq (epq.source ∩ s) epq.source := by
    simp only [OpenPartialHomeomorph.coe_restrOpen,
      OpenPartialHomeomorph.restrOpen_toPartialEquiv, PartialEquiv.restr_source, epq, epq', p, q,
      HasStrictFDerivAt.coe_implicitToOpenPartialHomeomorphOfComplementedKerRange]
    refine .prodMk (.continuousLinearMap_comp ?_ _) ?_
    · constructor
      · grw [Set.inter_assoc, V.inter_subset_left]
      · exact .inter (OpenPartialHomeomorph.open_source _) hVo
      · exact h.contDiffOn.mono (Set.inter_subset_right.trans hVU)
      · exact fun a ha ↦ h.isBigO a ha.2
    · refine hker.choose.contDiff.contDiffOn.contDiffMoreiraHolderOn
        Set.inter_subset_left (.inter ?_ hVo) (WithTop.coe_lt_top _) _
      apply OpenPartialHomeomorph.open_source
  refine ⟨heUV, ⟨Set.inter_subset_left, epq.open_target, ?_, ?_⟩, ?_⟩
  · rintro y ⟨hy₁, hy₂⟩
    rcases hVd _ hy₂ with ⟨e, he⟩
    replace he : HasFDerivAt epq (e : E →L[ℝ] p × q) (epq.symm y) := by
      rw [he]
      apply DifferentiableAt.hasFDerivAt
      refine (heUV.contDiffOn.differentiableOn <| by norm_cast; grind).differentiableAt ?_
      exact epq.open_source.mem_nhds (epq.symm_mapsTo ⟨hy₁, hy₂⟩)
    apply ContDiffAt.contDiffWithinAt
    apply OpenPartialHomeomorph.contDiffAt_symm _ hy₁ he (heUV.contDiffOn.contDiffAt _)
    exact epq.open_source.mem_nhds (epq.symm_mapsTo ⟨hy₁, hy₂⟩)
  · intro y hy
    rcases hVd _ hy.1.2 with ⟨e, he⟩
    replace he : HasFDerivAt epq (e : E →L[ℝ] p × q) (epq.symm y) := by
      rw [he]
      apply DifferentiableAt.hasFDerivAt
      refine (heUV.contDiffOn.differentiableOn <| by norm_cast; grind).differentiableAt ?_
      exact epq.open_source.mem_nhds (epq.symm_mapsTo hy.1)
    apply ContDiffMoreiraHolderAt.isBigO
    apply OpenPartialHomeomorph.contDiffMoreiraHolderAt_symm _ hy.1 he
    apply heUV.contDiffMoreiraHolderAt
    exact ⟨epq.symm_mapsTo hy.1, hy.2⟩
  · intro y hy
    ext1
    · simp only [Function.comp_apply, ContinuousLinearEquiv.fst_equivOfRightInverse,
        Pi.prod, p, r, q, epr, epq, epq', OpenPartialHomeomorph.coe_restrOpen_symm,
        ← hf'.implicitToOpenPartialHomeomorphOfComplementedKerRange_apply_fst hker hrange]
      rw [OpenPartialHomeomorph.rightInvOn _ hy.1]
    · simp
