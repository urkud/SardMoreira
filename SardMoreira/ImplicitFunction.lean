module

public import SardMoreira.ContDiffMoreiraHolder
public import SardMoreira.LinearAlgebra

@[expose] public section

noncomputable section

open scoped Topology unitInterval

namespace HasStrictFDerivAt

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

@[irreducible, simps +simpRhs pt]
def implicitFunctionDataOfComplementedKerRange (f : E → F) (f' : E →L[𝕜] F) {a : E}
    (hf : HasStrictFDerivAt f f' a) (hker : f'.ker.ClosedComplemented)
    (hrange : f'.range.ClosedComplemented) :
    have := hrange.isClosed.completeSpace_coe
    ImplicitFunctionData 𝕜 E f'.range f'.ker := by
  haveI := hrange.isClosed.completeSpace_coe
  have hrange_apply (x) : hrange.choose (f' x) = ⟨f' x, by simp⟩ :=
    hrange.choose_spec ⟨f' x, by simp⟩
  have hker_eq : (hrange.choose ∘L f').ker = f'.ker := by
    ext x
    simp_all
  have hrange_eq : (hrange.choose ∘L f').range = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨_, x, rfl⟩
    use x
    simp_all
  refine
    { leftFun := hrange.choose ∘ f
      leftDeriv := hrange.choose ∘L f'
      rightFun := hker.choose
      rightDeriv := hker.choose
      pt := a
      hasStrictFDerivAt_leftFun := hrange.choose.hasStrictFDerivAt.comp a hf
      hasStrictFDerivAt_rightFun := hker.choose.hasStrictFDerivAt
      range_leftDeriv := hrange_eq
      range_rightDeriv := LinearMap.range_eq_of_proj (Classical.choose_spec hker)
      isCompl_ker := ?_ }
  rw [hker_eq]
  exact LinearMap.isCompl_of_proj hker.choose_spec

def implicitToOpenPartialHomeomorphOfComplementedKerRange (f : E → F) (f' : E →L[𝕜] F) {a : E}
    (hf : HasStrictFDerivAt f f' a) (hker : f'.ker.ClosedComplemented)
    (hrange : f'.range.ClosedComplemented) :
    OpenPartialHomeomorph E (f'.range × f'.ker) :=
  have := hrange.isClosed.completeSpace_coe
  (hf.implicitFunctionDataOfComplementedKerRange f f' hker hrange).toOpenPartialHomeomorph

@[simp]
theorem mem_implicitToOpenPartialHomeomorphOfComplementedKerRange_source
    {f : E → F} {f' : E →L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f f' a) (hker : f'.ker.ClosedComplemented)
    (hrange : f'.range.ClosedComplemented) :
    a ∈ (hf.implicitToOpenPartialHomeomorphOfComplementedKerRange f f' hker hrange).source := by
  unfold implicitToOpenPartialHomeomorphOfComplementedKerRange
  convert ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source _
  simp

theorem implicitToOpenPartialHomeomorphOfComplementedKerRange_apply {f : E → F} {f' : E →L[𝕜] F}
    {a : E} (hf : HasStrictFDerivAt f f' a) (hker : f'.ker.ClosedComplemented)
    (hrange : f'.range.ClosedComplemented) (x : E) :
    implicitToOpenPartialHomeomorphOfComplementedKerRange f f' hf hker hrange x =
      (hrange.choose (f x), hker.choose x) := by
  -- `simp [implicitToOpenPartialHomeomorphOfComplementedKerRange,
  --  implicitFunctionDataOfComplementedKerRange]` works but it's much slower
  simp only [implicitToOpenPartialHomeomorphOfComplementedKerRange,
    implicitFunctionDataOfComplementedKerRange, Function.comp_apply, ImplicitFunctionData.toOpenPartialHomeomorph_apply]

theorem coe_implicitToOpenPartialHomeomorphOfComplementedKerRange {f : E → F} {f' : E →L[𝕜] F}
    {a : E} (hf : HasStrictFDerivAt f f' a) (hker : f'.ker.ClosedComplemented)
    (hrange : f'.range.ClosedComplemented) :
    implicitToOpenPartialHomeomorphOfComplementedKerRange f f' hf hker hrange =
      fun x ↦ (hrange.choose (f x), hker.choose x) :=
  funext <| implicitToOpenPartialHomeomorphOfComplementedKerRange_apply hf hker hrange

@[simp]
theorem implicitToOpenPartialHomeomorphOfComplementedKerRange_apply_fst {f : E → F} {f' : E →L[𝕜] F}
    {a : E} (hf : HasStrictFDerivAt f f' a) (hker : f'.ker.ClosedComplemented)
    (hrange : f'.range.ClosedComplemented) (x : E) :
    (implicitToOpenPartialHomeomorphOfComplementedKerRange f f' hf hker hrange x).fst =
      hrange.choose (f x) := by
  simp [implicitToOpenPartialHomeomorphOfComplementedKerRange_apply]

end HasStrictFDerivAt
