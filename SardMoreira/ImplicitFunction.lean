import Mathlib

noncomputable section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

namespace HasStrictFDerivAt

@[irreducible]
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

theorem implicitToOpenPartialHomeomorphOfComplementedKerRange_apply_fst {f : E → F} {f' : E →L[𝕜] F}
    {a : E} (hf : HasStrictFDerivAt f f' a) (hker : (LinearMap.ker f').ClosedComplemented)
    (hrange : (LinearMap.range f').ClosedComplemented) (x : E) :
    (implicitToOpenPartialHomeomorphOfComplementedKerRange f f' hf hker hrange x).fst =
      hrange.choose (f x) := by
  simp [implicitToOpenPartialHomeomorphOfComplementedKerRange_apply]

def implicitOfComplementedKerRangeConjugated (f : E → F) (f' : E →L[𝕜] F) {a : E}
    (hf : HasStrictFDerivAt f f' a) (hker : (LinearMap.ker f').ClosedComplemented)
    (hrange : (LinearMap.range f').ClosedComplemented)
    (x : LinearMap.range f' × LinearMap.ker f') :
    LinearMap.range f' × LinearMap.ker hrange.choose :=
  (x.fst, hrange.choose.projKerOfRightInverse (LinearMap.range f').subtypeL hrange.choose_spec <|
    f ((implicitToOpenPartialHomeomorphOfComplementedKerRange f f' hf hker hrange).symm x) - f a)

@[simp]
theorem implicitOfComplementedKerRangeConjugated_fst {f : E → F} {f' : E →L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f f' a) (hker : (LinearMap.ker f').ClosedComplemented)
    (hrange : (LinearMap.range f').ClosedComplemented) (x : LinearMap.range f' × LinearMap.ker f') :
    (implicitOfComplementedKerRangeConjugated f f' hf hker hrange x).fst = x.fst := rfl
