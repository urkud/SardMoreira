module

public import SardMoreira.ContDiff
public import SardMoreira.ImplicitFunction
public import SardMoreira.LinearAlgebra

/-!
# Constant rank theorem

Let `f : E → F` be a `C¹` map from a finite dimensional real normed space.
Suppose that the rank of `fderiv ℝ f x` does not exceed the rank of `f' = fderiv ℝ f a`
for `x` close to `a`.
Then, in the chart `HasStrictFDerivAt.toOpenPartialHomeomorphRangeProdKer`,
the map `f` does not depend on the second (kernel) coordinate near the image of `a`.

Combined with
`HasStrictFDerivAt.prodEquivOfIsTopCompl_symm_apply_toOpenPartialHomeomorphRangeProdKer_symm`,
this says that near `a`, `f` is written in suitable charts as `(y, z) ↦ (y, g y)`.
-/

@[expose] public section

open scoped Topology
open Metric Module

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace HasStrictFDerivAt

/-- **Constant rank theorem**: if `f` is `C¹` near `a`
and the rank of `fderiv ℝ f x` does not exceed the rank of `f'` for `x` close to `a`,
then `f` written in the chart `hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD`
does not depend on the second coordinate near the image of `a`. -/
theorem eventually_apply_toOpenPartialHomeomorphRangeProdKer_symm_eq
    {f : E → F} {f' : E →L[ℝ] F} {a : E} (hf : HasStrictFDerivAt f f' a)
    (hf₁ : ContDiffAt ℝ 1 f a) {C : Submodule ℝ F} {D : Submodule ℝ E}
    (hC : f'.range.IsTopCompl C) (hD : f'.ker.IsTopCompl D)
    (hrank : ∀ᶠ x in 𝓝 a, finrank ℝ (fderiv ℝ f x).range ≤ finrank ℝ f'.range) :
    ∀ᶠ p in 𝓝 (hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD a),
      f ((hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD).symm p) =
        f ((hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD).symm
          (p.1, (hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD a).2)) := by
  set e := hf.toOpenPartialHomeomorphRangeProdKer f f' hC hD
  set y₀ := e a
  set eCod := (Submodule.prodEquivOfIsTopCompl _ _ hC).symm
  set πC := C.projectionOntoL f'.range hC.symm
  set γ : f'.range × f'.ker → C := fun p ↦ πC (f (e.symm p))
  have hae : a ∈ e.source := by simp [e]
  have hy₀ : y₀ ∈ e.target := e.map_source hae
  have heq {q} (hq : q ∈ e.target) : eCod (f (e.symm q)) = (q.1, γ q) :=
    hf.prodEquivOfIsTopCompl_symm_apply_toOpenPartialHomeomorphRangeProdKer_symm hC hD hq
  have heqOn : e.target.EqOn (Function.prod Prod.fst γ) (eCod ∘ f ∘ e.symm) := fun q hq ↦ by
    simp [heq hq]
  -- Choose a ball around `y₀` such that all the properties we need hold on this ball.
  have heC : ContDiffAt ℝ 1 e a := by
    rw [HasStrictFDerivAt.coe_toOpenPartialHomeomorphRangeProdKer]
    exact ((ContinuousLinearMap.contDiff _).contDiffAt.comp a hf₁).prodMk
      (ContinuousLinearMap.contDiff _).contDiffAt
  have hgood : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x ∧ (fderiv ℝ e x).IsInvertible ∧
      finrank ℝ (fderiv ℝ f x).range ≤ finrank ℝ f'.range := by
    filter_upwards [hf₁.eventually (by simp), heC.eventually_isInvertible_fderiv
      (hf.isInvertible_fderiv_toOpenPartialHomeomorphRangeProdKer hC hD) one_ne_zero, hrank]
      with x hx₁ hx₂ hx₃
    exact ⟨hx₁.differentiableAt one_ne_zero, hx₂, hx₃⟩
  have hgood' : ∀ᶠ q in 𝓝 y₀, q ∈ e.target ∧ DifferentiableAt ℝ f (e.symm q) ∧
      (fderiv ℝ e (e.symm q)).IsInvertible ∧
      finrank ℝ (fderiv ℝ f (e.symm q)).range ≤ finrank ℝ f'.range := by
    refine (e.open_target.eventually_mem hy₀).and ?_
    have := e.continuousAt_symm hy₀
    rw [ContinuousAt, e.left_inv hae] at this
    exact this.eventually hgood
  obtain ⟨r, hr₀, hr⟩ := Metric.eventually_nhds_iff_ball.1 hgood'
  -- At each point of this ball, the derivative of `γ` in the second variable vanishes.
  have hγd {q} (hq : q ∈ ball y₀ r) : DifferentiableAt ℝ γ q := by
    obtain ⟨hqt, hfd, hinv, -⟩ := hr q hq
    exact πC.differentiableAt.comp q
      (hfd.comp q (e.hasFDerivAt_symm_inverse hqt hinv).differentiableAt)
  have hγ' {q} (hq : q ∈ ball y₀ r) : fderiv ℝ γ q ∘L .inr ℝ _ _ = 0 := by
    obtain ⟨hqt, hfd, hinv, hrk⟩ := hr q hq
    have hd := (e.hasFDerivAt_symm_inverse hqt hinv).differentiableAt
    have hrank_eq : (fderiv ℝ (Function.prod Prod.fst γ) q).finrank =
        finrank ℝ (fderiv ℝ f (e.symm q)).range := by
      rw [heqOn.eventuallyEq_of_mem (e.open_target.mem_nhds hqt) |>.fderiv_eq,
        fderiv_comp _ eCod.differentiableAt (hfd.comp q hd), eCod.fderiv, eCod.finrank_comp_left,
        fderiv_comp _ hfd hd, ContinuousLinearMap.finrank_comp_eq_left_of_surjective]
      · rfl
      · exact e.surjective_fderiv_symm hqt hinv
    have hprod : fderiv ℝ (Function.prod Prod.fst γ) q =
        (ContinuousLinearMap.fst ℝ _ _).prod (fderiv ℝ γ q) := by
      unfold Function.prod
      rw [DifferentiableAt.fderiv_prodMk differentiableAt_fst (hγd hq), fderiv_fst]
    rw [hprod] at hrank_eq
    change finrank ℝ (LinearMap.range (LinearMap.prod (LinearMap.fst ℝ _ _)
      (fderiv ℝ γ q : f'.range × f'.ker →ₗ[ℝ] C))) = _ at hrank_eq
    rw [LinearMap.finrank_range_prod_fst] at hrank_eq
    have h0 : LinearMap.range ((fderiv ℝ γ q : f'.range × f'.ker →ₗ[ℝ] C) ∘ₗ
        LinearMap.inr ℝ _ _) = ⊥ :=
      Submodule.finrank_eq_zero.1 (by omega)
    ext1 z
    exact LinearMap.congr_fun (LinearMap.range_eq_bot.1 h0) z
  have hball {q : f'.range × f'.ker} (hq : q ∈ ball y₀ r) {z : f'.ker} (hz : z ∈ ball y₀.2 r) :
      (q.1, z) ∈ ball y₀ r := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff] at hq ⊢
    exact ⟨hq.1, hz⟩
  have hkey {q} (hq : q ∈ ball y₀ r) : f (e.symm q) = eCod.symm (q.1, γ q) := by
    rw [← heq (hr q hq).1, ContinuousLinearEquiv.symm_apply_apply]
  -- Now we use the fact that the derivative vanishes on the ball.
  filter_upwards [ball_mem_nhds y₀ hr₀] with p hp
  have hp₂ : p.2 ∈ ball y₀.2 r := (mem_ball.1 hp).trans_le' (le_max_right _ _)
  have hconst : γ (p.1, p.2) = γ (p.1, y₀.2) := by
    refine isOpen_ball.is_const_of_fderiv_eq_zero (𝕜 := ℝ) (f := fun z ↦ γ (p.1, z))
      isPreconnected_ball (fun z hz ↦ ?_) (fun z hz ↦ ?_) hp₂ (mem_ball_self hr₀)
    · exact ((hγd (hball hp hz)).comp z (by fun_prop)).differentiableWithinAt
    · rw [fderiv_fun_comp_prodMk (hγd (hball hp hz))]
      exact hγ' (hball hp hz)
  rw [hkey hp, hkey (hball hp (mem_ball_self hr₀)), hconst]

end HasStrictFDerivAt
