import Mathlib

open scoped ENNReal NNReal Filter Uniformity Topology
open Function

noncomputable section

@[ext]
structure WithRPowDist (X : Type*) (r : ℝ) (hr₀ : 0 < r) (hr₁ : r ≤ 1) where
  val : X

namespace WithRPowDist

variable {X : Type*} {α : ℝ} {hα₀ : 0 < α} {hα₁ : α ≤ 1}

@[simps -fullyApplied apply symm_apply]
def equiv (X : Type*) (r : ℝ) (hr₀ : 0 < r) (hr₁ : r ≤ 1) : WithRPowDist X r hr₀ hr₁ ≃ X where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem val_comp_mk : (val : WithRPowDist X α hα₀ hα₁ → X) ∘ mk = id := rfl

@[simp]
theorem mk_comp_val : (mk : X → WithRPowDist X α hα₀ hα₁) ∘ val = id := rfl

theorem image_mk_eq_preimage (s : Set X) :
    (mk '' s : Set (WithRPowDist X α hα₀ hα₁)) = val ⁻¹' s :=
  (equiv X α hα₀ hα₁).symm.image_eq_preimage _

theorem image_val_eq_preimage (s : Set (WithRPowDist X α hα₀ hα₁)) :
    val '' s = mk ⁻¹' s :=
  (equiv X α hα₀ hα₁).image_eq_preimage _

@[simp]
theorem image_mk_image_val (s : Set (WithRPowDist X α hα₀ hα₁)) :
    mk '' (val '' s) = s :=
  (equiv X α hα₀ hα₁).symm_image_image _

@[simp]
theorem image_val_image_mk (s : Set X) : val '' (mk '' s : Set (WithRPowDist X α hα₀ hα₁)) = s :=
  (equiv X α hα₀ hα₁).image_symm_image _

theorem surjective_val : Surjective (val : WithRPowDist X α hα₀ hα₁ → X) :=
  equiv _ _ _ _ |>.surjective

theorem surjective_mk : Surjective (mk :  X → WithRPowDist X α hα₀ hα₁) :=
  equiv _ _ _ _ |>.symm |>.surjective

theorem injective_mk : Injective (mk : X → WithRPowDist X α hα₀ hα₁) := by
  simp [Injective]

section TopologicalSpace

variable [TopologicalSpace X]

/-
Induce topology, uniformity, and MeasurableSpace structures on this type from X. Define an equivalence between this space and X.
-/
instance : TopologicalSpace (WithRPowDist X α hα₀ hα₁) := .induced WithRPowDist.val ‹_›

@[fun_prop]
theorem continuous_val : Continuous (val : WithRPowDist X α hα₀ hα₁ → X) :=
  continuous_induced_dom

@[fun_prop]
theorem continuous_mk : Continuous (mk : X → WithRPowDist X α hα₀ hα₁) :=
  continuous_induced_rng.2 continuous_id

/-
Define a homeomorphism between this space and X.
-/
@[simps! -fullyApplied toEquiv apply symm_apply]
def homeomorph : WithRPowDist X α hα₀ hα₁ ≃ₜ X where
  toEquiv := WithRPowDist.equiv X α hα₀ hα₁

instance [T0Space X] : T0Space (WithRPowDist X α hα₀ hα₁) :=
  homeomorph.symm.t0Space

instance [T2Space X] : T2Space (WithRPowDist X α hα₀ hα₁) :=
  homeomorph.symm.t2Space

instance [SecondCountableTopology X] : SecondCountableTopology (WithRPowDist X α hα₀ hα₁) :=
  homeomorph.secondCountableTopology

end TopologicalSpace

section Bornology

variable [Bornology X]

instance : Bornology (WithRPowDist X α hα₀ hα₁) := .induced val

open Bornology

@[simp]
theorem isBounded_image_val_iff {s : Set (WithRPowDist X α hα₀ hα₁)} :
    IsBounded (val '' s) ↔ IsBounded s :=
  isBounded_induced.symm

@[simp]
theorem isBounded_preimage_mk_iff {s : Set (WithRPowDist X α hα₀ hα₁)} :
    IsBounded (mk ⁻¹' s) ↔ IsBounded s := by
  rw [← image_val_eq_preimage, isBounded_image_val_iff]

@[simp]
theorem isBounded_image_mk_iff {s : Set X} :
    IsBounded (mk '' s : Set (WithRPowDist X α hα₀ hα₁)) ↔ IsBounded s := by
  rw [← isBounded_image_val_iff, image_val_image_mk]

@[simp]
theorem isBounded_preimage_val_iff {s : Set X} :
    IsBounded (val ⁻¹' s : Set (WithRPowDist X α hα₀ hα₁)) ↔ IsBounded s := by
  rw [← image_mk_eq_preimage, isBounded_image_mk_iff]

end Bornology

section UniformSpace

variable [UniformSpace X]

instance : UniformSpace (WithRPowDist X α hα₀ hα₁) :=
  UniformSpace.comap WithRPowDist.val ‹_›

theorem uniformContinuous_val : UniformContinuous (val : WithRPowDist X α hα₀ hα₁ → X) :=
  uniformContinuous_comap

theorem uniformContinuous_mk : UniformContinuous (mk : X → WithRPowDist X α hα₀ hα₁) :=
  uniformContinuous_comap' uniformContinuous_id

/-
Define a UniformEquiv between this space and X.
-/
@[simps! toEquiv apply symm_apply]
def uniformEquiv : WithRPowDist X α hα₀ hα₁ ≃ᵤ X where
  toEquiv := WithRPowDist.equiv X α hα₀ hα₁
  uniformContinuous_toFun := uniformContinuous_val
  uniformContinuous_invFun := uniformContinuous_mk

end UniformSpace

section MeasurableSpace

variable [MeasurableSpace X]

instance : MeasurableSpace (WithRPowDist X α hα₀ hα₁) := .comap WithRPowDist.val ‹_›

@[fun_prop, measurability]
theorem measurable_val : Measurable (val : WithRPowDist X α hα₀ hα₁ → X) :=
  comap_measurable _

@[fun_prop, measurability]
theorem measurable_mk : Measurable (mk : X → WithRPowDist X α hα₀ hα₁) :=
  .of_comap_le <| by
    rw [instMeasurableSpace, MeasurableSpace.comap_comp, val_comp_mk, MeasurableSpace.comap_id]

/-
Define a measurable equivalence between this space and X.
-/
@[simps! -fullyApplied toEquiv apply symm_apply]
def measurableEquiv : WithRPowDist X α hα₀ hα₁ ≃ᵐ X where
  toEquiv := WithRPowDist.equiv X α hα₀ hα₁
  measurable_toFun := measurable_val
  measurable_invFun := measurable_mk

theorem measurableEmbedding_mk : MeasurableEmbedding (mk : X → WithRPowDist X α hα₀ hα₁) :=
  measurableEquiv.symm.measurableEmbedding

instance [TopologicalSpace X] [BorelSpace X] : BorelSpace (WithRPowDist X α hα₀ hα₁) :=
  measurableEquiv.measurableEmbedding.borelSpace homeomorph.isInducing

end MeasurableSpace

section EDist

variable [EDist X]

instance : EDist (WithRPowDist X α hα₀ hα₁) where
  edist x y := edist x.val y.val ^ α

theorem edist_def (x y : WithRPowDist X α hα₀ hα₁) : edist x y = edist x.val y.val ^ α := rfl

@[simp]
theorem edist_mk_mk (x y : X) : edist (mk x : WithRPowDist X α hα₀ hα₁) (mk y) = edist x y ^ α :=
  rfl

@[simp]
theorem edist_val_val (x y : WithRPowDist X α hα₀ hα₁) : edist x.val y.val = edist x y ^ α⁻¹ := by
  rw [edist_def, ENNReal.rpow_rpow_inv hα₀.ne']

end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace X]

open EMetric

instance : PseudoEMetricSpace (WithRPowDist X α hα₀ hα₁) where
  edist_self x := by simp [edist_def, hα₀]
  edist_comm x y := by rw [edist_def, edist_def, edist_comm]
  edist_triangle x y z := by
    simp only [edist_def]
    grw [edist_triangle x.val y.val z.val, ENNReal.rpow_add_le_add_rpow _ _ hα₀.le hα₁]
  toUniformSpace := inferInstance
  uniformity_edist := by
    have H : (𝓤 X).HasBasis (0 < ·) fun x => {p | edist p.1 p.2 < x ^ (α⁻¹)} := by
      refine EMetric.mk_uniformity_basis (fun _ _ ↦ by positivity) fun ε hε ↦
        ⟨ε ^ α, by positivity, ?_⟩
      rw [ENNReal.rpow_rpow_inv hα₀.ne']
    simp (disch := positivity) [uniformity_comap, H.eq_biInf, ENNReal.rpow_lt_rpow_iff]

@[simp]
theorem preimage_val_emetricBall (x : X) (r : ℝ≥0∞) :
    val ⁻¹' ball x r = ball (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [ENNReal.rpow_lt_rpow_iff]

@[simp]
theorem image_mk_emetricBall (x : X) (r : ℝ≥0∞) :
    mk '' ball x r = ball (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  rw [image_mk_eq_preimage, preimage_val_emetricBall]

@[simp]
theorem preimage_mk_emetricBall (x : WithRPowDist X α hα₀ hα₁) (d : ℝ≥0∞) :
    mk ⁻¹' ball x d = ball x.val (d ^ α⁻¹) := by
  apply injective_mk.image_injective
  rw [image_mk_emetricBall, Set.image_preimage_eq _ surjective_mk, ENNReal.rpow_inv_rpow hα₀.ne']

@[simp]
theorem image_val_emetricBall (x : WithRPowDist X α hα₀ hα₁) (d : ℝ≥0∞) :
    val '' ball x d = ball x.val (d ^ α⁻¹) := by
  rw [image_val_eq_preimage, preimage_mk_emetricBall]

@[simp]
theorem preimage_val_emetricClosedBall (x : X) (r : ℝ≥0∞) :
    val ⁻¹' closedBall x r = closedBall (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [ENNReal.rpow_le_rpow_iff]

@[simp]
theorem image_mk_emetricClosedBall (x : X) (r : ℝ≥0∞) :
    mk '' closedBall x r = closedBall (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  rw [image_mk_eq_preimage, preimage_val_emetricClosedBall]

@[simp]
theorem preimage_mk_emetricClosedBall (x : WithRPowDist X α hα₀ hα₁) (d : ℝ≥0∞) :
    mk ⁻¹' closedBall x d = closedBall x.val (d ^ α⁻¹) := by
  apply injective_mk.image_injective
  rw [image_mk_emetricClosedBall, Set.image_preimage_eq _ surjective_mk,
    ENNReal.rpow_inv_rpow hα₀.ne']

@[simp]
theorem image_val_emetricClosedBall (x : WithRPowDist X α hα₀ hα₁) (d : ℝ≥0∞) :
    val '' closedBall x d = closedBall x.val (d ^ α⁻¹) := by
  rw [image_val_eq_preimage, preimage_mk_emetricClosedBall]

@[simp]
theorem ediam_image_val (s : Set (WithRPowDist X α hα₀ hα₁)) : diam (val '' s) = diam s ^ α⁻¹ := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  simp [diam_le_iff, ENNReal.rpow_inv_le_iff hα₀]

@[simp]
theorem ediam_preimage_mk (s : Set (WithRPowDist X α hα₀ hα₁)) :
    diam (mk ⁻¹' s) = diam s ^ α⁻¹ := by
  rw [← image_val_eq_preimage, ediam_image_val]

@[simp]
theorem ediam_preimage_val (s : Set X) :
    diam (val ⁻¹' s : Set (WithRPowDist X α hα₀ hα₁)) = diam s ^ α := by
  rw [← ENNReal.rpow_inv_rpow hα₀.ne' (diam _), ← ediam_preimage_mk,
    ← Set.preimage_comp, val_comp_mk, Set.preimage_id]

@[simp]
theorem ediam_image_mk (s : Set X) :
    diam (mk '' s : Set (WithRPowDist X α hα₀ hα₁)) = diam s ^ α := by
  simp [image_mk_eq_preimage]

end PseudoEMetricSpace

instance [EMetricSpace X] : EMetricSpace (WithRPowDist X α hα₀ hα₁) :=
  .ofT0PseudoEMetricSpace _

instance [Dist X] : Dist (WithRPowDist X α hα₀ hα₁) where
  dist x y := dist x.val y.val ^ α

@[simp]
theorem dist_mk_mk [Dist X] (x y : X) :
    dist (mk x : WithRPowDist X α hα₀ hα₁) (mk y) = dist x y ^ α :=
  rfl

section PseudoMetricSpace

variable [PseudoMetricSpace X]

instance : PseudoMetricSpace (WithRPowDist X α hα₀ hα₁) :=
  letI aux : PseudoMetricSpace (WithRPowDist X α hα₀ hα₁) :=
    PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
      (by rintro ⟨x⟩ ⟨y⟩; simp [hα₀, hα₀.le, edist_ne_top])
      (by rintro ⟨x⟩ ⟨y⟩; simp [ENNReal.toReal_rpow, dist_edist])
  aux.replaceBornology fun s ↦ by
    rw [← isBounded_preimage_mk_iff, Metric.isBounded_iff, Metric.isBounded_iff]
    constructor
    · rintro ⟨C, hC⟩
      use C ^ α
      rintro ⟨x⟩ hx ⟨y⟩ hy
      grw [dist_mk_mk, hC hx hy]
    · rintro ⟨C, hC⟩
      use C ^ α⁻¹
      intro x hx y hy
      grw [← hC hx hy, dist_mk_mk, Real.rpow_rpow_inv (by positivity) hα₀.ne']

open Metric

@[simp]
theorem dist_val_val (x y : WithRPowDist X α hα₀ hα₁) : dist x.val y.val = dist x y ^ α⁻¹ := by
  cases x; cases y
  rw [dist_mk_mk, Real.rpow_rpow_inv dist_nonneg hα₀.ne']

@[simp]
theorem preimage_val_ball (x : X) {r : ℝ} (hr : 0 ≤ r) :
    val ⁻¹' ball x r = ball (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [Real.rpow_lt_rpow_iff]

@[simp]
theorem image_mk_ball (x : X) {r : ℝ} (hr : 0 ≤ r) :
    mk '' ball x r = ball (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  rw [image_mk_eq_preimage, preimage_val_ball x hr]

@[simp]
theorem preimage_mk_ball (x : WithRPowDist X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    mk ⁻¹' ball x r = ball x.val (r ^ α⁻¹) := by
  apply injective_mk.image_injective
  rw [image_mk_ball _ (by positivity), Set.image_preimage_eq _ surjective_mk,
    Real.rpow_inv_rpow hr hα₀.ne']

@[simp]
theorem image_val_ball (x : WithRPowDist X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    val '' ball x r = ball x.val (r ^ α⁻¹) := by
  rw [image_val_eq_preimage, preimage_mk_ball _ hr]

@[simp]
theorem preimage_val_closedBall (x : X) {r : ℝ} (hr : 0 ≤ r) :
    val ⁻¹' closedBall x r = closedBall (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [Real.rpow_le_rpow_iff]

@[simp]
theorem image_mk_closedBall (x : X) {r : ℝ} (hr : 0 ≤ r) :
    mk '' closedBall x r = closedBall (mk x : WithRPowDist X α hα₀ hα₁) (r ^ α) := by
  rw [image_mk_eq_preimage, preimage_val_closedBall x hr]

@[simp]
theorem preimage_mk_closedBall (x : WithRPowDist X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    mk ⁻¹' closedBall x r = closedBall x.val (r ^ α⁻¹) := by
  apply injective_mk.image_injective
  rw [image_mk_closedBall _ (by positivity), Set.image_preimage_eq _ surjective_mk,
    Real.rpow_inv_rpow hr hα₀.ne']

@[simp]
theorem image_val_closedBall (x : WithRPowDist X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    val '' closedBall x r = closedBall x.val (r ^ α⁻¹) := by
  rw [image_val_eq_preimage, preimage_mk_closedBall _ hr]

end PseudoMetricSpace

instance [MetricSpace X] : MetricSpace (WithRPowDist X α hα₀ hα₁) :=
  .ofT0PseudoMetricSpace _

end WithRPowDist

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X] {α : ℝ} {hα₀ : 0 < α} {hα₁ : α ≤ 1} {μ : Measure X}

open WithRPowDist

variable (α hα₀ hα₁) in
def withRPowDist (μ : Measure X) : Measure (WithRPowDist X α hα₀ hα₁) :=
  μ.map .mk

theorem withRPowDist_apply (μ : Measure X) (s : Set (WithRPowDist X α hα₀ hα₁)) :
    μ.withRPowDist α hα₀ hα₁ s = μ (.mk ⁻¹' s) := by
  rw [withRPowDist, measurableEmbedding_mk.map_apply]

instance [IsFiniteMeasure μ] : IsFiniteMeasure (μ.withRPowDist α hα₀ hα₁) := by
  unfold withRPowDist
  infer_instance

instance [SigmaFinite μ] : SigmaFinite (μ.withRPowDist α hα₀ hα₁) :=
  measurableEquiv.symm.measurableEmbedding.sigmaFinite_map

instance [SFinite μ] : SFinite (μ.withRPowDist α hα₀ hα₁) := by
  unfold withRPowDist
  infer_instance

section TopologicalSpace

variable [TopologicalSpace X]

-- TODO: generalize to a homeomorphism
instance [IsLocallyFiniteMeasure μ] : IsLocallyFiniteMeasure (μ.withRPowDist α hα₀ hα₁) where
  finiteAtNhds := by
    rintro ⟨x⟩
    rcases μ.finiteAt_nhds x with ⟨s, hsx, hμs⟩
    simp only [homeomorph.nhds_eq_comap, homeomorph_apply]
    refine ⟨_, Filter.preimage_mem_comap hsx, ?_⟩
    rwa [withRPowDist, measurableEmbedding_mk.map_apply]

instance [IsFiniteMeasureOnCompacts μ] : IsFiniteMeasureOnCompacts (μ.withRPowDist α hα₀ hα₁) where
  lt_top_of_isCompact := by
    intro K hK
    rw [withRPowDist_apply, ← image_val_eq_preimage]
    exact hK.image continuous_val |>.measure_lt_top

instance [μ.OuterRegular] : (μ.withRPowDist α hα₀ hα₁).OuterRegular := by
  refine ⟨fun A hA r hr ↦ ?_⟩
  rw [withRPowDist_apply] at hr
  rcases Set.exists_isOpen_lt_of_lt _ r hr with ⟨U, hAU, hUo, hU⟩
  refine ⟨val ⁻¹' U, ?_, hUo.preimage continuous_val, by rwa [withRPowDist_apply]⟩
  rintro ⟨x⟩ hx
  exact hAU hx

instance [μ.InnerRegular] : (μ.withRPowDist α hα₀ hα₁).InnerRegular := by
  constructor
  rw [withRPowDist, ← measurableEquiv_symm_apply]
  exact InnerRegular.innerRegular.map' _ measurable_mk fun K hK ↦ hK.image continuous_mk

instance [μ.WeaklyRegular] : (μ.withRPowDist α hα₀ hα₁).WeaklyRegular where
  innerRegular := by
    rw [withRPowDist, ← measurableEquiv_symm_apply]
    apply WeaklyRegular.innerRegular.map'
    · exact fun U hU ↦ hU.preimage continuous_mk
    · intro K hK
      rwa [measurableEquiv_symm_apply, ← homeomorph_symm_apply, Homeomorph.isClosed_image]

instance [μ.InnerRegularCompactLTTop] : (μ.withRPowDist α hα₀ hα₁).InnerRegularCompactLTTop where
  innerRegular := by
    rw [withRPowDist, ← measurableEquiv_symm_apply]
    apply InnerRegularCompactLTTop.innerRegular.map'
    · rintro U ⟨hUm, hμU⟩
      rw [MeasurableEquiv.map_apply] at hμU
      exact ⟨hUm.preimage <| MeasurableEquiv.measurable _, hμU⟩
    · exact fun K hK ↦ hK.image continuous_mk

instance [μ.Regular] : (μ.withRPowDist α hα₀ hα₁).Regular where
  innerRegular := by
    rw [withRPowDist, ← measurableEquiv_symm_apply]
    apply Regular.innerRegular.map'
    · exact fun U hU ↦ hU.preimage continuous_mk
    · exact fun K hK ↦ hK.image continuous_mk

end TopologicalSpace

@[simp]
theorem withRPowDist_hausdorffMeasure [EMetricSpace X] [BorelSpace X] (d : ℝ) :
    (μH[d] : Measure X).withRPowDist α hα₀ hα₁ = μH[d / α] := by
  ext s hs
  simp only [withRPowDist_apply, hausdorffMeasure_apply,
    ← (Surjective.piMap fun _ : ℕ ↦ (@injective_mk X α hα₀ hα₁).preimage_surjective).iInf_comp,
    Pi.map_apply, ← Set.preimage_iUnion, surjective_mk.preimage_subset_preimage_iff,
    ediam_preimage_mk, surjective_mk.nonempty_preimage, ENNReal.rpow_inv_le_iff hα₀]
  apply (ENNReal.rpow_left_surjective hα₀.ne').iSup_congr
  intro r
  simp [← ENNReal.rpow_mul, div_eq_inv_mul, pos_iff_ne_zero, hα₀, hα₀.le]

instance [PseudoMetricSpace X] [IsUnifLocDoublingMeasure μ] :
    IsUnifLocDoublingMeasure (μ.withRPowDist α hα₀ hα₁) where
  exists_measure_closedBall_le_mul'' := by
    use IsUnifLocDoublingMeasure.scalingConstantOf μ (2 ^ α⁻¹)
    rcases (nhdsGT_basis _).eventually_iff.mp
      (IsUnifLocDoublingMeasure.eventually_measure_le_scaling_constant_mul μ (2 ^ α⁻¹))
      with ⟨r, hr₀, hr⟩
    filter_upwards [Ioo_mem_nhdsGT (show 0 < r ^ α by positivity)]
    rintro a ⟨ha₀, ha⟩ ⟨x⟩
    simpa (disch := positivity) [withRPowDist_apply, Real.mul_rpow, Real.rpow_pos_of_pos,
      Real.rpow_inv_lt_iff_of_pos, *] using fun h ↦ @hr (a ^ α⁻¹) h x

end MeasureTheory.Measure
