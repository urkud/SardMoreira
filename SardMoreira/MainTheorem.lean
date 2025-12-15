import Mathlib
import SardMoreira.ContDiffMoreiraHolder
import SardMoreira.ImplicitFunction
import SardMoreira.LinearAlgebra
import SardMoreira.ChartEstimates
import SardMoreira.WithRPowDist

open scoped unitInterval NNReal Topology ENNReal
open MeasureTheory Measure Metric

local notation "dim" => Module.finrank ℝ

-- TODO: generalize to semilinear maps
protected noncomputable def ContinuousLinearMap.finrank {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    (f : M →L[R] N) : ℕ :=
  Module.finrank R (LinearMap.range f)

theorem ContinuousLinearMap.finrank_comp_eq_left_of_surjective {R M N P : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [AddCommMonoid P] [Module R P] [TopologicalSpace P]
    (g : N →L[R] P) {f : M →L[R] N} (hf : Function.Surjective f) :
    (g ∘L f).finrank = g.finrank := by
  -- Since $f$ is surjective, the image of $g \circ f$ is the same as the image of $g$.
  have h_range : LinearMap.range (g.comp f) = LinearMap.range g :=
    SetLike.coe_injective <| hf.range_comp g
  rw [ContinuousLinearMap.finrank, ContinuousLinearMap.finrank, h_range]

theorem ContinuousLinearMap.finrank_comp_eq_right_of_injective {R M N P : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [AddCommMonoid P] [Module R P] [TopologicalSpace P]
    {g : N →L[R] P} (hg : Function.Injective g) (f : M →L[R] N) :
    (g ∘L f).finrank = f.finrank := by
  -- Since $g$ is injective, the range of $g \circ f$ is isomorphic to the range of $f$.
  have h_iso : LinearMap.range (g.comp f) ≃ₗ[R] LinearMap.range f := by
    symm;
    refine' { Equiv.ofBijective ( fun x => ⟨ g x, by aesop ⟩ ) ⟨ fun x y hxy => _, fun x => _ ⟩ with .. } <;> aesop;
  exact h_iso.finrank_eq

@[simp]
theorem ContinuousLinearEquiv.finrank_comp_left {R M N N' : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [AddCommMonoid N'] [Module R N'] [TopologicalSpace N']
    (e : N ≃L[R] N') (f : M →L[R] N) : (e ∘L f : M →L[R] N').finrank = f.finrank := by
  apply ContinuousLinearMap.finrank_comp_eq_right_of_injective
  exact e.injective

@[simp]
theorem ContinuousLinearEquiv.finrank_comp_right {R M M' N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [AddCommMonoid M'] [Module R M'] [TopologicalSpace M']
    (f : M →L[R] N) (e : M' ≃L[R] M) : (f ∘L e : M' →L[R] N).finrank = f.finrank := by
  apply ContinuousLinearMap.finrank_comp_eq_left_of_surjective
  exact e.surjective

theorem LipschitzWith.hausdorffMeasure_image_null {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] {K : NNReal} {f : X → Y}
    (h : LipschitzWith K f) {d : ℝ} (hd : 0 ≤ d) {s : Set X} (hs : μH[d] s = 0) :
    μH[d] (f '' s) = 0 := by
  grw [← nonpos_iff_eq_zero, h.hausdorffMeasure_image_le hd, hs, mul_zero]

/-- Moreira's upper estimate on the Hausdorff dimension of the image of the set of points $x$
such that `fderiv ℝ f x` has rank at most `p < min n m`,
provided that `f` is a $$C^{k+(\alpha)}$$-map
from an `n`-dimensional space to an `m`-dimensional space.

Note that the estimate does not depend on `m`. -/
noncomputable def sardMoreiraBound (n k : ℕ) (α : I) (p : ℕ) : ℝ≥0 :=
  p + (n - p) / (k + ⟨α, α.2.1⟩)

theorem monotone_sardMoreiraBound (n : ℕ) {k : ℕ} (hk : k ≠ 0) (α : I) :
    Monotone (sardMoreiraBound n k α) := by
  apply monotone_nat_of_le_succ
  intro p
  rcases α with ⟨α, hα₀, hα₁⟩
  simp only [sardMoreiraBound, field]
  rw [← NNReal.coe_le_coe]
  push_cast [tsub_add_eq_tsub_tsub]
  grw [@NNReal.coe_sub_def _ 1, ← le_max_left, ← sub_nonneg]
  push_cast
  linarith only [hα₀, show (1 : ℝ) ≤ k by norm_cast; grind]

@[gcongr]
theorem sardMoreiraBound_le_sardMoreiraBound {m n k l p q : ℕ} (hl : l ≠ 0) (hmn : m ≤ n)
    (hlk : l ≤ k) (hpq : p ≤ q) (α : I) :
    sardMoreiraBound m k α p ≤ sardMoreiraBound n l α q := by
  grw [← monotone_sardMoreiraBound n hl α hpq]
  unfold sardMoreiraBound
  gcongr

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {k p : ℕ} {α : I}

namespace Moreira2001

theorem mkMetric'Pre_image_piProd_fst_null_of_isBigO_of_null
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    [MeasurableSpace G] [BorelSpace G]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    {f : E × F → G} {s : Set (E × F)} {n : ℕ} (hsm : MeasurableSet s) (hk : k ≠ 0) (hnp : dim E < n)
    (hn : dim E + dim F ≤ n)
    (h_contDiff : ∃ U ∈ 𝓝ˢ s, ContDiffOn ℝ 1 f U)
    (h_isBigO : ∀ x ∈ s, (fun y ↦ f (x.1, y) - f x) =O[𝓝 x.2] (fun y ↦ ‖y - x.2‖ ^ (k + α : ℝ)))
    (hμ₀ : μH[dim E].prod (μH[dim F]) s = 0) {r : ℝ≥0∞} (hr : 0 < r) :
    (OuterMeasure.mkMetric'.pre (fun s ↦ EMetric.diam s ^ (sardMoreiraBound n k α (dim E) : ℝ)) r)
      (Pi.prod Prod.fst f '' s) = 0 := by

  sorry

theorem mkMetric'Pre_image_piProd_fst_null_of_isLittleO
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    [MeasurableSpace G] [BorelSpace G]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    {μ : Measure (E × F)} [μ.IsAddHaarMeasure]
    {f : E × F → G} {s : Set (E × F)} {n : ℕ} (hsm : MeasurableSet s) (hk : k ≠ 0) (hnp : dim E < n)
    (hn : dim E + dim F ≤ n)
    (h_contDiff : ∃ U ∈ 𝓝ˢ s, ContDiffOn ℝ 1 f U)
    (h_isBigO : ∀ x ∈ s, (fun y ↦ f (x.1, y) - f x) =O[𝓝 x.2] (fun y ↦ ‖y - x.2‖ ^ (k + α : ℝ)))
    (hμ₀ : μ s = 0) {r : ℝ≥0∞} (hr : 0 < r) :
    (OuterMeasure.mkMetric'.pre (fun s ↦ EMetric.diam s ^ (sardMoreiraBound n k α (dim E) : ℝ)) r)
      (Pi.prod Prod.fst f '' s) = 0 := by
  sorry

theorem hausdorffMeasure_image_piProd_fst_null_of_isBigO_isLittleO
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    [MeasurableSpace G] [BorelSpace G]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    {f : E × F → G} {s : Set (E × F)} {n : ℕ} (hk : k ≠ 0) (hnp : dim E < n)
    (hn : dim E + dim F ≤ n)
    (h_contDiff : ∀ x ∈ s, ContDiffAt ℝ 1 f x)
    (h_isBigO : ∀ x ∈ s, (fun y ↦ f (x.1, y) - f x) =O[𝓝 x.2] (fun y ↦ ‖y - x.2‖ ^ (k + α : ℝ)))
    (h_isLittleO : ∀ᵐ x ∂(μH[dim E].prod μH[dim F]), x ∈ s →
      (fun y ↦ f (x.1, y) - f x) =o[𝓝 x.2] (fun y ↦ ‖y - x.2‖ ^ (k + α : ℝ))) :
    μH[sardMoreiraBound n k α (dim E)] (Pi.prod Prod.fst f '' s) = 0 := by
  generalize hd : (sardMoreiraBound n k α (dim E) : ℝ) = d
  generalize hg : Pi.prod Prod.fst f = g
  suffices ∀ r, 0 < r → (OuterMeasure.mkMetric'.pre (fun s ↦ EMetric.diam s ^ d) r) (g '' s) = 0 by
    simpa only [hausdorffMeasure, ← toOuterMeasure_apply, mkMetric_toOuterMeasure,
      OuterMeasure.mkMetric, OuterMeasure.mkMetric', OuterMeasure.iSup_apply, ENNReal.iSup_eq_zero]
  intro r hr
  sorry
  -- wlog hs : Bornology.IsBounded s generalizing s
  -- · rw [← Set.inter_univ s, ← iUnion_ball_nat 0, Set.inter_iUnion, Set.image_iUnion,
  --     measure_iUnion_null_iff]
  --   intro N
  --   apply this
  --   · exact hsm.inter measurableSet_ball
  --   · refine h_contDiff.imp fun U ↦ And.imp_left <| Filter.le_def.mp ?_ _
  --     gcongr
  --     exact Set.inter_subset_left
  --   · exact fun x hx ↦ (h_isBigO x hx.1)


theorem hausdorffMeasure_image_piProd_fst_null_of_fderiv_comp_inr_zero
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace G] [BorelSpace G]
    [Nontrivial F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    {f : E × F → G} {s U : Set (E × F)} (hf : ContDiffMoreiraHolderOn k α f s U) (hk : k ≠ 0)
    (hs : ∀ x ∈ s, fderiv ℝ f x ∘L .inr ℝ E F = 0) :
    μH[sardMoreiraBound (dim E + dim F) k α (dim E)]
      (Pi.prod Prod.fst f '' s) = 0 := by
  rcases Nat.exists_add_one_eq.mpr hk.bot_lt with ⟨k, rfl⟩
  suffices ∀ ψ ∈ (Atlas.main k α s).charts,
      μH[sardMoreiraBound (dim E + dim F) (k + 1) α (dim E)]
        ((Pi.prod Prod.fst f ∘ ψ) '' ψ.set) = 0 by
    rw [← measure_biUnion_null_iff] at this
    · refine measure_mono_null ?_ this
      simp only [Set.image_comp, ← Set.image_iUnion₂]
      gcongr
      refine (Atlas.main k α s).subset_biUnion_isLargeAt.trans ?_
      gcongr
      apply Set.sep_subset
    · apply Atlas.countable
  intro ψ hψ
  set g := Pi.prod Prod.fst (f ∘ ψ)
  suffices μH[sardMoreiraBound (dim E + dim F) (k + 1) α (dim E)] (g '' ψ.set) = 0 by
    simpa [g] using this
  apply hausdorffMeasure_image_piProd_fst_null_of_isBigO_isLittleO
  · simp
  · simp [Module.finrank_pos]
  · grw [ψ.finrank_le]
  · intro x hx
    refine .comp _ ?_ (ψ.contDiffAt hx)
    exact hf.contDiffMoreiraHolderAt (ψ.mapsTo hx) |>.contDiffAt.of_le (by simp)
  · intro x hx
    push_cast
    apply Atlas.isBigO_main_sub_of_fderiv_zero_right hψ hx
    · filter_upwards [eventually_mem_nhdsWithin] with x hx using hf.contDiffMoreiraHolderAt hx
    · filter_upwards [eventually_mem_nhdsWithin] using hs
  · push_cast
    filter_upwards [Besicovitch.ae_tendsto_measure_sectr_inter_closedBall_div
      (μH[dim E]) (μH[dim ψ.Dom]) (measurableSet_closure (s := ψ.set))] with x hx hψx
    apply Atlas.isLittleO_main_sub_of_fderiv_zero_right hψ hψx
    · filter_upwards [eventually_mem_nhdsWithin] with y hy using hf.contDiffMoreiraHolderAt hy
    · filter_upwards [eventually_mem_nhdsWithin] using hs
    · convert hx
      simp [Set.indicator_of_mem (subset_closure hψx)]

theorem hausdorffMeasure_image_piProd_fst_null_of_finrank_eq
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace G] [BorelSpace G]
    [Nontrivial F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    {f : E × F → G} {s U : Set (E × F)} (hf : ContDiffMoreiraHolderOn k α f s U) (hk : k ≠ 0)
    (hs : ∀ x ∈ s, dim (LinearMap.range <| fderiv ℝ (Pi.prod Prod.fst f) x) = dim E) :
    μH[sardMoreiraBound (dim E + dim F) k α (dim E)]
      (Pi.prod Prod.fst f '' s) = 0 := by
  apply hausdorffMeasure_image_piProd_fst_null_of_fderiv_comp_inr_zero hf hk
  intro x hx
  rw [← ContinuousLinearMap.finrank_range_prod_fst_iff_comp_inr_eq_zero, ← hs x hx]
  suffices fderiv ℝ (Pi.prod Prod.fst f) x = .prod (.fst ℝ E F) (fderiv ℝ f x) by
    -- TODO: introduce&use `ContinuousLinearMap.rank`/`ContinuousLinearMap.finrank`?
    generalize H : fderiv ℝ (Pi.prod Prod.fst f) x = f'
    rw [H] at this
    subst f'
    rfl
  unfold Pi.prod
  rw [DifferentiableAt.fderiv_prodMk (by fun_prop), fderiv_fst]
  exact hf.contDiffMoreiraHolderAt hx |>.differentiableAt hk

theorem hausdorffMeasure_image_nhdsWithin_null_of_finrank_eq [MeasurableSpace F] [BorelSpace F]
    (hp_dom : p < dim E) (hp_cod : p < dim F) (hk : k ≠ 0) {f : E → F} {s U : Set E}
    (hf : ContDiffMoreiraHolderOn k α f s U)
    (hs : ∀ x ∈ s, dim (LinearMap.range <| fderiv ℝ f x) = p) {x : E} (hx : x ∈ s) :
    ∃ t ∈ 𝓝[s] x, μH[sardMoreiraBound (dim E) k α p] (f '' t) = 0 := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by grind)
  have : FiniteDimensional ℝ F := .of_finrank_pos (Nat.zero_lt_of_lt hp_cod)
  have hker := ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range (fderiv ℝ f x)
  have hrange := Submodule.ClosedComplemented.of_finiteDimensional (LinearMap.range (fderiv ℝ f x))
  rcases hf.exists_openPartialHomeomorph_conj_piProd_fst hk hx hker hrange
    with ⟨epq, epr, g, hx_epq, hepqU, hepq, hepq_symm, heqOn⟩
  use s ∩ epq.source, inter_mem_nhdsWithin _ (epq.open_source.mem_nhds hx_epq)
  set t := epq.target ∩ epq.symm ⁻¹' s
  have heqOn_g : Set.EqOn (Prod.snd ∘ epr ∘ f ∘ epq.symm) g epq.target := heqOn.comp_left
  have hg : ContDiffMoreiraHolderOn k α g t epq.target := by
    refine .congr_eqOn ?_ heqOn_g
    refine .continuousLinearMap_comp ?_
      (.snd ℝ (LinearMap.range (fderiv ℝ f x)) (LinearMap.ker hrange.choose))
    refine .continuousLinearMap_comp ?_ epr.toContinuousLinearMap
    refine hf.comp hepq_symm (epq.symm_mapsTo.mono_right hepqU) ?_ hk
    exact (Set.mapsTo_preimage _ _).mono_left Set.inter_subset_right
  have hrange_ker :
      dim (LinearMap.range (fderiv ℝ f x)) + dim (LinearMap.ker (fderiv ℝ f x)) = dim E :=
    LinearMap.finrank_range_add_finrank_ker (fderiv ℝ f x : E →ₗ[ℝ] F)
  have : Nontrivial ↥(LinearMap.ker (fderiv ℝ f x)) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rwa [← hrange_ker, hs x hx, lt_add_iff_pos_right] at hp_dom
  have := hausdorffMeasure_image_piProd_fst_null_of_finrank_eq hg hk ?_
  · rw [hrange_ker, hs x hx] at this
    refine measure_mono_null (Set.mapsTo_iff_image_subset.mp ?_)
      (epr.symm.lipschitz.hausdorffMeasure_image_null (by positivity) this)
    rintro a ⟨has, ha⟩
    rw [epr.image_symm_eq_preimage, Set.mem_preimage, Set.mem_image]
    refine ⟨epq a, ⟨epq.mapsTo ha, ?_⟩, ?_⟩
    · simp [*]
    · rw [← heqOn (epq.mapsTo ha)]
      simp [ha]
  · intro a ha
    simp only [← ContinuousLinearMap.finrank.eq_1] at *
    rw [← (heqOn.eventuallyEq_of_mem <| epq.open_target.mem_nhds ha.1).fderiv_eq, epr.comp_fderiv,
      epr.finrank_comp_left, fderiv_comp, ContinuousLinearMap.finrank_comp_eq_left_of_surjective,
      hs x hx, hs _ ha.2]
    · apply Function.LeftInverse.surjective (g := fderiv ℝ epq (epq.symm a))
      rw [Function.leftInverse_iff_comp, ← ContinuousLinearMap.coe_comp',
        ← ContinuousLinearMap.coe_id' (R₁ := ℝ), DFunLike.coe_fn_eq]
      have : fderiv ℝ (epq.symm ∘ epq) (epq.symm a) = .id ℝ E := by
        rw [(epq.leftInvOn.eqOn.eventuallyEq_of_mem _).fderiv_eq, fderiv_id]
        exact epq.open_source.mem_nhds <| epq.symm_mapsTo ha.1
      rwa [fderiv_comp, epq.rightInvOn ha.1] at this
      · rw [epq.rightInvOn ha.1]
        exact hepq_symm.contDiffMoreiraHolderAt ha |>.differentiableAt hk
      · exact hepq.contDiffMoreiraHolderAt ⟨epq.symm_mapsTo ha.1, ha.2⟩ |>.differentiableAt hk
    · exact hf.contDiffMoreiraHolderAt ha.2 |>.differentiableAt hk
    · exact hepq_symm.contDiffMoreiraHolderAt ha |>.differentiableAt hk

theorem hausdorffMeasure_image_null_of_finrank_eq [MeasurableSpace F] [BorelSpace F]
    (hp_dom : p < dim E)
    (hp_cod : p < dim F) (hk : k ≠ 0) {f : E → F} {s U : Set E}
    (hf : ContDiffMoreiraHolderOn k α f s U)
    (hs : ∀ x ∈ s, dim (LinearMap.range <| fderiv ℝ f x) = p) :
    μH[sardMoreiraBound (dim E) k α p] (f '' s) = 0 := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by grind)
  rw [← coe_toOuterMeasure, ← OuterMeasure.comap_apply]
  refine measure_null_of_locally_null _ fun x hx ↦ ?_
  apply hausdorffMeasure_image_nhdsWithin_null_of_finrank_eq <;> assumption

end Moreira2001

theorem hausdorffMeasure_sardMoreiraBound_image_null_of_finrank_le
    [MeasurableSpace F] [BorelSpace F]
    (hp_dom : p < dim E)
    (hp_cod : p < dim F) (hk : k ≠ 0) {f : E → F} {s U : Set E}
    (hf : ContDiffMoreiraHolderOn k α f s U)
    (hs : ∀ x ∈ s, dim (LinearMap.range <| fderiv ℝ f x) ≤ p) :
    μH[sardMoreiraBound (dim E) k α p] (f '' s) = 0 := by
  -- Apply the Moreira2001 theorem to each of the sets where the rank is exactly `p' ≤ p`.
  have h_apply : ∀ p' ≤ p,
      μH[sardMoreiraBound (dim E) k α p']
        (f '' {x ∈ s | dim (LinearMap.range (fderiv ℝ f x)) = p'}) = 0 := by
    intro p' hp'
    apply Moreira2001.hausdorffMeasure_image_null_of_finrank_eq
      (by grind) (by grind) hk (U := U)
    · exact hf.subset_left Set.inter_subset_left
    · simp
  -- Since $s$ is the union of the sets where the rank is exactly $p'$ for $p' \leq p$,
  -- we can use the countable subadditivity of the Hausdorff measure.
  have h_union :
      f '' s = ⋃ p' ≤ p, f '' {x ∈ s | dim (LinearMap.range (fderiv ℝ f x)) = p'} := by
    ext y
    simp only [Set.mem_image, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    exact ⟨fun ⟨x, hx, hx'⟩ ↦ ⟨_, hs x hx, x, ⟨hx, rfl⟩, hx'⟩,
      fun ⟨i, hi, x, hx, hx'⟩ ↦ ⟨x, hx.1, hx'⟩⟩
  simp only [h_union, measure_iUnion_null_iff]
  intro p' hp'
  rw [← nonpos_iff_eq_zero, ← h_apply p' hp']
  apply hausdorffMeasure_mono
  exact monotone_sardMoreiraBound _ hk _ hp'

theorem dimH_image_le_sardMoreiraBound_of_finrank_le
    (hp_dom : p < dim E)
    (hp_cod : p < dim F) (hk : k ≠ 0) {f : E → F} {s U : Set E}
    (hf : ContDiffMoreiraHolderOn k α f s U)
    (hs : ∀ x ∈ s, dim (LinearMap.range <| fderiv ℝ f x) ≤ p) :
    dimH (f '' s) ≤ sardMoreiraBound (dim E) k α p := by
  borelize F
  apply dimH_le_of_hausdorffMeasure_ne_top
  simp [hausdorffMeasure_sardMoreiraBound_image_null_of_finrank_le hp_dom hp_cod hk hf hs]
