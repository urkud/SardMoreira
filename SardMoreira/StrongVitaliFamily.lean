import Mathlib

open MeasureTheory Measure Metric Filter
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X] {m : MeasurableSpace X}

structure StrongVitaliFamily (μ : Measure X) extends VitaliFamily μ where
  exists_covering_of_measure_zero' {s : Set X} {p : X → Set X → Prop} (hs₀ : μ s = 0)
    (hfreq : ∀ x ∈ s, ∃ᶠ t in toVitaliFamily.filterAt x, p x t) {ε : ℝ≥0} (hε : ε ≠ 0) :
    ∃ t : Set (X × Set X), (∀ y ∈ t, y.1 ∈ s) ∧ (∀ y ∈ t, p y.1 y.2) ∧
      (∑' y : t, μ y.1.2 < ε) ∧ s ⊆ ⋃ y ∈ t, y.2

@[simp]
theorem VitaliFamily.filterAt_enlarge {μ : Measure X} (v : VitaliFamily μ) {δ : ℝ} (δpos : 0 < δ) :
    (v.enlarge δ δpos).filterAt = v.filterAt := by
  ext1 x
  suffices {t | MeasurableSet t → (interior t).Nonempty → ¬t ⊆ closedBall x δ →
      t ∈ v.setsAt x} ∈ (𝓝 x).smallSets by
    simpa [VitaliFamily.filterAt, VitaliFamily.enlarge, ← sup_principal, inf_sup_left,
      mem_inf_principal]
  filter_upwards [eventually_smallSets_subset.mpr (closedBall_mem_nhds _ δpos)]
  simp +contextual

/- Aristotle took a wrong turn (reason code: 9). Please try again. -/
@[simps toVitaliFamily]
def StrongVitaliFamily.enlarge {μ : Measure X} (v : StrongVitaliFamily μ) (δ : ℝ) (δpos : 0 < δ) :
    StrongVitaliFamily μ where
  toVitaliFamily := v.toVitaliFamily.enlarge δ δpos
  exists_covering_of_measure_zero' := by
    simp only [VitaliFamily.filterAt_enlarge]
    exact v.exists_covering_of_measure_zero'

/-
This is just wrong with the family we use in Mathlib.
Just make all the sets in the family avoid one point.

@[simps toVitaliFamily]
def Vitali.strongVitaliFamily [OpensMeasurableSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [μ.OuterRegular] (C : ℝ≥0)
    (h : ∀ x : X, ∃ᶠ (r : ℝ) in 𝓝[>] 0, μ (closedBall x (3 * r)) ≤ C * μ (closedBall x r)) :
    StrongVitaliFamily μ where
  toVitaliFamily := Vitali.vitaliFamily μ C h
  exists_covering_of_measure_zero' := by
    intro s p hμs hps


def IsUnifLocDoublingMeasure.strongVitaliFamily (μ : Measure X) [IsUnifLocDoublingMeasure μ]
    [SecondCountableTopology X] [BorelSpace X] [IsLocallyFiniteMeasure μ] (K : ℝ) :
    StrongVitaliFamily μ where
  toVitaliFamily := IsUnifLocDoublingMeasure.vitaliFamily μ K
  exists_covering_of_measure_zero' := by
    rw [IsUnifLocDoublingMeasure.vitaliFamily_def]
    -- Without these, Lean fails to find proofs by unification
    simp only [← Vitali.strongVitaliFamily_toVitaliFamily,
      ← StrongVitaliFamily.enlarge_toVitaliFamily]
    exact (Vitali.strongVitaliFamily μ _ _).enlarge _ _ |>.exists_covering_of_measure_zero'
-/

instance (priority := 100) Besicovitch.isUnifLocDoublingMeasure
    [SecondCountableTopology X] [OpensMeasurableSpace X] [HasBesicovitchCovering X]
    (μ : Measure X) [SFinite μ] [μ.OuterRegular] :
    IsUnifLocDoublingMeasure μ where
  exists_measure_closedBall_le_mul'' := by
    rcases HasBesicovitchCovering.no_satelliteConfig (α := X) with ⟨N, τ, hτ, hN⟩
    have := exist_disjoint_covering_families (α := X) hτ hN

def Besicovitch.strongVitaliFamily [SecondCountableTopology X] [OpensMeasurableSpace X]
    [HasBesicovitchCovering X] (μ : Measure X) [SFinite μ] [μ.OuterRegular] :
    StrongVitaliFamily μ where
  toVitaliFamily := Besicovitch.vitaliFamily μ
  exists_covering_of_measure_zero' := by
    intro s p hμs hps ε hε
    have := Besicovitch.exists_closedBall_covering_tsum_measure_le μ (ε := ε / 2)
      (ENNReal.half_pos <| by positivity).ne'
      (fun x ↦ {r | p x (closedBall x r)}) s ?_
    · rcases this with ⟨t, r, htc, hts, htp, hsub, htsum⟩
      refine ⟨(fun x ↦ (x, closedBall x (r x))) '' t, ?_, ?_, ?_, ?_⟩
      · simpa using hts
      · simpa using htp
      · rw [tsum_image (g := fun x ↦ (x, closedBall x (r x))) (f := fun x ↦ μ x.2) (s := t)]
        · grw [htsum, hμs, zero_add]
          apply ENNReal.half_lt_self <;> simp [hε]
        · simp +contextual [Set.InjOn]
      · rwa [Set.biUnion_image]
    · intro x hxs δ hδ
      simp only [(Metric.nhds_basis_ball.vitaliFamily _).frequently_iff] at hps
      rcases hps x hxs (δ / 2) (by positivity) with ⟨_, ⟨⟨r, hr₀ : 0 < r, rfl⟩, hsub⟩, hp⟩
      refine ⟨min r (δ / 2), ?_, by positivity, by simp [hδ]⟩
      apply min_rec
      · exact fun _ ↦ hp
      · intro hle
        suffices closedBall x r = closedBall x (δ / 2) by simpa [this] using hp
        exact (hsub.trans ball_subset_closedBall).antisymm (by simp only; gcongr)
