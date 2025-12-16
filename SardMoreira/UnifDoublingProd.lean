import Mathlib

open scoped Topology Filter
open MeasureTheory Measure Metric

/--
The product of two uniformly locally doubling measures is a uniformly locally doubling measure,
assuming the second one is s-finite.
-/
instance IsUnifLocDoublingMeasure.prod {α β : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
    [PseudoMetricSpace β] [MeasurableSpace β] (μ : Measure α) (ν : Measure β) [SFinite ν]
    [IsUnifLocDoublingMeasure μ] [IsUnifLocDoublingMeasure ν] :
    IsUnifLocDoublingMeasure (μ.prod ν) := by
  constructor
  use doublingConstant μ * doublingConstant ν
  filter_upwards [exists_measure_closedBall_le_mul' μ, exists_measure_closedBall_le_mul' ν]
    with r hμr hνr x
  rw [← closedBall_prod_same, prod_prod, ← closedBall_prod_same, prod_prod]
  grw [hμr, hνr, ENNReal.coe_mul, mul_mul_mul_comm]

instance IsUnifLocDoublingMeasure.volume_prod {α β : Type*} [PseudoMetricSpace α] [MeasureSpace α]
    [PseudoMetricSpace β] [MeasureSpace β] [SFinite (volume : Measure β)]
    [IsUnifLocDoublingMeasure (volume : Measure α)]
    [IsUnifLocDoublingMeasure (volume : Measure β)] :
    IsUnifLocDoublingMeasure (volume : Measure (α × β)) :=
  .prod _ _

instance IsUnifLocDoublingMeasure.pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, PseudoMetricSpace (α i)] [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] [∀ i, IsUnifLocDoublingMeasure (μ i)] :
    IsUnifLocDoublingMeasure (Measure.pi μ) := by
  use ∏ i, doublingConstant (μ i)
  filter_upwards [Filter.eventually_all.mpr fun i ↦ exists_measure_closedBall_le_mul' (μ i),
    eventually_mem_nhdsWithin] with r hr (hr₀ : 0 < r) x
  simpa (disch := positivity) [Finset.prod_mul_distrib, closedBall_pi, pi_pi]
    using Fintype.prod_mono' fun i ↦ hr i (x i)

instance IsUnifLocDoublingMeasure.volume_pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, PseudoMetricSpace (α i)] [∀ i, MeasureSpace (α i)]
    [∀ i, SigmaFinite (volume : Measure (α i))]
    [∀ i, IsUnifLocDoublingMeasure (volume : Measure (α i))] :
    IsUnifLocDoublingMeasure (volume : Measure (∀ i, α i)) :=
  .pi _

instance IsLocallyFiniteMeasure.prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] :
    IsLocallyFiniteMeasure (μ.prod ν) where
  finiteAtNhds := by
    rintro ⟨x, y⟩
    -- TODO: add FiniteAtFilter _ (_ ×ˢ _)
    rcases finiteAt_nhds μ x with ⟨s, hs, hμs⟩
    rcases finiteAt_nhds ν y with ⟨t, ht, hνt⟩
    use s ×ˢ t, prod_mem_nhds hs ht
    grw [prod_prod_le]
    exact ENNReal.mul_lt_top hμs hνt
