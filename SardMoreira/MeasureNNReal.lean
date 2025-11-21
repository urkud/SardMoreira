import SardMoreira.MeasureComap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open scoped ENNReal NNReal Set.Notation Pointwise
open MeasureTheory Filter Set Function Metric Topology

noncomputable instance : MeasureSpace ℝ≥0 where
  volume := .comap (↑) (volume : Measure ℝ)

theorem NNReal.volume_def : (volume : Measure ℝ≥0) = .comap (↑) (volume : Measure ℝ) := rfl

-- TODO: should we have this instance? I'm not sure.
instance : SigmaFinite (volume : Measure ℝ≥0) := .comap _ (by fun_prop)
