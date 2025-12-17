/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib

/-!
A lemma from https://github.com/leanprover-community/mathlib4/pull/32775
-/

open MeasureTheory Measure Metric Filter
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X] {m : MeasurableSpace X}

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
