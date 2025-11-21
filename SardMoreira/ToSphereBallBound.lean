import Mathlib.MeasureTheory.Constructions.HaarToSphere

open MeasureTheory MeasureTheory.Measure Metric Set
open scoped Pointwise NNReal ENNReal

@[simp]
theorem Subtype.preimage_ball {X : Type*} [PseudoMetricSpace X] {p : X → Prop}
    (x : {x // p x}) (r : ℝ) : Subtype.val ⁻¹' (ball x.1 r) = ball x r :=
  rfl

@[simp]
theorem Subtype.image_ball {X : Type*} [PseudoMetricSpace X] {p : X → Prop}
    (x : {x // p x}) (r : ℝ) : Subtype.val '' (ball x r) = ball x.1 r ∩ {x | p x} := by
  ext; simp [Subtype.dist_eq]

private lemma ball_subset_sector_of_small_epsilon
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (hx : ‖x‖ = 1) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 2) :
    ball ((1 - ε / 4) • x) (ε / 4) ⊆
      Ioo (0 : ℝ) 1 • (ball x ε ∩ sphere (0 : E) 1) := by
  intro y hy
  rw [mem_ball] at hy
  have habs : |1 - ε / 4| = 1 - ε / 4 := abs_of_nonneg (by linarith)
  -- Note that $y ≠ 0$.
  have hy₀ : y ≠ 0 := by
    rintro rfl
    have : 1 - ε / 4 < ε / 4 := by simpa [norm_smul, habs, hx] using hy
    linarith
  have hy₁ : ‖y‖ < 1 := calc
    ‖y‖ ≤ dist y ((1 - ε / 4) • x) + ‖(1 - ε / 4) • x‖ := by
      simpa using dist_triangle y ((1 - ε / 4) • x) 0
    _ < ε / 4 + ‖(1 - ε / 4) • x‖ := by gcongr
    _ = 1 := by simp [norm_smul, habs, hx]
  -- Let $u = y / \|y\|$. We show $\|u - x\| < \epsilon$.
  set u : E := ‖y‖⁻¹ • y
  have hu₁ : ‖u‖ = 1 := by simp [u, hy₀, norm_smul]
  refine  ⟨‖y‖, ⟨by simpa, hy₁⟩, u, ⟨?_, by simpa⟩, by simp [u, hy₀]⟩
  rw [mem_ball]
  have hyx := calc
    dist y x ≤ dist y ((1 - ε / 4) • x) + dist ((1 - ε / 4) • x) x := dist_triangle ..
    _ < ε / 4 + dist ((1 - ε / 4) • x) x := by gcongr
    _ = ε / 4 + ε / 4 := by simp [sub_smul, norm_smul, hx, abs_of_pos hε]
    _ = ε / 2 := by ring
  have huy : dist u y ≤ dist x y := by
    have H : u - y = (1 - ‖y‖) • u := by simp [u, hy₀, sub_smul]
    simpa [dist_eq_norm_sub, H, norm_smul, abs_of_nonneg, hy₁.le, hu₁, hx]
      using dist_triangle x y 0
  linarith [dist_triangle u y x, dist_comm x y]

namespace MeasureTheory.Measure

/-- Lower estimate on the measure of the `ε`-cone in an `n`-dimensional normed space
divided by the measure of the ball. -/
@[irreducible]
noncomputable def toSphereBallBound (n : ℕ) (ε : ℝ) : ℝ≥0 :=
  if n ≠ 0 ∧ 0 < ε then n * ((min (Real.toNNReal ε) 2) / 4) ^ n else 1

theorem toSphereBallBound_pos (n : ℕ) (ε : ℝ) : 0 < toSphereBallBound n ε := by
  unfold toSphereBallBound
  split_ifs with h
  · cases h
    -- TODO: add a `positivity` extension for `Real.toNNReal`.
    have : 0 < ε.toNNReal := by simpa
    positivity
  · positivity

/-- A ball of radius `ε` on the unit sphere in a real normed space
has measure at least `toSphereBallBound n ε * μ (ball 0 1)`,
where `n` is the dimension of the space,
`toSphereBallBound n ε` is a lower estimate that depends only on the dimension and `ε`,
which is positive for positive `n` and `ε`. -/
theorem toSphereBallBound_mul_measure_unitBall_le_toSphere_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]
    {ε : ℝ} (hε : 0 < ε) (x : sphere (0 : E) 1) :
    toSphereBallBound (Module.finrank ℝ E) ε * μ (ball 0 1) ≤ μ.toSphere (ball x ε) := by
  have : Nontrivial E := ⟨⟨x, 0, ne_of_apply_ne Norm.norm (by simp)⟩⟩
  wlog hε₂ : ε ≤ 2 generalizing ε
  · trans μ.toSphere (ball x (min ε 2))
    · simpa [Real.toNNReal_monotone.map_min, toSphereBallBound]
        using this (ε := min ε 2) (by simp [hε]) (by simp)
    · gcongr
      simp
  rw [μ.toSphere_apply' measurableSet_ball, Subtype.image_ball, setOf_mem_eq]
  grw [← ball_subset_sector_of_small_epsilon] <;> try assumption
  · have hdim : Module.finrank ℝ E ≠ 0 := Module.finrank_pos.ne'
    have : min (ENNReal.ofReal ε) 2 = ENNReal.ofReal ε := by simpa
    simp (disch := positivity) [μ.addHaar_ball_of_pos (r := ε / 4), ENNReal.ofReal_div_of_pos,
      toSphereBallBound, mul_assoc, ENNReal.ofNNReal_toNNReal, this, hdim, hε]
  · simp

/-- A ball of radius `ε` on the unit sphere in a real normed space
has measure at least `toSphereBallBound n ε * μ (ball 0 1)`,
where `n` is the dimension of the space,
`toSphereBallBound n ε` is a lower estimate that depends only on the dimension and `ε`,
which is positive for positive `n` and `ε`.

This is a version stated in terms `MeasureTheory.Measure.real`. -/
theorem toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]
    {ε : ℝ} (hε : 0 < ε) (x : sphere (0 : E) 1) :
    toSphereBallBound (Module.finrank ℝ E) ε * μ.real (ball 0 1) ≤
      μ.toSphere.real (ball x ε) := by
  grw [Measure.real, Measure.real, ← toSphereBallBound_mul_measure_unitBall_le_toSphere_ball μ hε,
    ENNReal.toReal_mul, ENNReal.coe_toReal]
  simp

end MeasureTheory.Measure
