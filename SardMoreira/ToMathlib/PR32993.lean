import Mathlib.Data.ENNReal.Basic

open ENNReal

protected theorem ENNReal.div_right_comm {a b c : ℝ≥0∞} : a / b / c = a / c / b := by
  simp only [div_eq_mul_inv, mul_right_comm]
