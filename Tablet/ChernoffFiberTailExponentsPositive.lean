import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Tablet.Preamble

-- [TABLET NODE: ChernoffFiberTailExponentsPositive]

theorem ChernoffFiberTailExponentsPositive (δ : ℝ)
    (hδ : 0 < δ) (hδle : δ ≤ (1 / 2 : ℝ)) :
    0 < (1 + δ) * Real.log (1 + δ) - δ ∧
    0 < δ + (1 - δ) * Real.log (1 - δ) := by
-- BODY
  have hδlt1 : δ < 1 := by linarith
  have hone_add_pos : 0 < 1 + δ := by linarith
  constructor
  · have hlog : 2 * δ / (δ + 2) < Real.log (1 + δ) := by
      simpa [add_comm, add_left_comm, add_assoc] using Real.lt_log_one_add_of_pos hδ
    have hden_pos : 0 < δ + 2 := by linarith
    have hbase : δ < (1 + δ) * (2 * δ / (δ + 2)) := by
      field_simp [hden_pos.ne']
      nlinarith [sq_pos_of_ne_zero hδ.ne']
    have hmul : (1 + δ) * (2 * δ / (δ + 2)) < (1 + δ) * Real.log (1 + δ) := by
      exact mul_lt_mul_of_pos_left hlog hone_add_pos
    linarith
  · have hpos : 0 < 1 - δ := by linarith
    have hinv_ne_one : (1 - δ)⁻¹ ≠ 1 := by
      intro h
      have hmul := congrArg (fun t : ℝ => t * (1 - δ)) h
      field_simp [hpos.ne'] at hmul
      linarith
    have hlog_inv :
        Real.log ((1 - δ)⁻¹) < (1 - δ)⁻¹ - 1 :=
      Real.log_lt_sub_one_of_pos (inv_pos.mpr hpos) hinv_ne_one
    have hneglog :
        -Real.log (1 - δ) < (1 - δ)⁻¹ - 1 := by
      simpa [Real.log_inv] using hlog_inv
    have hmul := mul_lt_mul_of_pos_left hneglog hpos
    have hright : (1 - δ) * ((1 - δ)⁻¹ - 1) = δ := by
      field_simp [hpos.ne']
      ring
    have hleft : (1 - δ) * (-Real.log (1 - δ)) =
        -((1 - δ) * Real.log (1 - δ)) := by ring
    have hbound : -((1 - δ) * Real.log (1 - δ)) < δ := by
      simpa [hleft, hright] using hmul
    linarith
