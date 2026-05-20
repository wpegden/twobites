import Tablet.Preamble
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

-- [TABLET NODE: MajorizationTwoCoordinateAbsRearrangement]

theorem MajorizationTwoCoordinateAbsRearrangement {a d α β : ℝ} (had : a ≤ d) (hba : β ≤ α) :
    |d - α| + |a - β| ≤ |a - α| + |d - β| := by
-- BODY
  rcases le_total d α with hd1 | hd1 <;> rcases le_total a α with ha1 | ha1 <;>
  rcases le_total d β with hd2 | hd2 <;> rcases le_total a β with ha2 | ha2 <;>
  (try rw [abs_of_nonneg (by linarith)]) <;>
  (try rw [abs_of_nonpos (by linarith)]) <;>
  (try rw [abs_of_nonneg (by linarith)]) <;>
  (try rw [abs_of_nonpos (by linarith)]) <;>
  (try rw [abs_of_nonneg (by linarith)]) <;>
  (try rw [abs_of_nonpos (by linarith)]) <;>
  (try rw [abs_of_nonneg (by linarith)]) <;>
  (try rw [abs_of_nonpos (by linarith)]) <;>
  linarith
