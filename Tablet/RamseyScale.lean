import Tablet.Preamble

-- [TABLET NODE: RamseyScale]

noncomputable def RamseyScale (k : ℕ) : ℝ :=
-- BODY
  ((k : ℝ) ^ 2) / Real.log (k : ℝ)
