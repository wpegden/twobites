import Tablet.Preamble

-- [TABLET NODE: TwoBiteHugeCutoff]

noncomputable def TwoBiteHugeCutoff (n : ℕ) : ℝ :=
-- BODY
  Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / Real.log (Real.log (n : ℝ))
