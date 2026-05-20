import Tablet.Preamble

-- [TABLET NODE: TwoBiteEdgeProbability]

noncomputable def TwoBiteEdgeProbability (β : ℝ) (n : ℕ) : ℝ :=
-- BODY
  β * Real.sqrt (Real.log (n : ℝ) / (n : ℝ))
