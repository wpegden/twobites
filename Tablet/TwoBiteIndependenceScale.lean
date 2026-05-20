import Tablet.Preamble

-- [TABLET NODE: TwoBiteIndependenceScale]

noncomputable def TwoBiteIndependenceScale (κ : ℝ) (n : ℕ) : ℝ :=
-- BODY
  κ * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
