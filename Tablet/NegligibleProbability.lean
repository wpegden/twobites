import Tablet.Preamble

-- [TABLET NODE: NegligibleProbability]

def NegligibleProbability (prob : ℕ → ℝ) : Prop :=
-- BODY
  Filter.Tendsto prob Filter.atTop (nhds (0 : ℝ))
