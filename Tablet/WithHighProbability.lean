import Tablet.Preamble

-- [TABLET NODE: WithHighProbability]

def WithHighProbability (prob : ℕ → ℝ) : Prop :=
-- BODY
  Filter.Tendsto prob Filter.atTop (nhds (1 : ℝ))
