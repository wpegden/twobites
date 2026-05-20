import Tablet.Preamble

-- [TABLET NODE: WithinRelativeError]

def WithinRelativeError (ε target actual : ℝ) : Prop :=
-- BODY
  |actual - target| ≤ ε * target
