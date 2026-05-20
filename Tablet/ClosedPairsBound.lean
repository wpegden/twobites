import Tablet.Preamble

-- [TABLET NODE: ClosedPairsBound]

def ClosedPairsBound (closedPairs : ℝ) (ε1 k : ℝ) : Prop :=
-- BODY
  closedPairs ≤ ε1 * k ^ 2
