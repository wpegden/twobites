import Tablet.TwoBiteRedGraph
import Tablet.TwoBiteBlueGraph

-- [TABLET NODE: TwoBiteEdgeCoordinateValue]

def TwoBiteEdgeCoordinateValue {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p)
    (e : Sum (Fin m × Fin m) (Fin m × Fin m)) : Prop :=
-- BODY
  match e with
  | Sum.inl q => (TwoBiteRedGraph ω).Adj q.1 q.2
  | Sum.inr q => (TwoBiteBlueGraph ω).Adj q.1 q.2
