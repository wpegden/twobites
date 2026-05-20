import Tablet.TwoBiteBaseVertex
import Tablet.TwoBiteRedGraph
import Tablet.TwoBiteBlueGraph

-- [TABLET NODE: TwoBiteBaseAdj]

def TwoBiteBaseAdj {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
    (x y : TwoBiteBaseVertex m) : Prop :=
-- BODY
  match x, y with
  | Sum.inl r, Sum.inl s => (TwoBiteRedGraph ω).Adj r s
  | Sum.inr b, Sum.inr c => (TwoBiteBlueGraph ω).Adj b c
  | _, _ => False
