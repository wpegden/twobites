import Tablet.TwoBiteBaseVertex
import Tablet.TwoBiteRedGraph
import Tablet.TwoBiteBlueGraph
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection

-- [TABLET NODE: TwoBiteLiftedNeighborhood]

noncomputable def TwoBiteLiftedNeighborhood {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (x : TwoBiteBaseVertex m) : Finset (Fin n) := by
-- BODY
  classical
  exact
    Finset.univ.filter
      (fun v =>
        match x with
        | Sum.inl r => (TwoBiteRedGraph ω).Adj r (TwoBiteRedProjection ω v)
        | Sum.inr b => (TwoBiteBlueGraph ω).Adj b (TwoBiteBlueProjection ω v))
