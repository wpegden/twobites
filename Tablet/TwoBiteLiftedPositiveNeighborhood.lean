import Tablet.TwoBiteBaseVertex
import Tablet.TwoBiteRedGraph
import Tablet.TwoBiteBlueGraph
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection

-- [TABLET NODE: TwoBiteLiftedPositiveNeighborhood]

noncomputable def TwoBiteLiftedPositiveNeighborhood {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (x : TwoBiteBaseVertex m) :
    Finset (Fin n) := by
-- BODY
  classical
  exact
    Finset.univ.filter
      (fun v =>
        match x with
        | Sum.inl r =>
            r.val < (TwoBiteRedProjection ω v).val ∧
              (TwoBiteRedGraph ω).Adj r (TwoBiteRedProjection ω v)
        | Sum.inr b =>
            b.val < (TwoBiteBlueProjection ω v).val ∧
              (TwoBiteBlueGraph ω).Adj b (TwoBiteBlueProjection ω v))
