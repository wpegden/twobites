import Tablet.TwoBiteProjectionPairSet
import Tablet.TwoBiteBasePairs
import Tablet.TwoBiteBaseVertex
import Tablet.TwoBiteX
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection

-- [TABLET NODE: TwoBiteProjectedPairsClosedInClass]

noncomputable def TwoBiteProjectedPairsClosedInClass {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (I : Finset (Fin n))
    (cls : TwoBiteBaseVertex m → Prop) :
    Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) := by
-- BODY
  classical
  exact
    (TwoBiteProjectionPairSet ω I).filter (fun e =>
      match e with
      | Sum.inl q =>
          ∃ x : TwoBiteBaseVertex m,
            cls x ∧
              q ∈ TwoBiteBasePairs
                ((TwoBiteX ω I x).image (TwoBiteRedProjection ω))
      | Sum.inr q =>
          ∃ x : TwoBiteBaseVertex m,
            cls x ∧
              q ∈ TwoBiteBasePairs
                ((TwoBiteX ω I x).image (TwoBiteBlueProjection ω)))
