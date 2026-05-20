import Tablet.TwoBiteBasePairs
import Tablet.TwoBiteXPlus
import Tablet.TwoBiteProjectionPairClosed
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection

-- [TABLET NODE: TwoBiteProjectionPairSameColorClosed]

noncomputable def TwoBiteProjectionPairSameColorClosed {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (I : Finset (Fin n))
    (e : Sum (Fin m × Fin m) (Fin m × Fin m)) : Prop :=
-- BODY
  match e with
  | Sum.inl q =>
      ∃ r : Fin m,
        q ∈
          TwoBiteBasePairs
            ((TwoBiteXPlus ω I (Sum.inl r)).image (TwoBiteRedProjection ω))
  | Sum.inr q =>
      ∃ b : Fin m,
        q ∈
          TwoBiteBasePairs
            ((TwoBiteXPlus ω I (Sum.inr b)).image (TwoBiteBlueProjection ω))
