import Tablet.TwoBiteBasePairs
import Tablet.TwoBiteX
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection

-- [TABLET NODE: TwoBiteProjectionPairClosed]

noncomputable def TwoBiteProjectionPairClosed {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (I : Finset (Fin n))
    (e : Sum (Fin m × Fin m) (Fin m × Fin m)) : Prop :=
-- BODY
  match e with
  | Sum.inl q =>
      ∃ x : TwoBiteBaseVertex m,
        q ∈ TwoBiteBasePairs ((TwoBiteX ω I x).image (TwoBiteRedProjection ω))
  | Sum.inr q =>
      ∃ x : TwoBiteBaseVertex m,
        q ∈ TwoBiteBasePairs ((TwoBiteX ω I x).image (TwoBiteBlueProjection ω))
