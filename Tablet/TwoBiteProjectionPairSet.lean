import Tablet.TwoBiteBasePairs
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection

-- [TABLET NODE: TwoBiteProjectionPairSet]

noncomputable def TwoBiteProjectionPairSet {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (I : Finset (Fin n)) :
    Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) := by
-- BODY
  classical
  exact
    ((TwoBiteBasePairs (I.image (TwoBiteRedProjection ω))).image Sum.inl) ∪
      ((TwoBiteBasePairs (I.image (TwoBiteBlueProjection ω))).image Sum.inr)
