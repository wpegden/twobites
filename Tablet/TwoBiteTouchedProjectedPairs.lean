import Tablet.TwoBiteProjectionPairSet
import Tablet.TwoBiteProjectionPairTouched

-- [TABLET NODE: TwoBiteTouchedProjectedPairs]

noncomputable def TwoBiteTouchedProjectedPairs {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (ε : ℝ) (I : Finset (Fin n)) :
    Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) := by
-- BODY
  classical
  exact
    (TwoBiteProjectionPairSet ω I).filter
      (fun e => TwoBiteProjectionPairTouched ω ε I e)
