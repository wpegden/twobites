import Tablet.TwoBiteProjectionPairSet
import Tablet.TwoBiteProjectionPairClosed

-- [TABLET NODE: TwoBiteUnclosedProjectedPairs]

noncomputable def TwoBiteUnclosedProjectedPairs {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (I : Finset (Fin n)) :
    Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) := by
-- BODY
  classical
  exact
    (TwoBiteProjectionPairSet ω I).filter
      (fun e => ¬ TwoBiteProjectionPairClosed ω I e)
