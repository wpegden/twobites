import Tablet.TwoBiteProjectionPairSet
import Tablet.TwoBiteProjectionPairSameColorClosed
import Tablet.TwoBiteProjectionPairTouched
import Tablet.TwoBitePreTerminalRecordedPairs

-- [TABLET NODE: TwoBiteStagedOpenPairs]

noncomputable def TwoBiteStagedOpenPairs {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (ε : ℝ) (I : Finset (Fin n)) :
    Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) := by
-- BODY
  classical
  exact
    (TwoBiteProjectionPairSet ω I).filter
      (fun e =>
        ¬ TwoBiteProjectionPairSameColorClosed ω I e ∧
          ¬ TwoBiteProjectionPairTouched ω ε I e ∧
            e ∉ TwoBitePreTerminalRecordedPairs ω ε I)
