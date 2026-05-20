import Tablet.FiberAndDegreeEvent
import Tablet.TwoBiteMediumClosedPairsEvent
import Tablet.TwoBiteSmallClosedPairsEvent

-- [TABLET NODE: TwoBiteRegularityEvent]

noncomputable def TwoBiteRegularityEvent {n m k : ℕ} {p : ℝ}
    (ε ε1 ε2 : ℝ) (ω : TwoBiteSample n m p) : Prop :=
-- BODY
  FiberAndDegreeEvent ω ε2 ∧
    TwoBiteMediumClosedPairsEvent (k := k) ε ε1 ω ∧
      TwoBiteSmallClosedPairsEvent (k := k) ε ε1 ω
