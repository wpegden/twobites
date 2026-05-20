import Tablet.ClosedPairsBound
import Tablet.TwoBiteClosedPairsInClass
import Tablet.TwoBiteMediumClass

-- [TABLET NODE: TwoBiteMediumClosedPairsEvent]

noncomputable def TwoBiteMediumClosedPairsEvent {n m k : ℕ} {p : ℝ}
    (ε ε1 : ℝ) (ω : TwoBiteSample n m p) : Prop :=
-- BODY
  ∀ I : Finset (Fin n), I.card = k →
    ClosedPairsBound
      ((TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I)).card : ℝ)
      ε1 (k : ℝ)
