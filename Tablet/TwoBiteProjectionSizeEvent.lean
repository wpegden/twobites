import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection

-- [TABLET NODE: TwoBiteProjectionSizeEvent]

def TwoBiteProjectionSizeEvent {n m k ℓR ℓB : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (I : Finset (Fin n)) : Prop :=
-- BODY
  I.card = k ∧
    (I.image (TwoBiteRedProjection ω)).card = ℓR ∧
      (I.image (TwoBiteBlueProjection ω)).card = ℓB
