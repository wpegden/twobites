import Tablet.TwoBiteStageF1
import Tablet.TwoBiteStageF2

-- [TABLET NODE: TwoBiteStageRevealedVertex]

noncomputable def TwoBiteStageRevealedVertex {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (ε : ℝ) (I : Finset (Fin n))
    (x : TwoBiteBaseVertex m) : Prop :=
-- BODY
  ¬ TwoBiteProjectionContains ω I x ∨
    TwoBiteStageF1 ω I x ∨
      TwoBiteStageF2 ω ε I x
