import Tablet.TwoBiteStageF1
import Tablet.TwoBiteBaseAdj
import Tablet.TwoBiteLargeCutoff

-- [TABLET NODE: TwoBiteStageF2]

noncomputable def TwoBiteStageF2 {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (ε : ℝ) (I : Finset (Fin n))
    (x : TwoBiteBaseVertex m) : Prop := by
-- BODY
  classical
  exact
    TwoBiteProjectionContains ω I x ∧
      TwoBiteLargeCutoff ε n / Real.log (n : ℝ) <
        (((Finset.univ : Finset (TwoBiteBaseVertex m)).filter
          (fun y => TwoBiteStageF1 ω I y ∧ TwoBiteBaseAdj ω x y)).card : ℝ)
