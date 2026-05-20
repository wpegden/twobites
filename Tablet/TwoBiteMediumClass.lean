import Tablet.TwoBiteX
import Tablet.TwoBiteSmallCutoff
import Tablet.TwoBiteLargeCutoff

-- [TABLET NODE: TwoBiteMediumClass]

noncomputable def TwoBiteMediumClass {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (ε : ℝ) (I : Finset (Fin n))
    (x : TwoBiteBaseVertex m) : Prop :=
-- BODY
  TwoBiteSmallCutoff ε n < ((TwoBiteX ω I x).card : ℝ) ∧
    ((TwoBiteX ω I x).card : ℝ) ≤ TwoBiteLargeCutoff ε n
