import Tablet.TwoBiteX
import Tablet.TwoBiteLargeCutoff
import Tablet.TwoBiteHugeCutoff

-- [TABLET NODE: TwoBiteLargeClass]

noncomputable def TwoBiteLargeClass {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (ε : ℝ) (I : Finset (Fin n))
    (x : TwoBiteBaseVertex m) : Prop :=
-- BODY
  TwoBiteLargeCutoff ε n < ((TwoBiteX ω I x).card : ℝ) ∧
    ((TwoBiteX ω I x).card : ℝ) ≤ TwoBiteHugeCutoff n
