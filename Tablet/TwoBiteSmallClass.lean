import Tablet.TwoBiteX
import Tablet.TwoBiteSmallCutoff

-- [TABLET NODE: TwoBiteSmallClass]

noncomputable def TwoBiteSmallClass {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (ε : ℝ) (I : Finset (Fin n))
    (x : TwoBiteBaseVertex m) : Prop :=
-- BODY
  0 ≤ ((TwoBiteX ω I x).card : ℝ) ∧
    ((TwoBiteX ω I x).card : ℝ) ≤ TwoBiteSmallCutoff ε n
