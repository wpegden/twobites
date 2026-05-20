import Tablet.TwoBiteProjectionContains
import Tablet.TwoBiteBaseFiber

-- [TABLET NODE: TwoBiteStageF1]

noncomputable def TwoBiteStageF1 {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (I : Finset (Fin n))
    (x : TwoBiteBaseVertex m) : Prop :=
-- BODY
  TwoBiteProjectionContains ω I x ∧
    Real.log (n : ℝ) < ((TwoBiteBaseFiber ω x ∩ I).card : ℝ)
