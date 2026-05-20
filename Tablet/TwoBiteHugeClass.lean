import Tablet.TwoBiteX
import Tablet.TwoBiteHugeCutoff

-- [TABLET NODE: TwoBiteHugeClass]

noncomputable def TwoBiteHugeClass {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (I : Finset (Fin n))
    (x : TwoBiteBaseVertex m) : Prop :=
-- BODY
  TwoBiteHugeCutoff n < ((TwoBiteX ω I x).card : ℝ) ∧
    ((TwoBiteX ω I x).card : ℝ) ≤ (I.card : ℝ)
