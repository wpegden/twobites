import Tablet.Preamble

-- [TABLET NODE: TwoBiteLargeCutoff]

noncomputable def TwoBiteLargeCutoff (ε : ℝ) (n : ℕ) : ℝ :=
-- BODY
  Real.rpow (n : ℝ) ((1 / 4 : ℝ) + ε)
