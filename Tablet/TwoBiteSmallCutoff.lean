import Tablet.Preamble

-- [TABLET NODE: TwoBiteSmallCutoff]

noncomputable def TwoBiteSmallCutoff (ε : ℝ) (n : ℕ) : ℝ :=
-- BODY
  Real.rpow (n : ℝ) (2 * ε)
