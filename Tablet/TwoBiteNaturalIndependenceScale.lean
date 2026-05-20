import Tablet.TwoBiteIndependenceScale

-- [TABLET NODE: TwoBiteNaturalIndependenceScale]

noncomputable def TwoBiteNaturalIndependenceScale (κ : ℝ) (n : ℕ) : ℕ :=
-- BODY
  Nat.ceil (TwoBiteIndependenceScale κ n)
