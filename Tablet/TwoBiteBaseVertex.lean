import Tablet.Preamble

-- [TABLET NODE: TwoBiteBaseVertex]

abbrev TwoBiteBaseVertex (m : ℕ) : Type :=
-- BODY
  Sum (Fin m) (Fin m)
