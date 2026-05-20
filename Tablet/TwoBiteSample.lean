import Tablet.Preamble

-- [TABLET NODE: TwoBiteSample]

abbrev TwoBiteSample (n m : ℕ) (_p : ℝ) : Type :=
-- BODY
  SimpleGraph (Fin m) × SimpleGraph (Fin m) × (Fin n ↪ (Fin m × Fin m))
