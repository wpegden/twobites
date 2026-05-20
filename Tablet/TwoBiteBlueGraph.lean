import Tablet.TwoBiteSample

-- [TABLET NODE: TwoBiteBlueGraph]

def TwoBiteBlueGraph {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p) :
    SimpleGraph (Fin m) :=
-- BODY
  ω.2.1
