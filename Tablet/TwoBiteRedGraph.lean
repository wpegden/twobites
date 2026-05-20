import Tablet.TwoBiteSample

-- [TABLET NODE: TwoBiteRedGraph]

def TwoBiteRedGraph {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p) :
    SimpleGraph (Fin m) :=
-- BODY
  ω.1
