import Tablet.TwoBiteSample

-- [TABLET NODE: TwoBiteEmbedding]

def TwoBiteEmbedding {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p) :
    Fin n ↪ (Fin m × Fin m) :=
-- BODY
  ω.2.2
