import Tablet.TwoBiteEmbedding

-- [TABLET NODE: TwoBiteBlueProjection]

def TwoBiteBlueProjection {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
    (v : Fin n) :
    Fin m :=
-- BODY
  (TwoBiteEmbedding ω v).2
