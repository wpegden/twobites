import Tablet.TwoBiteEmbedding

-- [TABLET NODE: TwoBiteRedProjection]

def TwoBiteRedProjection {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
    (v : Fin n) :
    Fin m :=
-- BODY
  (TwoBiteEmbedding ω v).1
