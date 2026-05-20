import Tablet.TwoBitePairsInSet

-- [TABLET NODE: TwoBiteFinalPairs]

noncomputable def TwoBiteFinalPairs {n : ℕ}
    (X : Finset (Fin n)) : Finset (Fin n × Fin n) :=
-- BODY
  TwoBitePairsInSet (fun v : Fin n => v.val) X
