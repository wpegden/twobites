import Tablet.TwoBitePairsInSet

-- [TABLET NODE: TwoBiteBasePairs]

noncomputable def TwoBiteBasePairs {m : ℕ}
    (X : Finset (Fin m)) : Finset (Fin m × Fin m) :=
-- BODY
  TwoBitePairsInSet (fun v : Fin m => v.val) X
