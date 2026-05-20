import Tablet.TwoBiteBaseVertex
import Tablet.TwoBiteFinalPairs
import Tablet.TwoBiteX

-- [TABLET NODE: TwoBiteClosedPairsInClass]

noncomputable def TwoBiteClosedPairsInClass {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (I : Finset (Fin n))
    (cls : TwoBiteBaseVertex m → Prop) : Finset (Fin n × Fin n) := by
-- BODY
  classical
  exact
    ((Finset.univ : Finset (TwoBiteBaseVertex m)).filter cls).biUnion
      (fun x => TwoBiteFinalPairs (TwoBiteX ω I x))
