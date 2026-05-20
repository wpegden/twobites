import Tablet.TwoBiteBaseVertex
import Tablet.TwoBiteX
import Tablet.RealChooseTwo

-- [TABLET NODE: TwoBiteProjectedPairSum]

noncomputable def TwoBiteProjectedPairSum {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (I : Finset (Fin n))
    (cls : TwoBiteBaseVertex m → Prop) (proj : Fin n → Fin m) : ℝ := by
-- BODY
  classical
  exact
    ((Finset.univ : Finset (TwoBiteBaseVertex m)).filter cls).sum
      (fun x => RealChooseTwo (((TwoBiteX ω I x).image proj).card : ℝ))
