import Tablet.TwoBiteLargeClass
import Tablet.TwoBiteHugeClass

-- [TABLET NODE: TwoBiteLargeHugeVertices]

noncomputable def TwoBiteLargeHugeVertices {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (ε : ℝ) (I : Finset (Fin n)) :
    Finset (TwoBiteBaseVertex m) := by
-- BODY
  classical
  exact
    (Finset.univ : Finset (TwoBiteBaseVertex m)).filter
      (fun x => TwoBiteLargeClass ω ε I x ∨ TwoBiteHugeClass ω I x)
