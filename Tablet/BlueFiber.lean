import Tablet.TwoBiteBlueProjection

-- [TABLET NODE: BlueFiber]

noncomputable def BlueFiber {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
    (b : Fin m) :
    Finset (Fin n) := by
-- BODY
  classical
  exact Finset.univ.filter (fun v => TwoBiteBlueProjection ω v = b)
