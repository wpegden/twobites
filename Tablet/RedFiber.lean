import Tablet.TwoBiteRedProjection

-- [TABLET NODE: RedFiber]

noncomputable def RedFiber {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
    (r : Fin m) :
    Finset (Fin n) := by
-- BODY
  classical
  exact Finset.univ.filter (fun v => TwoBiteRedProjection ω v = r)
