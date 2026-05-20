import Tablet.TwoBiteLiftedPositiveNeighborhood

-- [TABLET NODE: TwoBiteXPlus]

noncomputable def TwoBiteXPlus {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (I : Finset (Fin n))
    (x : TwoBiteBaseVertex m) : Finset (Fin n) := by
-- BODY
  classical
  exact I.filter (fun v => v ∈ TwoBiteLiftedPositiveNeighborhood ω x)
