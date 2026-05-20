import Tablet.TwoBiteLiftedNeighborhood

-- [TABLET NODE: TwoBiteX]

noncomputable def TwoBiteX {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
    (I : Finset (Fin n)) (x : TwoBiteBaseVertex m) : Finset (Fin n) := by
-- BODY
  classical
  exact I.filter (fun v => v ∈ TwoBiteLiftedNeighborhood ω x)
