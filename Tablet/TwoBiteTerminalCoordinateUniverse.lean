import Tablet.Preamble

-- [TABLET NODE: TwoBiteTerminalCoordinateUniverse]

noncomputable def TwoBiteTerminalCoordinateUniverse (m : ℕ) :
    Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) := by
-- BODY
  classical
  exact
    (((Finset.univ : Finset (Fin m × Fin m)).filter
        (fun q => q.1.val < q.2.val)).image Sum.inl) ∪
      (((Finset.univ : Finset (Fin m × Fin m)).filter
        (fun q => q.1.val < q.2.val)).image Sum.inr)
