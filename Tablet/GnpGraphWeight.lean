import Tablet.Preamble

-- [TABLET NODE: GnpGraphWeight]

noncomputable def GnpGraphWeight {m : ℕ} (p : ℝ)
    (G : SimpleGraph (Fin m)) : ℝ := by
-- BODY
  classical
  exact
    ((Finset.univ : Finset (Fin m × Fin m)).filter
      (fun e => e.1.val < e.2.val)).prod
      (fun e => if G.Adj e.1 e.2 then p else 1 - p)
