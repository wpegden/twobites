import Tablet.Preamble

-- [TABLET NODE: RamseyWitness]

noncomputable def RamseyWitness (N k : ℕ) : Prop := by
-- BODY
  classical
  exact ∃ G : SimpleGraph (Fin N),
    G.CliqueFree 3 ∧
      ∀ I : Finset (Fin N), I.card = k → ¬ G.IsIndepSet (↑I : Set (Fin N))
