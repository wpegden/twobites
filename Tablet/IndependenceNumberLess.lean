import Tablet.Preamble

-- [TABLET NODE: IndependenceNumberLess]

noncomputable def IndependenceNumberLess {α : Type} [Fintype α]
    (G : SimpleGraph α) (x : ℝ) : Prop := by
-- BODY
  classical
  exact ∀ I : Finset α, G.IsIndepSet (↑I : Set α) → (I.card : ℝ) < x
