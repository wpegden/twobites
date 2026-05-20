import Tablet.Preamble

-- [TABLET NODE: GraphDegreeCount]

noncomputable def GraphDegreeCount {α : Type} [Fintype α]
    (G : SimpleGraph α) (v : α) : ℕ := by
-- BODY
  classical
  exact (Finset.univ.filter (fun w => G.Adj v w)).card
