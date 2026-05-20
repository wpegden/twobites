import Tablet.Preamble

-- [TABLET NODE: TwoBitePairsInSet]

noncomputable def TwoBitePairsInSet {α : Type} [DecidableEq α]
    (rank : α → ℕ) (X : Finset α) : Finset (α × α) := by
-- BODY
  classical
  exact (X.product X).filter (fun e => rank e.1 < rank e.2)
