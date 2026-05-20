import Tablet.TwoBiteReducedVertexCount

-- [TABLET NODE: TwoBiteNaturalReducedVertexCount]

noncomputable def TwoBiteNaturalReducedVertexCount (n : ℕ) : ℕ :=
-- BODY
  Nat.floor (TwoBiteReducedVertexCount n)
