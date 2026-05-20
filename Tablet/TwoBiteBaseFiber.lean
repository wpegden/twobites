import Tablet.TwoBiteBaseVertex
import Tablet.RedFiber
import Tablet.BlueFiber

-- [TABLET NODE: TwoBiteBaseFiber]

noncomputable def TwoBiteBaseFiber {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (x : TwoBiteBaseVertex m) : Finset (Fin n) :=
-- BODY
  match x with
  | Sum.inl r => RedFiber ω r
  | Sum.inr b => BlueFiber ω b
