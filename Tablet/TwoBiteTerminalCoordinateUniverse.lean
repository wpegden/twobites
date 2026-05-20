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

def TwoBiteCoordinateIsRed {m : ℕ}
    (e : Sum (Fin m × Fin m) (Fin m × Fin m)) : Prop :=
  match e with
  | Sum.inl _ => True
  | Sum.inr _ => False

def TwoBiteCoordinateIsBlue {m : ℕ}
    (e : Sum (Fin m × Fin m) (Fin m × Fin m)) : Prop :=
  match e with
  | Sum.inl _ => False
  | Sum.inr _ => True

def TwoBiteTerminalOrderBlueBeforeRed {m : ℕ}
    (terminal : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
    (order : List (Sum (Fin m × Fin m) (Fin m × Fin m))) : Prop :=
  ∀ (pre : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
    (e : Sum (Fin m × Fin m) (Fin m × Fin m))
    (suffix : List (Sum (Fin m × Fin m) (Fin m × Fin m))),
    order = pre ++ e :: suffix →
      TwoBiteCoordinateIsRed e →
        ∀ c,
          c ∈ terminal →
            TwoBiteCoordinateIsBlue c →
              c ∈ pre.toFinset

def TwoBiteTerminalOrderRedBeforeBlue {m : ℕ}
    (terminal : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
    (order : List (Sum (Fin m × Fin m) (Fin m × Fin m))) : Prop :=
  ∀ (pre : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
    (e : Sum (Fin m × Fin m) (Fin m × Fin m))
    (suffix : List (Sum (Fin m × Fin m) (Fin m × Fin m))),
    order = pre ++ e :: suffix →
      TwoBiteCoordinateIsBlue e →
        ∀ c,
          c ∈ terminal →
            TwoBiteCoordinateIsRed c →
              c ∈ pre.toFinset
