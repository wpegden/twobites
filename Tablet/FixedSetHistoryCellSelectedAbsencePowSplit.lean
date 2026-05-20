import Tablet.Preamble

-- [TABLET NODE: FixedSetHistoryCellSelectedAbsencePowSplit]

theorem FixedSetHistoryCellSelectedAbsencePowSplit
    {Coord : Type} [DecidableEq Coord]
    (p : ℝ) (absent selected : Finset Coord) :
    selected ⊆ absent →
      ((1 : ℝ) - p) ^ absent.card =
        ((1 : ℝ) - p) ^ (absent.card - selected.card) *
          ((1 : ℝ) - p) ^ selected.card := by
-- BODY
  intro hselected
  have hcard :
      absent.card = absent.card - selected.card + selected.card := by
    exact (Nat.sub_add_cancel (Finset.card_le_card hselected)).symm
  calc
    ((1 : ℝ) - p) ^ absent.card
        =
        ((1 : ℝ) - p) ^ (absent.card - selected.card + selected.card) := by
          exact congrArg (fun k : ℕ => ((1 : ℝ) - p) ^ k) hcard
    _ =
        ((1 : ℝ) - p) ^ (absent.card - selected.card) *
          ((1 : ℝ) - p) ^ selected.card := by
          rw [pow_add]
