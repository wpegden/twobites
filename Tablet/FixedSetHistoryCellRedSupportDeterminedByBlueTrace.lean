import Tablet.Preamble

-- [TABLET NODE: FixedSetHistoryCellRedSupportDeterminedByBlueTrace]

theorem FixedSetHistoryCellRedSupportDeterminedByBlueTrace :
    ∀ {m : ℕ} {BranchLabel RedLabel : Type}
      (terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (blueTrace :
        BranchLabel →
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (redSupport :
        BranchLabel →
          RedLabel →
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
      (∀ β β' : BranchLabel,
        (∀ e,
          e ∈ terminal →
            (match e with
            | Sum.inl _ => False
            | Sum.inr _ => True) →
              (e ∈ blueTrace β ↔ e ∈ blueTrace β')) →
          β = β') →
      ∀ β β' : BranchLabel,
        ∀ J : RedLabel,
          (∀ e,
            e ∈ terminal →
              (match e with
              | Sum.inl _ => False
              | Sum.inr _ => True) →
                (e ∈ blueTrace β ↔ e ∈ blueTrace β')) →
            redSupport β J = redSupport β' J := by
-- BODY
  intro m BranchLabel RedLabel terminal blueTrace redSupport hbranch β β' J hblue
  have hβ : β = β' := hbranch β β' hblue
  subst hβ
  rfl
