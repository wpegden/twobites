import Tablet.FixedSetHistoryCellRISIRevealOrderScanConstruction
import Tablet.FixedSetHistoryCellRISIResidualScanStability

-- [TABLET NODE: FixedSetHistoryCellFixedBJResidualSingleScanStability]

theorem FixedSetHistoryCellFixedBJResidualSingleScanStability :
    ∀ {Coord BranchLabel Transcript : Type}
      [DecidableEq Coord] [DecidableEq BranchLabel] [DecidableEq Transcript]
      (terminal : Finset Coord)
      (transcriptLabels : Finset Transcript)
      (present absent selected : Transcript → Finset Coord)
      (fixedSupport : BranchLabel → Transcript → Finset Coord)
      (cellRealized : BranchLabel → Transcript → Prop)
      (residualScan reconstructedScan :
        Finset Coord → Option (BranchLabel × Transcript)),
      (∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              fixedSupport β τ ⊆ present τ →
                (present τ \ fixedSupport β τ) ⊆ A →
                  Disjoint (absent τ \ selected τ) A →
                    residualScan A =
                      reconstructedScan ((A \ selected τ) ∪ fixedSupport β τ)) →
      (∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              fixedSupport β τ ⊆ present τ →
                (present τ \ fixedSupport β τ) ⊆ A →
                  Disjoint (absent τ \ selected τ) A →
                    reconstructedScan ((A \ selected τ) ∪ fixedSupport β τ) =
                      some (β, τ)) →
      ∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              fixedSupport β τ ⊆ present τ →
                (present τ \ fixedSupport β τ) ⊆ A →
                  Disjoint (absent τ \ selected τ) A →
                    residualScan A = some (β, τ) := by
-- BODY
  classical
  intro Coord BranchLabel Transcript _ _ _ terminal transcriptLabels present
    absent selected fixedSupport cellRealized residualScan reconstructedScan
    hresidualScan_def hreconstructed_stable A β τ hAterminal hτ hreal
    hfixedSupport hpresent_res habsent_res
  calc
    residualScan A =
        reconstructedScan ((A \ selected τ) ∪ fixedSupport β τ) :=
      hresidualScan_def A β τ hAterminal hτ hreal hfixedSupport
        hpresent_res habsent_res
    _ = some (β, τ) :=
      hreconstructed_stable A β τ hAterminal hτ hreal hfixedSupport
        hpresent_res habsent_res
