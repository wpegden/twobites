import Tablet.FixedSetHistoryCellRISIRevealOrderScanConstruction
import Tablet.FixedSetHistoryCellRISIResidualScanStability
import Tablet.FixedSetHistoryCellRedBranchTranscriptCells
import Tablet.FixedSetHistoryCellRedPrefixScanInvariant

-- [TABLET NODE: FixedSetHistoryCellFixedBJResidualOwnerConstruction]

theorem FixedSetHistoryCellFixedBJResidualOwnerConstruction :
    ∀ {Coord BranchLabel Transcript : Type}
      [DecidableEq Coord] [DecidableEq BranchLabel] [DecidableEq Transcript]
      (terminal : Finset Coord)
      (transcriptLabels : Finset Transcript)
      (present absent selected : Transcript → Finset Coord)
      (fixedSupport : BranchLabel → Transcript → Finset Coord)
      (cellRealized : BranchLabel → Transcript → Prop)
      (residualScan : Finset Coord → Option (BranchLabel × Transcript)),
      (∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              fixedSupport β τ ⊆ present τ →
                (present τ \ fixedSupport β τ) ⊆ A →
                  Disjoint (absent τ \ selected τ) A →
                    residualScan A = some (β, τ)) →
      ∃ residualOwner : Finset Coord → Option (BranchLabel × Transcript),
        ∀ β τ,
          τ ∈ transcriptLabels →
            cellRealized β τ →
              fixedSupport β τ ⊆ present τ →
                terminal.powerset.filter
                    (fun A =>
                      (present τ \ fixedSupport β τ) ⊆ A ∧
                        Disjoint (absent τ \ selected τ) A)
                  ⊆
                terminal.powerset.filter
                    (fun A => residualOwner A = some (β, τ)) := by
-- BODY
  classical
  intro Coord BranchLabel Transcript _ _ _ terminal transcriptLabels present
    absent selected fixedSupport cellRealized residualScan hscan_stable
  let residualOwner : Finset Coord → Option (BranchLabel × Transcript) :=
    residualScan
  refine ⟨residualOwner, ?_⟩
  intro β τ hτ hreal hfixedSupport A hA
  rw [Finset.mem_filter] at hA ⊢
  rcases hA with ⟨hApow, hconstraints⟩
  have hAterminal : A ⊆ terminal := Finset.mem_powerset.mp hApow
  constructor
  · exact hApow
  · dsimp [residualOwner]
    exact
      hscan_stable A β τ hAterminal hτ hreal hfixedSupport
        hconstraints.1 hconstraints.2
