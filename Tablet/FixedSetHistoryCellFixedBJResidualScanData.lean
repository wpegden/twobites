import Tablet.FixedSetHistoryCellFixedBJResidualScanInterface

-- [TABLET NODE: FixedSetHistoryCellFixedBJResidualScanData]

theorem FixedSetHistoryCellFixedBJResidualScanData :
    ∀ {Coord BranchLabel Transcript : Type}
      [DecidableEq Coord] [DecidableEq BranchLabel] [DecidableEq Transcript]
      (terminal : Finset Coord)
      (order : List Coord)
      (transcriptLabels : Finset Transcript)
      (present absent selected : Transcript → Finset Coord)
      (fixedSupport : BranchLabel → Transcript → Finset Coord)
      (cellRealized : BranchLabel → Transcript → Prop)
      (assignmentCompatible : Finset Coord → BranchLabel → Transcript → Prop),
      order.Nodup →
      order.toFinset = terminal →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized β τ →
            fixedSupport β τ ⊆ present τ ∧
            present τ ⊆ terminal ∧
            absent τ ⊆ terminal ∧
            Disjoint (present τ) (absent τ) ∧
            selected τ ⊆ absent τ) →
      (∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              assignmentCompatible A β τ →
                present τ ⊆ A ∧
                Disjoint (absent τ \ selected τ) A) →
      (∀ A β β' τ τ',
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            τ' ∈ transcriptLabels →
              cellRealized β τ →
                cellRealized β' τ' →
                  assignmentCompatible A β τ →
                    assignmentCompatible A β' τ' →
                      β = β' ∧ τ = τ') →
      (∃ residualScan : Finset Coord → Option (BranchLabel × Transcript),
        ∃ reconstructedScan :
          Finset Coord → Option (BranchLabel × Transcript),
          (∀ A β τ,
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized β τ →
                  reconstructedScan A = some (β, τ) →
                    assignmentCompatible A β τ) ∧
          (∀ A β τ,
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized β τ →
                  assignmentCompatible A β τ →
                    reconstructedScan A = some (β, τ)) ∧
          (∀ A β τ,
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized β τ →
                  fixedSupport β τ ⊆ present τ →
                    (present τ \ fixedSupport β τ) ⊆ A →
                      Disjoint (absent τ \ selected τ) A →
                        residualScan A =
                          reconstructedScan
                            ((A \ selected τ) ∪ fixedSupport β τ)) ∧
          (∀ A β τ,
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized β τ →
                  fixedSupport β τ ⊆ present τ →
                    (present τ \ fixedSupport β τ) ⊆ A →
                      Disjoint (absent τ \ selected τ) A →
                        reconstructedScan
                            ((A \ selected τ) ∪ fixedSupport β τ) =
                          some (β, τ)) ∧
          (∀ A β τ,
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized β τ →
                  residualScan A = some (β, τ) →
                    assignmentCompatible
                      ((A \ selected τ) ∪ fixedSupport β τ) β τ) ∧
          (∀ A β τ,
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized β τ →
                  assignmentCompatible
                    ((A \ selected τ) ∪ fixedSupport β τ) β τ →
                    residualScan A = some (β, τ)) ∧
          ∀ A β β' τ τ',
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                τ' ∈ transcriptLabels →
                  cellRealized β τ →
                    cellRealized β' τ' →
                      residualScan A = some (β, τ) →
                        residualScan A = some (β', τ') →
                          β = β' ∧ τ = τ') →
      (∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              (present τ \ fixedSupport β τ) ⊆ A →
                Disjoint (absent τ \ selected τ) A →
                  assignmentCompatible
                    ((A \ selected τ) ∪ fixedSupport β τ) β τ) ∧
      ∀ A β β' τ τ',
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            τ' ∈ transcriptLabels →
              cellRealized β τ →
                cellRealized β' τ' →
                  assignmentCompatible
                    ((A \ selected τ) ∪ fixedSupport β τ) β τ →
                  assignmentCompatible
                    ((A \ selected τ') ∪ fixedSupport β' τ') β' τ' →
                    β = β' ∧ τ = τ' := by
-- BODY
  classical
  intro Coord BranchLabel Transcript _ _ _ terminal order transcriptLabels
    present absent selected fixedSupport cellRealized assignmentCompatible
    _horder_nodup _horder_terminal hrealized_geometry _hcompat_forward
    _hcompat_inj hinterface
  rcases hinterface with
    ⟨residualScan, reconstructedScan, _hreconstructed_to_scan,
      _hscan_to_reconstructed, hdelete_reinsert,
      hreconstructed_stable, hscan_to_compat, hcompat_to_scan,
      hscan_functional⟩
  have hscan_cylinder :
      ∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              fixedSupport β τ ⊆ present τ →
                (present τ \ fixedSupport β τ) ⊆ A →
                  Disjoint (absent τ \ selected τ) A →
                    residualScan A = some (β, τ) :=
    by
      intro A β τ hA hτ hreal hfixed hpresent_res habsent_res
      calc
        residualScan A =
            reconstructedScan ((A \ selected τ) ∪ fixedSupport β τ) :=
          hdelete_reinsert A β τ hA hτ hreal hfixed hpresent_res
            habsent_res
        _ = some (β, τ) :=
          hreconstructed_stable A β τ hA hτ hreal hfixed hpresent_res
            habsent_res
  refine ⟨?_, ?_⟩
  · intro A β τ hA hτ hreal hpresent_res habsent_res
    have hfixed : fixedSupport β τ ⊆ present τ :=
      (hrealized_geometry β τ hτ hreal).1
    exact
      hscan_to_compat A β τ hA hτ hreal
        (hscan_cylinder A β τ hA hτ hreal hfixed hpresent_res
          habsent_res)
  · intro A β β' τ τ' hA hτ hτ' hreal hreal' hcompat hcompat'
    exact
      hscan_functional A β β' τ τ' hA hτ hτ' hreal hreal'
        (hcompat_to_scan A β τ hA hτ hreal hcompat)
        (hcompat_to_scan A β' τ' hA hτ' hreal' hcompat')
