import Tablet.FixedSetHistoryCellCanonicalAbsenceSelection
import Tablet.FixedSetHistoryCellTerminalAssignmentExtension

open Classical

-- [TABLET NODE: FixedSetHistoryCellRISIRevealOrderScanConstruction]

theorem FixedSetHistoryCellRISIRevealOrderScanConstruction :
    ∀ {Coord BranchLabel Transcript : Type} [DecidableEq Coord]
      (terminal : Finset Coord)
      (order : List Coord)
      (present absent selected fixedSupport : Transcript → Finset Coord)
      (dependencySet : Transcript → Coord → Finset Coord)
      (stagedOpen touched sameColorClosed preTerminalRecorded :
        Finset Coord → Coord → Prop)
      (branchOfAssignment : Finset Coord → BranchLabel)
      (scanTranscript : Finset Coord → Option Transcript)
      (witness : Finset Coord)
      (β : BranchLabel) (τ : Transcript)
      (_risiReadClassified :
        ∀ e,
          e ∈ terminal →
            ∀ c,
              c ∈ dependencySet τ e →
                c ∈ fixedSupport τ ∨
                  c ∈ present τ \ fixedSupport τ ∨
                    c ∈ selected τ ∨
                      c ∈ absent τ \ selected τ)
      (_risiDependenciesPast :
        ∀ (pre suffix : List Coord) (e : Coord),
          order = pre ++ e :: suffix →
            dependencySet τ e ⊆ pre.toFinset)
      (_risiExactReadStability :
        ∀ A,
          A ⊆ terminal →
            ∀ e,
              e ∈ terminal →
                (∀ c,
                  c ∈ dependencySet τ e →
                    (c ∈ witness ↔ c ∈ A)) →
              (stagedOpen witness e ↔ stagedOpen A e) ∧
              (touched witness e ↔ touched A e) ∧
              (sameColorClosed witness e ↔ sameColorClosed A e) ∧
              (preTerminalRecorded witness e ↔ preTerminalRecorded A e))
      (_risiDeterministicOutput :
        ∀ A,
          A ⊆ terminal →
          (∀ e,
            e ∈ terminal →
              (stagedOpen witness e ↔ stagedOpen A e) ∧
              (touched witness e ↔ touched A e) ∧
              (sameColorClosed witness e ↔ sameColorClosed A e) ∧
              (preTerminalRecorded witness e ↔ preTerminalRecorded A e)) →
            branchOfAssignment A = β ∧ scanTranscript A = some τ),
      order.Nodup →
      order.toFinset = terminal →
      present τ ⊆ terminal →
      absent τ ⊆ terminal →
      fixedSupport τ ⊆ present τ →
      selected τ ⊆ absent τ →
      Disjoint (present τ) (absent τ) →
      (∀ e, e ∈ present τ → e ∈ witness) →
      (∀ e, e ∈ absent τ → e ∉ witness) →
      (∀ e,
        e ∈ terminal →
          dependencySet τ e ⊆ present τ ∪ absent τ) ∧
      (∀ A,
        A ⊆ terminal →
          ∀ e,
            e ∈ terminal →
              (∀ c,
                c ∈ dependencySet τ e →
                  (c ∈ witness ↔ c ∈ A)) →
            (stagedOpen witness e ↔ stagedOpen A e) ∧
            (touched witness e ↔ touched A e) ∧
            (sameColorClosed witness e ↔ sameColorClosed A e) ∧
            (preTerminalRecorded witness e ↔ preTerminalRecorded A e)) ∧
      (∀ A,
        A ⊆ terminal →
        (∀ e,
          e ∈ terminal →
            (stagedOpen witness e ↔ stagedOpen A e) ∧
            (touched witness e ↔ touched A e) ∧
            (sameColorClosed witness e ↔ sameColorClosed A e) ∧
            (preTerminalRecorded witness e ↔ preTerminalRecorded A e)) →
          branchOfAssignment A = β ∧ scanTranscript A = some τ) := by
-- BODY
  classical
  intro Coord BranchLabel Transcript _ terminal order present absent selected
    fixedSupport dependencySet stagedOpen touched sameColorClosed
    preTerminalRecorded branchOfAssignment scanTranscript witness β τ
    hreadClassified _hdependenciesPast _hExactReadStability
    _hDeterministicOutput _horderNodup _horderTerminal _hpresentTerminal
    _habsentTerminal hfixedPresent hselectedAbsent _hpresentAbsent
    _hwitnessPresent _hwitnessAbsent
  refine ⟨?_, _hExactReadStability, _hDeterministicOutput⟩
  intro e he c hc
  rcases hreadClassified e he c hc with
    hfixed | hpresentVariable | hselected | habsentUnselected
  · exact Finset.mem_union.mpr (Or.inl (hfixedPresent hfixed))
  · exact
      Finset.mem_union.mpr
        (Or.inl (Finset.mem_sdiff.mp hpresentVariable).1)
  · exact Finset.mem_union.mpr (Or.inr (hselectedAbsent hselected))
  · exact
      Finset.mem_union.mpr
        (Or.inr (Finset.mem_sdiff.mp habsentUnselected).1)
