import Tablet.FixedSetPreTerminalReplayUniqueness
import Tablet.FixedSetPreTerminalF2QueriesRecorded
import Tablet.TwoBiteProjectionPairTouched
import Tablet.TwoBiteStageRevealedVertex

-- [TABLET NODE: FixedSetPreTerminalStageTouchPreservation]

theorem FixedSetPreTerminalStageTouchPreservation :
    ∀ {n m : ℕ} {p ε : ℝ} (I : Finset (Fin n))
      (recorded : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (ω ω' : TwoBiteSample n m p),
      (∀ e,
        e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔ e ∈ recorded) →
      (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) →
      (∀ c,
        c ∈ recorded →
          (TwoBiteEdgeCoordinateValue ω c ↔
            TwoBiteEdgeCoordinateValue ω' c)) →
      (∀ x,
        TwoBiteStageRevealedVertex ω ε I x ↔
          TwoBiteStageRevealedVertex ω' ε I x) ∧
      (∀ e,
        TwoBiteProjectionPairTouched ω ε I e ↔
          TwoBiteProjectionPairTouched ω' ε I e) := by
-- BODY
  intro n m p ε I recorded ω ω' hRecorded hEmbedding hEdge
  classical
  have hProjection :
      ∀ x : TwoBiteBaseVertex m,
        TwoBiteProjectionContains ω I x ↔
          TwoBiteProjectionContains ω' I x := by
    intro x
    cases x with
    | inl r =>
        simp [TwoBiteProjectionContains, TwoBiteRedProjection, TwoBiteEmbedding,
          hEmbedding]
    | inr b =>
        simp [TwoBiteProjectionContains, TwoBiteBlueProjection, TwoBiteEmbedding,
          hEmbedding]
  have hFiber :
      ∀ x : TwoBiteBaseVertex m,
        TwoBiteBaseFiber ω x = TwoBiteBaseFiber ω' x := by
    intro x
    cases x with
    | inl r =>
        ext v
        simp [TwoBiteBaseFiber, RedFiber, TwoBiteRedProjection, TwoBiteEmbedding,
          hEmbedding v]
    | inr b =>
        ext v
        simp [TwoBiteBaseFiber, BlueFiber, TwoBiteBlueProjection, TwoBiteEmbedding,
          hEmbedding v]
  have hF1 :
      ∀ x : TwoBiteBaseVertex m,
        TwoBiteStageF1 ω I x ↔ TwoBiteStageF1 ω' I x := by
    intro x
    simp [TwoBiteStageF1, hProjection x, hFiber x]
  have hEdgeOld :
      ∀ c,
        c ∈ TwoBitePreTerminalRecordedPairs ω ε I →
          (TwoBiteEdgeCoordinateValue ω c ↔
            TwoBiteEdgeCoordinateValue ω' c) := by
    intro c hc
    exact hEdge c ((hRecorded c).1 hc)
  have hRedEdgeRecorded :
      ∀ r s : Fin m, ∀ q : Fin m × Fin m,
        (q = (r, s) ∨ q = (s, r)) →
        q.1.val < q.2.val →
        TwoBiteStageF1 ω I (Sum.inl s) →
        TwoBiteProjectionContains ω I (Sum.inl r) →
          ((TwoBiteRedGraph ω).Adj r s ↔
            (TwoBiteRedGraph ω').Adj r s) := by
    intro r s q hq hlt hF1s hprojr
    have hcoord :
        Sum.inl q ∈ TwoBitePreTerminalRecordedPairs ω ε I :=
      (FixedSetPreTerminalF2QueriesRecorded I ω).1 r s q hq hlt hF1s hprojr
    have hedge := hEdgeOld (Sum.inl q) hcoord
    rcases hq with hq | hq
    · subst q
      simpa [TwoBiteEdgeCoordinateValue] using hedge
    · subst q
      constructor
      · intro hrs
        exact (SimpleGraph.adj_comm (TwoBiteRedGraph ω') r s).2
          (hedge.1 ((SimpleGraph.adj_comm (TwoBiteRedGraph ω) r s).1 hrs))
      · intro hrs
        exact (SimpleGraph.adj_comm (TwoBiteRedGraph ω) r s).2
          (hedge.2 ((SimpleGraph.adj_comm (TwoBiteRedGraph ω') r s).1 hrs))
  have hBlueEdgeRecorded :
      ∀ b c : Fin m, ∀ q : Fin m × Fin m,
        (q = (b, c) ∨ q = (c, b)) →
        q.1.val < q.2.val →
        TwoBiteStageF1 ω I (Sum.inr c) →
        TwoBiteProjectionContains ω I (Sum.inr b) →
          ((TwoBiteBlueGraph ω).Adj b c ↔
            (TwoBiteBlueGraph ω').Adj b c) := by
    intro b c q hq hlt hF1c hprojb
    have hcoord :
        Sum.inr q ∈ TwoBitePreTerminalRecordedPairs ω ε I :=
      (FixedSetPreTerminalF2QueriesRecorded I ω).2 b c q hq hlt hF1c hprojb
    have hedge := hEdgeOld (Sum.inr q) hcoord
    rcases hq with hq | hq
    · subst q
      simpa [TwoBiteEdgeCoordinateValue] using hedge
    · subst q
      constructor
      · intro hbc
        exact (SimpleGraph.adj_comm (TwoBiteBlueGraph ω') b c).2
          (hedge.1 ((SimpleGraph.adj_comm (TwoBiteBlueGraph ω) b c).1 hbc))
      · intro hbc
        exact (SimpleGraph.adj_comm (TwoBiteBlueGraph ω) b c).2
          (hedge.2 ((SimpleGraph.adj_comm (TwoBiteBlueGraph ω') b c).1 hbc))
  have hRedLoop :
      ∀ r : Fin m,
        ¬ (TwoBiteRedGraph ω).Adj r r ∧
          ¬ (TwoBiteRedGraph ω').Adj r r := by
    intro r
    exact ⟨SimpleGraph.irrefl (TwoBiteRedGraph ω),
      SimpleGraph.irrefl (TwoBiteRedGraph ω')⟩
  have hBlueLoop :
      ∀ b : Fin m,
        ¬ (TwoBiteBlueGraph ω).Adj b b ∧
          ¬ (TwoBiteBlueGraph ω').Adj b b := by
    intro b
    exact ⟨SimpleGraph.irrefl (TwoBiteBlueGraph ω),
      SimpleGraph.irrefl (TwoBiteBlueGraph ω')⟩
  have hBaseAdjCounted :
      ∀ x y : TwoBiteBaseVertex m,
        TwoBiteProjectionContains ω I x →
        TwoBiteStageF1 ω I y →
          (TwoBiteBaseAdj ω x y ↔ TwoBiteBaseAdj ω' x y) := by
    intro x y hx hy
    cases x with
    | inl r =>
        cases y with
        | inl s =>
            by_cases hrs : r = s
            · subst s
              constructor
              · intro h
                exact False.elim ((hRedLoop r).1 h)
              · intro h
                exact False.elim ((hRedLoop r).2 h)
            · by_cases hlt : r.val < s.val
              · simpa [TwoBiteBaseAdj] using
                  hRedEdgeRecorded r s (r, s) (Or.inl rfl) hlt hy hx
              · have hneval : s.val ≠ r.val := by
                  intro hv
                  apply hrs
                  exact Fin.ext hv.symm
                have hslt : s.val < r.val :=
                  Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) hneval
                simpa [TwoBiteBaseAdj] using
                  hRedEdgeRecorded r s (s, r) (Or.inr rfl) hslt hy hx
        | inr b =>
            simp [TwoBiteBaseAdj]
    | inr b =>
        cases y with
        | inl r =>
            simp [TwoBiteBaseAdj]
        | inr c =>
            by_cases hbc : b = c
            · subst c
              constructor
              · intro h
                exact False.elim ((hBlueLoop b).1 h)
              · intro h
                exact False.elim ((hBlueLoop b).2 h)
            · by_cases hlt : b.val < c.val
              · simpa [TwoBiteBaseAdj] using
                  hBlueEdgeRecorded b c (b, c) (Or.inl rfl) hlt hy hx
              · have hneval : c.val ≠ b.val := by
                  intro hv
                  apply hbc
                  exact Fin.ext hv.symm
                have hclt : c.val < b.val :=
                  Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) hneval
                simpa [TwoBiteBaseAdj] using
                  hBlueEdgeRecorded b c (c, b) (Or.inr rfl) hclt hy hx
  have hF2 :
      ∀ x : TwoBiteBaseVertex m,
        TwoBiteStageF2 ω ε I x ↔ TwoBiteStageF2 ω' ε I x := by
    intro x
    constructor
    · intro hxF2
      rcases hxF2 with ⟨hxproj, hxcount⟩
      refine ⟨(hProjection x).1 hxproj, ?_⟩
      have hfilter :
          ((Finset.univ : Finset (TwoBiteBaseVertex m)).filter
              (fun y => TwoBiteStageF1 ω I y ∧ TwoBiteBaseAdj ω x y)) =
            ((Finset.univ : Finset (TwoBiteBaseVertex m)).filter
              (fun y => TwoBiteStageF1 ω' I y ∧ TwoBiteBaseAdj ω' x y)) := by
        apply Finset.filter_congr
        intro y hy
        constructor
        · intro hyold
          exact ⟨(hF1 y).1 hyold.1,
            (hBaseAdjCounted x y hxproj hyold.1).1 hyold.2⟩
        · intro hynew
          have hyF1old : TwoBiteStageF1 ω I y := (hF1 y).2 hynew.1
          exact ⟨hyF1old,
            (hBaseAdjCounted x y hxproj hyF1old).2 hynew.2⟩
      simpa [TwoBiteStageF2, hfilter] using hxcount
    · intro hxF2
      rcases hxF2 with ⟨hxproj, hxcount⟩
      have hxproj_old : TwoBiteProjectionContains ω I x := (hProjection x).2 hxproj
      refine ⟨hxproj_old, ?_⟩
      have hfilter :
          ((Finset.univ : Finset (TwoBiteBaseVertex m)).filter
              (fun y => TwoBiteStageF1 ω I y ∧ TwoBiteBaseAdj ω x y)) =
            ((Finset.univ : Finset (TwoBiteBaseVertex m)).filter
              (fun y => TwoBiteStageF1 ω' I y ∧ TwoBiteBaseAdj ω' x y)) := by
        apply Finset.filter_congr
        intro y hy
        constructor
        · intro hyold
          exact ⟨(hF1 y).1 hyold.1,
            (hBaseAdjCounted x y hxproj_old hyold.1).1 hyold.2⟩
        · intro hynew
          have hyF1old : TwoBiteStageF1 ω I y := (hF1 y).2 hynew.1
          exact ⟨hyF1old,
            (hBaseAdjCounted x y hxproj_old hyF1old).2 hynew.2⟩
      simpa [TwoBiteStageF2, hfilter] using hxcount
  have hStage :
      ∀ x : TwoBiteBaseVertex m,
        TwoBiteStageRevealedVertex ω ε I x ↔
          TwoBiteStageRevealedVertex ω' ε I x := by
    intro x
    simp [TwoBiteStageRevealedVertex, hProjection x, hF1 x, hF2 x]
  refine ⟨hStage, ?_⟩
  intro e
  cases e with
  | inl q =>
      simp [TwoBiteProjectionPairTouched, hStage (Sum.inl q.1),
        hStage (Sum.inl q.2)]
  | inr q =>
      simp [TwoBiteProjectionPairTouched, hStage (Sum.inr q.1),
        hStage (Sum.inr q.2)]
