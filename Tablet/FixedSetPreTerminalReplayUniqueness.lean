import Tablet.FixedSetPreTerminalF2QueriesRecorded
import Tablet.TwoBitePreTerminalRecordedPairs
import Tablet.TwoBiteEdgeCoordinateValue

-- [TABLET NODE: FixedSetPreTerminalReplayUniqueness]

theorem FixedSetPreTerminalReplayUniqueness :
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
      ∀ e,
        e ∈ TwoBitePreTerminalRecordedPairs ω' ε I ↔ e ∈ recorded := by
-- BODY
  intro n m p ε I recorded ω ω' hRecorded hEmbedding hEdge e
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
  have hRedIncidentEdge :
      ∀ r s : Fin m, ∀ q : Fin m × Fin m,
        (q = (r, s) ∨ q = (s, r)) →
        q.1.val < q.2.val →
        TwoBiteStageRevealedVertex ω ε I (Sum.inl r) →
        TwoBiteProjectionContains ω I (Sum.inl s) →
          ((TwoBiteRedGraph ω).Adj r s ↔
            (TwoBiteRedGraph ω').Adj r s) := by
    intro r s q hq hlt hst hproj
    have hcoord :
        Sum.inl q ∈ TwoBitePreTerminalRecordedPairs ω ε I := by
      simp [TwoBitePreTerminalRecordedPairs, TwoBiteTerminalCoordinateUniverse]
      constructor
      · exact hlt
      · left
        exact ⟨r, s, hq, Or.inl ⟨hst, hproj⟩⟩
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
  have hBlueIncidentEdge :
      ∀ b c : Fin m, ∀ q : Fin m × Fin m,
        (q = (b, c) ∨ q = (c, b)) →
        q.1.val < q.2.val →
        TwoBiteStageRevealedVertex ω ε I (Sum.inr b) →
        TwoBiteProjectionContains ω I (Sum.inr c) →
          ((TwoBiteBlueGraph ω).Adj b c ↔
            (TwoBiteBlueGraph ω').Adj b c) := by
    intro b c q hq hlt hst hproj
    have hcoord :
        Sum.inr q ∈ TwoBitePreTerminalRecordedPairs ω ε I := by
      simp [TwoBitePreTerminalRecordedPairs, TwoBiteTerminalCoordinateUniverse]
      constructor
      · exact hlt
      · left
        exact ⟨b, c, hq, Or.inl ⟨hst, hproj⟩⟩
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
  have hBaseAdjIncident :
      ∀ x y : TwoBiteBaseVertex m,
        TwoBiteStageRevealedVertex ω ε I x →
        TwoBiteProjectionContains ω I y →
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
                  hRedIncidentEdge r s (r, s) (Or.inl rfl) hlt hx hy
              · have hneval : s.val ≠ r.val := by
                  intro hv
                  apply hrs
                  exact Fin.ext hv.symm
                have hslt : s.val < r.val :=
                  Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) hneval
                simpa [TwoBiteBaseAdj] using
                  hRedIncidentEdge r s (s, r) (Or.inr rfl) hslt hx hy
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
                  hBlueIncidentEdge b c (b, c) (Or.inl rfl) hlt hx hy
              · have hneval : c.val ≠ b.val := by
                  intro hv
                  apply hbc
                  exact Fin.ext hv.symm
                have hclt : c.val < b.val :=
                  Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) hneval
                simpa [TwoBiteBaseAdj] using
                  hBlueIncidentEdge b c (c, b) (Or.inr rfl) hclt hx hy
  have hXStable :
      ∀ x : TwoBiteBaseVertex m,
        TwoBiteStageRevealedVertex ω ε I x →
          TwoBiteX ω I x = TwoBiteX ω' I x := by
    intro x hx
    apply Finset.ext
    intro v
    cases x with
    | inl r =>
        constructor
        · intro hv
          simp [TwoBiteX, TwoBiteLiftedNeighborhood] at hv ⊢
          refine ⟨hv.1, ?_⟩
          have hprojv :
              TwoBiteProjectionContains ω I
                (Sum.inl (TwoBiteRedProjection ω v)) := by
            simp [TwoBiteProjectionContains]
            exact ⟨v, hv.1, rfl⟩
          have hold :
              TwoBiteBaseAdj ω (Sum.inl r)
                (Sum.inl (TwoBiteRedProjection ω v)) := by
            simpa [TwoBiteBaseAdj] using hv.2
          have hnew :=
            (hBaseAdjIncident (Sum.inl r)
              (Sum.inl (TwoBiteRedProjection ω v)) hx hprojv).1 hold
          simpa [TwoBiteBaseAdj, TwoBiteRedProjection, TwoBiteEmbedding,
            hEmbedding v] using hnew
        · intro hv
          simp [TwoBiteX, TwoBiteLiftedNeighborhood] at hv ⊢
          refine ⟨hv.1, ?_⟩
          have hprojv :
              TwoBiteProjectionContains ω I
                (Sum.inl (TwoBiteRedProjection ω v)) := by
            simp [TwoBiteProjectionContains]
            exact ⟨v, hv.1, rfl⟩
          have hnew :
              TwoBiteBaseAdj ω' (Sum.inl r)
                (Sum.inl (TwoBiteRedProjection ω v)) := by
            simpa [TwoBiteBaseAdj, TwoBiteRedProjection, TwoBiteEmbedding,
              hEmbedding v] using hv.2
          have hold :=
            (hBaseAdjIncident (Sum.inl r)
              (Sum.inl (TwoBiteRedProjection ω v)) hx hprojv).2 hnew
          simpa [TwoBiteBaseAdj] using hold
    | inr b =>
        constructor
        · intro hv
          simp [TwoBiteX, TwoBiteLiftedNeighborhood] at hv ⊢
          refine ⟨hv.1, ?_⟩
          have hprojv :
              TwoBiteProjectionContains ω I
                (Sum.inr (TwoBiteBlueProjection ω v)) := by
            simp [TwoBiteProjectionContains]
            exact ⟨v, hv.1, rfl⟩
          have hold :
              TwoBiteBaseAdj ω (Sum.inr b)
                (Sum.inr (TwoBiteBlueProjection ω v)) := by
            simpa [TwoBiteBaseAdj] using hv.2
          have hnew :=
            (hBaseAdjIncident (Sum.inr b)
              (Sum.inr (TwoBiteBlueProjection ω v)) hx hprojv).1 hold
          simpa [TwoBiteBaseAdj, TwoBiteBlueProjection, TwoBiteEmbedding,
            hEmbedding v] using hnew
        · intro hv
          simp [TwoBiteX, TwoBiteLiftedNeighborhood] at hv ⊢
          refine ⟨hv.1, ?_⟩
          have hprojv :
              TwoBiteProjectionContains ω I
                (Sum.inr (TwoBiteBlueProjection ω v)) := by
            simp [TwoBiteProjectionContains]
            exact ⟨v, hv.1, rfl⟩
          have hnew :
              TwoBiteBaseAdj ω' (Sum.inr b)
                (Sum.inr (TwoBiteBlueProjection ω v)) := by
            simpa [TwoBiteBaseAdj, TwoBiteBlueProjection, TwoBiteEmbedding,
              hEmbedding v] using hv.2
          have hold :=
            (hBaseAdjIncident (Sum.inr b)
              (Sum.inr (TwoBiteBlueProjection ω v)) hx hprojv).2 hnew
          simpa [TwoBiteBaseAdj] using hold
  have hRedXImage :
      ∀ x : TwoBiteBaseVertex m,
        TwoBiteStageRevealedVertex ω ε I x →
          (TwoBiteX ω I x).image (TwoBiteRedProjection ω) =
            (TwoBiteX ω' I x).image (TwoBiteRedProjection ω') := by
    intro x hx
    apply Finset.ext
    intro r
    constructor
    · intro hr
      rcases Finset.mem_image.mp hr with ⟨v, hv, hvr⟩
      exact Finset.mem_image.mpr
        ⟨v, by simpa [hXStable x hx] using hv,
          by
            simpa [TwoBiteRedProjection, TwoBiteEmbedding, hEmbedding v] using hvr⟩
    · intro hr
      rcases Finset.mem_image.mp hr with ⟨v, hv, hvr⟩
      exact Finset.mem_image.mpr
        ⟨v, by simpa [hXStable x hx] using hv,
          by
            simpa [TwoBiteRedProjection, TwoBiteEmbedding, hEmbedding v] using hvr⟩
  have hBlueXImage :
      ∀ x : TwoBiteBaseVertex m,
        TwoBiteStageRevealedVertex ω ε I x →
          (TwoBiteX ω I x).image (TwoBiteBlueProjection ω) =
            (TwoBiteX ω' I x).image (TwoBiteBlueProjection ω') := by
    intro x hx
    apply Finset.ext
    intro b
    constructor
    · intro hb
      rcases Finset.mem_image.mp hb with ⟨v, hv, hvb⟩
      exact Finset.mem_image.mpr
        ⟨v, by simpa [hXStable x hx] using hv,
          by
            simpa [TwoBiteBlueProjection, TwoBiteEmbedding, hEmbedding v] using hvb⟩
    · intro hb
      rcases Finset.mem_image.mp hb with ⟨v, hv, hvb⟩
      exact Finset.mem_image.mpr
        ⟨v, by simpa [hXStable x hx] using hv,
          by
            simpa [TwoBiteBlueProjection, TwoBiteEmbedding, hEmbedding v] using hvb⟩
  constructor
  · intro hmem
    apply (hRecorded e).1
    cases e with
    | inl q =>
        simp [TwoBitePreTerminalRecordedPairs, TwoBiteTerminalCoordinateUniverse]
          at hmem ⊢
        rcases hmem with ⟨hlt, hbranch⟩
        refine ⟨hlt, ?_⟩
        rcases hbranch with hincident | hX
        · left
          rcases hincident with ⟨r, s, hq, hcases⟩
          refine ⟨r, s, hq, ?_⟩
          rcases hcases with hcases | hcases
          · left
            exact ⟨(hStage (Sum.inl r)).2 hcases.1,
              (hProjection (Sum.inl s)).2 hcases.2⟩
          · right
            exact ⟨(hStage (Sum.inl s)).2 hcases.1,
              (hProjection (Sum.inl r)).2 hcases.2⟩
        · right
          rcases hX with hX | hX
          · left
            rcases hX with ⟨a, hxstage, hxpair⟩
            have hxstage_old :
                TwoBiteStageRevealedVertex ω ε I (Sum.inl a) :=
              (hStage (Sum.inl a)).2 hxstage
            exact ⟨a, hxstage_old,
              by simpa [hRedXImage (Sum.inl a) hxstage_old] using hxpair⟩
          · right
            rcases hX with ⟨b, hxstage, hxpair⟩
            have hxstage_old :
                TwoBiteStageRevealedVertex ω ε I (Sum.inr b) :=
              (hStage (Sum.inr b)).2 hxstage
            exact ⟨b, hxstage_old,
              by simpa [hRedXImage (Sum.inr b) hxstage_old] using hxpair⟩
    | inr q =>
        simp [TwoBitePreTerminalRecordedPairs, TwoBiteTerminalCoordinateUniverse]
          at hmem ⊢
        rcases hmem with ⟨hlt, hbranch⟩
        refine ⟨hlt, ?_⟩
        rcases hbranch with hincident | hX
        · left
          rcases hincident with ⟨b, c, hq, hcases⟩
          refine ⟨b, c, hq, ?_⟩
          rcases hcases with hcases | hcases
          · left
            exact ⟨(hStage (Sum.inr b)).2 hcases.1,
              (hProjection (Sum.inr c)).2 hcases.2⟩
          · right
            exact ⟨(hStage (Sum.inr c)).2 hcases.1,
              (hProjection (Sum.inr b)).2 hcases.2⟩
        · right
          rcases hX with hX | hX
          · left
            rcases hX with ⟨a, hxstage, hxpair⟩
            have hxstage_old :
                TwoBiteStageRevealedVertex ω ε I (Sum.inl a) :=
              (hStage (Sum.inl a)).2 hxstage
            exact ⟨a, hxstage_old,
              by simpa [hBlueXImage (Sum.inl a) hxstage_old] using hxpair⟩
          · right
            rcases hX with ⟨b, hxstage, hxpair⟩
            have hxstage_old :
                TwoBiteStageRevealedVertex ω ε I (Sum.inr b) :=
              (hStage (Sum.inr b)).2 hxstage
            exact ⟨b, hxstage_old,
              by simpa [hBlueXImage (Sum.inr b) hxstage_old] using hxpair⟩
  · intro hmem
    have hold : e ∈ TwoBitePreTerminalRecordedPairs ω ε I :=
      (hRecorded e).2 hmem
    cases e with
    | inl q =>
        simp [TwoBitePreTerminalRecordedPairs, TwoBiteTerminalCoordinateUniverse]
          at hold ⊢
        rcases hold with ⟨hlt, hbranch⟩
        refine ⟨hlt, ?_⟩
        rcases hbranch with hincident | hX
        · left
          rcases hincident with ⟨r, s, hq, hcases⟩
          refine ⟨r, s, hq, ?_⟩
          rcases hcases with hcases | hcases
          · left
            exact ⟨(hStage (Sum.inl r)).1 hcases.1,
              (hProjection (Sum.inl s)).1 hcases.2⟩
          · right
            exact ⟨(hStage (Sum.inl s)).1 hcases.1,
              (hProjection (Sum.inl r)).1 hcases.2⟩
        · right
          rcases hX with hX | hX
          · left
            rcases hX with ⟨a, hxstage, hxpair⟩
            exact ⟨a, (hStage (Sum.inl a)).1 hxstage,
              by simpa [hRedXImage (Sum.inl a) hxstage] using hxpair⟩
          · right
            rcases hX with ⟨b, hxstage, hxpair⟩
            exact ⟨b, (hStage (Sum.inr b)).1 hxstage,
              by simpa [hRedXImage (Sum.inr b) hxstage] using hxpair⟩
    | inr q =>
        simp [TwoBitePreTerminalRecordedPairs, TwoBiteTerminalCoordinateUniverse]
          at hold ⊢
        rcases hold with ⟨hlt, hbranch⟩
        refine ⟨hlt, ?_⟩
        rcases hbranch with hincident | hX
        · left
          rcases hincident with ⟨b, c, hq, hcases⟩
          refine ⟨b, c, hq, ?_⟩
          rcases hcases with hcases | hcases
          · left
            exact ⟨(hStage (Sum.inr b)).1 hcases.1,
              (hProjection (Sum.inr c)).1 hcases.2⟩
          · right
            exact ⟨(hStage (Sum.inr c)).1 hcases.1,
              (hProjection (Sum.inr b)).1 hcases.2⟩
        · right
          rcases hX with hX | hX
          · left
            rcases hX with ⟨a, hxstage, hxpair⟩
            exact ⟨a, (hStage (Sum.inl a)).1 hxstage,
              by simpa [hBlueXImage (Sum.inl a) hxstage] using hxpair⟩
          · right
            rcases hX with ⟨b, hxstage, hxpair⟩
            exact ⟨b, (hStage (Sum.inr b)).1 hxstage,
              by simpa [hBlueXImage (Sum.inr b) hxstage] using hxpair⟩
