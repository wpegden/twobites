import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteProjectionSizeEvent
import Tablet.TwoBiteStagedOpenPairs
import Tablet.TwoBiteTerminalCoordinateUniverse

-- [TABLET NODE: FixedSetHistoryCellRedProjectionSupportLabels]

theorem FixedSetHistoryCellRedProjectionSupportLabels :
    ∀ {n m k ℓR ℓB uR : ℕ} {p ε : ℝ}
      (I : Finset (Fin n))
      (hist target : TwoBiteSample n m p → Prop)
      (terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (rep : TwoBiteSample n m p)
      [∀ (ω : TwoBiteSample n m p),
        DecidablePred
          (fun e =>
            TwoBiteEdgeCoordinateValue ω e ∧
              match e with
              | Sum.inl _ => True
              | Sum.inr _ => False)],
      I.card = k →
      (∀ ω : TwoBiteSample n m p,
        hist ω → ∀ x : Fin n, ω.2.2 x = rep.2.2 x) →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
            (ℓB := ℓB) ω I) →
      (∀ ω : TwoBiteSample n m p, target ω → hist ω) →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          ∀ e,
            e ∈ TwoBiteStagedOpenPairs ω ε I →
              e ∈ terminal) →
      (∀ ω : TwoBiteSample n m p,
        target ω →
          (((TwoBiteStagedOpenPairs ω ε I).filter
            (fun e =>
              TwoBiteEdgeCoordinateValue ω e ∧
                match e with
                | Sum.inl _ => True
                | Sum.inr _ => False)).card = uR)) →
      ∃ NR : ℕ,
        (NR : ℝ) ≤ (k : ℝ) ^ 2 ∧
        ∃ redSupportLabels :
          Finset (Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
          redSupportLabels.card ≤ Nat.choose NR uR ∧
          (∀ R,
            R ∈ redSupportLabels →
              R.card = uR ∧
              R ⊆ terminal ∧
              ∀ e,
                e ∈ R →
                  match e with
                  | Sum.inl _ => True
                  | Sum.inr _ => False) ∧
          ∀ ω : TwoBiteSample n m p,
            target ω →
              ((TwoBiteStagedOpenPairs ω ε I).filter
                (fun e =>
                  TwoBiteEdgeCoordinateValue ω e ∧
                    match e with
                    | Sum.inl _ => True
                    | Sum.inr _ => False)) ∈ redSupportLabels := by
-- BODY
  classical
  intro n m k ℓR ℓB uR p ε I hist target terminal rep
    hDec hIcard hFixedEmbedding hProjectionCell hTargetHist hTerminal
    hRedCount
  letI :
      ∀ (ω : TwoBiteSample n m p),
        DecidablePred
          (fun e =>
            TwoBiteEdgeCoordinateValue ω e ∧
              match e with
              | Sum.inl _ => True
              | Sum.inr _ => False) := hDec
  let redUniverse :
      Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    (TwoBiteBasePairs (I.image (TwoBiteRedProjection rep))).image Sum.inl
  let redSupportLabels :
      Finset (Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) :=
    (redUniverse.powersetCard uR).filter (fun R => R ⊆ terminal)
  refine ⟨redUniverse.card, ?_, redSupportLabels, ?_, ?_, ?_⟩
  · have hImageCard :
        (I.image (TwoBiteRedProjection rep)).card ≤ k := by
      calc
        (I.image (TwoBiteRedProjection rep)).card ≤ I.card :=
          Finset.card_image_le
        _ = k := hIcard
    have hPairCard :
        (TwoBiteBasePairs (I.image (TwoBiteRedProjection rep))).card ≤
          (I.image (TwoBiteRedProjection rep)).card *
            (I.image (TwoBiteRedProjection rep)).card := by
      have hFilter :=
        Finset.card_filter_le
          ((I.image (TwoBiteRedProjection rep)).product
            (I.image (TwoBiteRedProjection rep)))
          (fun e : Fin m × Fin m => e.1.val < e.2.val)
      simpa [TwoBiteBasePairs, TwoBitePairsInSet] using hFilter
    have hUniverseCardNat : redUniverse.card ≤ k * k := by
      calc
        redUniverse.card ≤
            (TwoBiteBasePairs (I.image (TwoBiteRedProjection rep))).card :=
          Finset.card_image_le
        _ ≤
            (I.image (TwoBiteRedProjection rep)).card *
              (I.image (TwoBiteRedProjection rep)).card := hPairCard
        _ ≤ k * k := Nat.mul_le_mul hImageCard hImageCard
    have hUniverseCardReal : (redUniverse.card : ℝ) ≤ (k * k : ℕ) := by
      exact_mod_cast hUniverseCardNat
    simpa [pow_two, Nat.cast_mul] using hUniverseCardReal
  · have hSub :
        redSupportLabels ⊆ redUniverse.powersetCard uR :=
      Finset.filter_subset _ _
    calc
      redSupportLabels.card ≤ (redUniverse.powersetCard uR).card :=
        Finset.card_le_card hSub
      _ = Nat.choose redUniverse.card uR := by
        rw [Finset.card_powersetCard]
  · intro R hR
    have hR' := Finset.mem_filter.mp hR
    have hCard : R.card = uR := (Finset.mem_powersetCard.mp hR'.1).2
    have hSubsetUniverse : R ⊆ redUniverse :=
      (Finset.mem_powersetCard.mp hR'.1).1
    refine ⟨hCard, hR'.2, ?_⟩
    intro e he
    have heUniverse : e ∈ redUniverse := hSubsetUniverse he
    cases e with
    | inl q =>
        trivial
    | inr q =>
        simp [redUniverse] at heUniverse
  · intro ω hω
    let Rω :=
      (TwoBiteStagedOpenPairs ω ε I).filter
        (fun e =>
          TwoBiteEdgeCoordinateValue ω e ∧
            match e with
            | Sum.inl _ => True
            | Sum.inr _ => False)
    have hωHist : hist ω := hTargetHist ω hω
    have hEmbedding :
        ∀ x : Fin n, ω.2.2 x = rep.2.2 x :=
      hFixedEmbedding ω hωHist
    have hRedProjectionEq :
        I.image (TwoBiteRedProjection ω) =
          I.image (TwoBiteRedProjection rep) := by
      ext r
      constructor
      · intro hr
        rcases Finset.mem_image.mp hr with ⟨x, hxI, hxr⟩
        refine Finset.mem_image.mpr ⟨x, hxI, ?_⟩
        rw [← hxr]
        simp [TwoBiteRedProjection, TwoBiteEmbedding, hEmbedding x]
      · intro hr
        rcases Finset.mem_image.mp hr with ⟨x, hxI, hxr⟩
        refine Finset.mem_image.mpr ⟨x, hxI, ?_⟩
        rw [← hxr]
        simp [TwoBiteRedProjection, TwoBiteEmbedding, hEmbedding x]
    have hRω_subset_terminal : Rω ⊆ terminal := by
      intro e he
      have hStage : e ∈ TwoBiteStagedOpenPairs ω ε I :=
        (Finset.mem_filter.mp he).1
      exact hTerminal ω hωHist e hStage
    have hRω_subset_universe : Rω ⊆ redUniverse := by
      intro e he
      have hStage : e ∈ TwoBiteStagedOpenPairs ω ε I :=
        (Finset.mem_filter.mp he).1
      have hProjectionMember :
          e ∈ TwoBiteProjectionPairSet ω I := by
        have hStage' :
            e ∈ (TwoBiteProjectionPairSet ω I).filter
              (fun e =>
                ¬ TwoBiteProjectionPairSameColorClosed ω I e ∧
                  ¬ TwoBiteProjectionPairTouched ω ε I e ∧
                    e ∉ TwoBitePreTerminalRecordedPairs ω ε I) := by
          simpa [TwoBiteStagedOpenPairs] using hStage
        exact (Finset.mem_filter.mp hStage').1
      cases e with
      | inl q =>
          have hq :
              q ∈
                TwoBiteBasePairs (I.image (TwoBiteRedProjection ω)) := by
            simpa [TwoBiteProjectionPairSet] using hProjectionMember
          have hqRep :
              q ∈
                TwoBiteBasePairs (I.image (TwoBiteRedProjection rep)) := by
            simpa [hRedProjectionEq] using hq
          exact Finset.mem_image.mpr ⟨q, hqRep, rfl⟩
      | inr q =>
          exact False.elim (Finset.mem_filter.mp he).2.2
    have hRω_card : Rω.card = uR := hRedCount ω hω
    have hRω_mem_powerset : Rω ∈ redUniverse.powersetCard uR := by
      exact Finset.mem_powersetCard.mpr ⟨hRω_subset_universe, hRω_card⟩
    exact Finset.mem_filter.mpr ⟨hRω_mem_powerset, hRω_subset_terminal⟩
