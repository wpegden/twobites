import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteProjectionSizeEvent
import Tablet.TwoBiteStagedOpenPairs
import Tablet.TwoBiteTerminalCoordinateUniverse

-- [TABLET NODE: FixedSetHistoryCellBlueSupportLabels]

theorem FixedSetHistoryCellBlueSupportLabels :
    ∀ {n m k ℓR ℓB uB : ℕ} {p ε : ℝ}
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
              | Sum.inl _ => False
              | Sum.inr _ => True)],
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
                | Sum.inl _ => False
                | Sum.inr _ => True)).card = uB)) →
      ∃ NB : ℕ,
        (NB : ℝ) ≤ (k : ℝ) ^ 2 ∧
        ∃ blueSupportLabels :
          Finset (Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
          blueSupportLabels.card ≤ Nat.choose NB uB ∧
          (∀ B,
            B ∈ blueSupportLabels →
              B.card = uB ∧
              B ⊆ terminal ∧
              ∀ e,
                e ∈ B →
                  match e with
                  | Sum.inl _ => False
                  | Sum.inr _ => True) ∧
          ∀ ω : TwoBiteSample n m p,
            target ω →
              ((TwoBiteStagedOpenPairs ω ε I).filter
                (fun e =>
                  TwoBiteEdgeCoordinateValue ω e ∧
                    match e with
                    | Sum.inl _ => False
                    | Sum.inr _ => True)) ∈ blueSupportLabels := by
-- BODY
  classical
  intro n m k ℓR ℓB uB p ε I hist target terminal rep
    hDec hIcard hFixedEmbedding hProjectionCell hTargetHist hTerminal
    hBlueCount
  let blueUniverse :
      Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    (TwoBiteBasePairs (I.image (TwoBiteBlueProjection rep))).image Sum.inr
  let blueSupportLabels :
      Finset (Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) :=
    (blueUniverse.powersetCard uB).filter (fun B => B ⊆ terminal)
  refine ⟨blueUniverse.card, ?_, blueSupportLabels, ?_, ?_, ?_⟩
  · have hImageCard :
        (I.image (TwoBiteBlueProjection rep)).card ≤ k := by
      calc
        (I.image (TwoBiteBlueProjection rep)).card ≤ I.card :=
          Finset.card_image_le
        _ = k := hIcard
    have hPairCard :
        (TwoBiteBasePairs (I.image (TwoBiteBlueProjection rep))).card ≤
          (I.image (TwoBiteBlueProjection rep)).card *
            (I.image (TwoBiteBlueProjection rep)).card := by
      have hFilter :=
        Finset.card_filter_le
          ((I.image (TwoBiteBlueProjection rep)).product
            (I.image (TwoBiteBlueProjection rep)))
          (fun e : Fin m × Fin m => e.1.val < e.2.val)
      simpa [TwoBiteBasePairs, TwoBitePairsInSet] using hFilter
    have hUniverseCardNat : blueUniverse.card ≤ k * k := by
      calc
        blueUniverse.card ≤
            (TwoBiteBasePairs (I.image (TwoBiteBlueProjection rep))).card :=
          Finset.card_image_le
        _ ≤
            (I.image (TwoBiteBlueProjection rep)).card *
              (I.image (TwoBiteBlueProjection rep)).card := hPairCard
        _ ≤ k * k := Nat.mul_le_mul hImageCard hImageCard
    have hUniverseCardReal : (blueUniverse.card : ℝ) ≤ (k * k : ℕ) := by
      exact_mod_cast hUniverseCardNat
    simpa [pow_two, Nat.cast_mul] using hUniverseCardReal
  · have hSub :
        blueSupportLabels ⊆ blueUniverse.powersetCard uB :=
      Finset.filter_subset _ _
    calc
      blueSupportLabels.card ≤ (blueUniverse.powersetCard uB).card :=
        Finset.card_le_card hSub
      _ = Nat.choose blueUniverse.card uB := by
        rw [Finset.card_powersetCard]
  · intro B hB
    have hB' := Finset.mem_filter.mp hB
    have hCard : B.card = uB := (Finset.mem_powersetCard.mp hB'.1).2
    have hSubsetUniverse : B ⊆ blueUniverse :=
      (Finset.mem_powersetCard.mp hB'.1).1
    refine ⟨hCard, hB'.2, ?_⟩
    intro e he
    have heUniverse : e ∈ blueUniverse := hSubsetUniverse he
    cases e with
    | inl q =>
        simp [blueUniverse] at heUniverse
    | inr q =>
        trivial
  · intro ω hω
    let Bω :=
      (TwoBiteStagedOpenPairs ω ε I).filter
        (fun e =>
          TwoBiteEdgeCoordinateValue ω e ∧
            match e with
            | Sum.inl _ => False
            | Sum.inr _ => True)
    have hωHist : hist ω := hTargetHist ω hω
    have hEmbedding :
        ∀ x : Fin n, ω.2.2 x = rep.2.2 x :=
      hFixedEmbedding ω hωHist
    have hBlueProjectionEq :
        I.image (TwoBiteBlueProjection ω) =
          I.image (TwoBiteBlueProjection rep) := by
      ext b
      constructor
      · intro hb
        rcases Finset.mem_image.mp hb with ⟨x, hxI, hxb⟩
        refine Finset.mem_image.mpr ⟨x, hxI, ?_⟩
        rw [← hxb]
        simp [TwoBiteBlueProjection, TwoBiteEmbedding, hEmbedding x]
      · intro hb
        rcases Finset.mem_image.mp hb with ⟨x, hxI, hxb⟩
        refine Finset.mem_image.mpr ⟨x, hxI, ?_⟩
        rw [← hxb]
        simp [TwoBiteBlueProjection, TwoBiteEmbedding, hEmbedding x]
    have hBω_subset_terminal : Bω ⊆ terminal := by
      intro e he
      have hStage : e ∈ TwoBiteStagedOpenPairs ω ε I :=
        (Finset.mem_filter.mp he).1
      exact hTerminal ω hωHist e hStage
    have hBω_subset_universe : Bω ⊆ blueUniverse := by
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
          exact False.elim (Finset.mem_filter.mp he).2.2
      | inr q =>
          have hq :
              q ∈
                TwoBiteBasePairs (I.image (TwoBiteBlueProjection ω)) := by
            simpa [TwoBiteProjectionPairSet] using hProjectionMember
          have hqRep :
              q ∈
                TwoBiteBasePairs (I.image (TwoBiteBlueProjection rep)) := by
            simpa [hBlueProjectionEq] using hq
          exact Finset.mem_image.mpr ⟨q, hqRep, rfl⟩
    have hBω_card : Bω.card = uB := hBlueCount ω hω
    have hBω_mem_powerset : Bω ∈ blueUniverse.powersetCard uB := by
      exact Finset.mem_powersetCard.mpr ⟨hBω_subset_universe, hBω_card⟩
    exact Finset.mem_filter.mpr ⟨hBω_mem_powerset, hBω_subset_terminal⟩
