import Tablet.ClosedPairsBound
import Tablet.FixedSetHistoryCellGlobalRedExceptionalWitness
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBiteRegularityEvent
import Tablet.TwoBiteStagedOpenPairs

-- [TABLET NODE: FixedSetHistoryCellRedSupportLabels]

theorem FixedSetHistoryCellRedSupportLabels :
    ∀ {n m k uR : ℕ} {p ε ε1 ε2 : ℝ}
      (I : Finset (Fin n))
      (hist target : TwoBiteSample n m p → Prop)
      (recorded terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      [∀ (ω : TwoBiteSample n m p),
        DecidablePred
          (fun e =>
            TwoBiteEdgeCoordinateValue ω e ∧
              match e with
              | Sum.inl _ => True
              | Sum.inr _ => False)]
      [∀ (ω : TwoBiteSample n m p),
        DecidablePred
          (fun e =>
            TwoBiteEdgeCoordinateValue ω e ∧
              match e with
              | Sum.inl _ => False
              | Sum.inr _ => True)],
      (∃ NR0 : ℕ,
        (NR0 : ℝ) ≤ 3 * ε1 * (k : ℝ) ^ 2 ∧
        ∀ branch : TwoBiteSample n m p,
          hist branch →
            ∃ ER : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
              ER ⊆ terminal ∧
              (ER.card : ℝ) ≤ (NR0 : ℝ) ∧
              ∀ ω : TwoBiteSample n m p,
                hist ω →
                (∀ x : Fin n, ω.2.2 x = branch.2.2 x) →
                (∀ e,
                  e ∈ recorded →
                    (TwoBiteEdgeCoordinateValue ω e ↔
                      TwoBiteEdgeCoordinateValue branch e)) →
                (∀ e,
                  e ∈ terminal →
                    match e with
                    | Sum.inl _ => True
                    | Sum.inr _ =>
                        (TwoBiteEdgeCoordinateValue ω e ↔
                          TwoBiteEdgeCoordinateValue branch e)) →
                TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
                  ∀ e,
                    e ∈ TwoBiteStagedOpenPairs ω ε I →
                    TwoBiteEdgeCoordinateValue ω e →
                    (match e with
                    | Sum.inl _ => True
                    | Sum.inr _ => False) →
                    (TwoBiteFinalGraph ω).2.2.IsIndepSet
                      (↑I : Set (Fin n)) →
                    e ∈ ER) →
      (∀ ω : TwoBiteSample n m p, target ω → hist ω) →
      (∀ ω : TwoBiteSample n m p,
        target ω → TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω) →
      (∀ ω : TwoBiteSample n m p,
        target ω → (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n))) →
      (∀ ω : TwoBiteSample n m p,
        target ω →
          (((TwoBiteStagedOpenPairs ω ε I).filter
            (fun e =>
              TwoBiteEdgeCoordinateValue ω e ∧
                match e with
                | Sum.inl _ => True
                | Sum.inr _ => False)).card = uR)) →
      ∃ NR : ℕ,
        (NR : ℝ) ≤ 3 * ε1 * (k : ℝ) ^ 2 ∧
        ∃ (RedLabel : Type) (_ : Fintype RedLabel),
          Fintype.card RedLabel ≤ Nat.choose NR uR ∧
          ∃ redSupport :
            TwoBiteSample n m p →
              RedLabel →
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
            ∀ branch ω : TwoBiteSample n m p,
              target ω →
              hist branch →
              (∀ x : Fin n, ω.2.2 x = branch.2.2 x) →
              (∀ e,
                e ∈ recorded →
                  (TwoBiteEdgeCoordinateValue ω e ↔
                    TwoBiteEdgeCoordinateValue branch e)) →
              (∀ e,
                e ∈ terminal →
                  match e with
                  | Sum.inl _ => True
                  | Sum.inr _ =>
                      (TwoBiteEdgeCoordinateValue ω e ↔
                        TwoBiteEdgeCoordinateValue branch e)) →
                ∃ J : RedLabel,
                  redSupport branch J =
                    (TwoBiteStagedOpenPairs ω ε I).filter
                      (fun e =>
                        TwoBiteEdgeCoordinateValue ω e ∧
                          match e with
                          | Sum.inl _ => True
                          | Sum.inr _ => False) ∧
                  (redSupport branch J).card = uR ∧
                  redSupport branch J ⊆ terminal ∧
                  ∀ e,
                    e ∈ redSupport branch J →
                      match e with
                      | Sum.inl _ => True
                      | Sum.inr _ => False := by
-- BODY
  classical
  intro n m k uR p ε ε1 ε2 I hist target recorded terminal
    hDecRed hDecBlue hGlobal hTargetHist hTargetRegular hTargetIndep
    hRedCount
  letI :
      ∀ (ω : TwoBiteSample n m p),
        DecidablePred
          (fun e =>
            TwoBiteEdgeCoordinateValue ω e ∧
              match e with
              | Sum.inl _ => True
              | Sum.inr _ => False) := hDecRed
  letI :
      ∀ (ω : TwoBiteSample n m p),
        DecidablePred
          (fun e =>
            TwoBiteEdgeCoordinateValue ω e ∧
              match e with
              | Sum.inl _ => False
              | Sum.inr _ => True) := hDecBlue
  rcases hGlobal with ⟨NR0, hNR0_bound, hBranchPackage⟩
  let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
  let ERof : TwoBiteSample n m p → Finset Coord := fun branch =>
    if h : hist branch then Classical.choose (hBranchPackage branch h) else ∅
  have hERof_spec :
      ∀ branch (hbranch : hist branch),
        ERof branch ⊆ terminal ∧
        ((ERof branch).card : ℝ) ≤ (NR0 : ℝ) ∧
        ∀ ω : TwoBiteSample n m p,
          hist ω →
          (∀ x : Fin n, ω.2.2 x = branch.2.2 x) →
          (∀ e,
            e ∈ recorded →
              (TwoBiteEdgeCoordinateValue ω e ↔
                TwoBiteEdgeCoordinateValue branch e)) →
          (∀ e,
            e ∈ terminal →
              match e with
              | Sum.inl _ => True
              | Sum.inr _ =>
                  (TwoBiteEdgeCoordinateValue ω e ↔
                    TwoBiteEdgeCoordinateValue branch e)) →
          TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
            ∀ e,
              e ∈ TwoBiteStagedOpenPairs ω ε I →
              TwoBiteEdgeCoordinateValue ω e →
              (match e with
              | Sum.inl _ => True
              | Sum.inr _ => False) →
              (TwoBiteFinalGraph ω).2.2.IsIndepSet
                (↑I : Set (Fin n)) →
              e ∈ ERof branch := by
    intro branch hbranch
    simpa [ERof, hbranch] using
      Classical.choose_spec (hBranchPackage branch hbranch)
  let embOf :
      (branch : TwoBiteSample n m p) →
        ({e // e ∈ ERof branch} ↪ Fin NR0) := fun branch =>
    Classical.choice <|
      Function.Embedding.nonempty_of_card_le
        (α := {e // e ∈ ERof branch}) (β := Fin NR0) (by
          by_cases hbranch : hist branch
          · have hcardReal : ((ERof branch).card : ℝ) ≤ (NR0 : ℝ) :=
              (hERof_spec branch hbranch).2.1
            have hcardNat : (ERof branch).card ≤ NR0 := by
              exact_mod_cast hcardReal
            simpa using hcardNat
          · have hEmpty : ERof branch = ∅ := by
              simp [ERof, hbranch]
            simp [hEmpty])
  let RedLabel :=
    {J : Finset (Fin NR0) //
      J ∈ (Finset.univ : Finset (Fin NR0)).powersetCard uR}
  letI : Fintype RedLabel := by
    infer_instance
  let redSupport :
      TwoBiteSample n m p → RedLabel → Finset Coord := fun branch J =>
    (ERof branch).filter
      (fun e => ∃ h : e ∈ ERof branch, embOf branch ⟨e, h⟩ ∈ J.1)
  refine ⟨NR0, hNR0_bound, RedLabel, inferInstance, ?_, redSupport, ?_⟩
  · have hCardEq : Fintype.card RedLabel = Nat.choose NR0 uR := by
      dsimp [RedLabel]
      rw [Fintype.card_subtype]
      rw [show
          (Finset.univ.filter
              (fun J : Finset (Fin NR0) =>
                J ∈ (Finset.univ : Finset (Fin NR0)).powersetCard uR)) =
            (Finset.univ : Finset (Fin NR0)).powersetCard uR by
        ext J
        simp]
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    exact le_of_eq hCardEq
  · intro branch ω hω hbranch hSameEmbedding hRecordedCompat
      hTerminalBlueCompat
    let Bω : Finset Coord :=
      (TwoBiteStagedOpenPairs ω ε I).filter
        (fun e =>
          TwoBiteEdgeCoordinateValue ω e ∧
            match e with
            | Sum.inl _ => True
            | Sum.inr _ => False)
    have hBω_eq :
        Bω =
          (TwoBiteStagedOpenPairs ω ε I).filter
            (fun e =>
              TwoBiteEdgeCoordinateValue ω e ∧
                match e with
                | Sum.inl _ => True
                | Sum.inr _ => False) := by
      ext e
      constructor
      · intro he
        simpa [Bω] using he
      · intro he
        simpa [Bω] using he
    have hωHist : hist ω := hTargetHist ω hω
    have hERspec := hERof_spec branch hbranch
    have hBω_subset_ER : Bω ⊆ ERof branch := by
      intro e he
      have hStage : e ∈ TwoBiteStagedOpenPairs ω ε I :=
        (Finset.mem_filter.mp he).1
      have hPresent : TwoBiteEdgeCoordinateValue ω e :=
        (Finset.mem_filter.mp he).2.1
      cases e with
      | inl q =>
          exact
            hERspec.2.2 ω hωHist hSameEmbedding hRecordedCompat
              hTerminalBlueCompat (hTargetRegular ω hω) (Sum.inl q)
              hStage hPresent trivial (hTargetIndep ω hω)
      | inr q =>
          exact False.elim (Finset.mem_filter.mp he).2.2
    let Jset : Finset (Fin NR0) :=
      Bω.attach.image
        (fun e : {e // e ∈ Bω} =>
          embOf branch ⟨e.1, hBω_subset_ER e.2⟩)
    have hJset_card : Jset.card = uR := by
      have hinj :
          Function.Injective
            (fun e : {e // e ∈ Bω} =>
              embOf branch ⟨e.1, hBω_subset_ER e.2⟩) := by
        intro a b hab
        apply Subtype.ext
        have hsub :
            (⟨a.1, hBω_subset_ER a.2⟩ :
                {e // e ∈ ERof branch}) =
              ⟨b.1, hBω_subset_ER b.2⟩ :=
          (embOf branch).injective hab
        exact congrArg (fun z : {e // e ∈ ERof branch} => z.1) hsub
      calc
        Jset.card = Bω.attach.card := by
          dsimp [Jset]
          rw [Finset.card_image_of_injective _ hinj]
        _ = Bω.card := by simp
        _ = uR := by
          rw [hBω_eq]
          exact hRedCount ω hω
    have hJset_mem :
        Jset ∈ (Finset.univ : Finset (Fin NR0)).powersetCard uR := by
      exact Finset.mem_powersetCard.mpr
        ⟨by intro x hx; simp, hJset_card⟩
    let J : RedLabel := ⟨Jset, hJset_mem⟩
    have hSupport_eq : redSupport branch J = Bω := by
      ext e
      constructor
      · intro he
        have heFilter :
            e ∈ (ERof branch).filter
              (fun e =>
                ∃ h : e ∈ ERof branch,
                  embOf branch ⟨e, h⟩ ∈ J.1) := by
          simpa [redSupport] using he
        rcases (Finset.mem_filter.mp heFilter).2 with ⟨heER, heJ⟩
        have heJ' : embOf branch ⟨e, heER⟩ ∈ Jset := by
          simpa [J] using heJ
        rcases Finset.mem_image.mp heJ' with ⟨a, _ha, haeq⟩
        have hsub :
            (⟨a.1, hBω_subset_ER a.2⟩ :
                {e // e ∈ ERof branch}) =
              ⟨e, heER⟩ :=
          (embOf branch).injective haeq
        have hae : a.1 = e :=
          congrArg (fun z : {e // e ∈ ERof branch} => z.1) hsub
        simpa [hae] using a.2
      · intro heB
        have heER : e ∈ ERof branch := hBω_subset_ER heB
        have heFilter :
            e ∈ (ERof branch).filter
              (fun e =>
                ∃ h : e ∈ ERof branch,
                  embOf branch ⟨e, h⟩ ∈ J.1) := by
          refine Finset.mem_filter.mpr ⟨heER, ?_⟩
          refine ⟨heER, ?_⟩
          have hmemJset : embOf branch ⟨e, heER⟩ ∈ Jset := by
            dsimp [Jset]
            exact Finset.mem_image.mpr ⟨⟨e, heB⟩, by simp, rfl⟩
          simpa [J] using hmemJset
        simpa [redSupport] using heFilter
    refine ⟨J, ?_, ?_, ?_, ?_⟩
    · exact hSupport_eq.trans hBω_eq
    · rw [hSupport_eq]
      rw [hBω_eq]
      exact hRedCount ω hω
    · rw [hSupport_eq]
      exact fun e he => hERspec.1 (hBω_subset_ER he)
    · intro e he
      rw [hSupport_eq] at he
      exact (Finset.mem_filter.mp he).2.2
