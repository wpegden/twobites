import Tablet.ClosedPairsBound
import Tablet.FixedSetHistoryCellGlobalBlueExceptionalWitness
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBiteRegularityEvent
import Tablet.TwoBiteStagedOpenPairs

-- [TABLET NODE: FixedSetHistoryCellBlueExceptionalSupportLabels]

theorem FixedSetHistoryCellBlueExceptionalSupportLabels :
    ∀ {n m k uB : ℕ} {p ε ε1 ε2 : ℝ}
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
      (∃ NB0 : ℕ,
        (NB0 : ℝ) ≤ 3 * ε1 * (k : ℝ) ^ 2 ∧
        ∀ branch : TwoBiteSample n m p,
          hist branch →
            ∃ EB : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
              EB ⊆ terminal ∧
              (EB.card : ℝ) ≤ (NB0 : ℝ) ∧
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
                    | Sum.inl _ =>
                        (TwoBiteEdgeCoordinateValue ω e ↔
                          TwoBiteEdgeCoordinateValue branch e)
                    | Sum.inr _ => True) →
                TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
                  ∀ e,
                    e ∈ TwoBiteStagedOpenPairs ω ε I →
                    TwoBiteEdgeCoordinateValue ω e →
                    (match e with
                    | Sum.inl _ => False
                    | Sum.inr _ => True) →
                    (TwoBiteFinalGraph ω).2.2.IsIndepSet
                      (↑I : Set (Fin n)) →
                    e ∈ EB) →
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
                | Sum.inl _ => False
                | Sum.inr _ => True)).card = uB)) →
      ∃ NB : ℕ,
        (NB : ℝ) ≤ 3 * ε1 * (k : ℝ) ^ 2 ∧
        ∃ (BlueLabel : Type) (_ : Fintype BlueLabel),
          Fintype.card BlueLabel ≤ Nat.choose NB uB ∧
          ∃ blueSupport :
            TwoBiteSample n m p →
              BlueLabel →
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
                  | Sum.inl _ =>
                      (TwoBiteEdgeCoordinateValue ω e ↔
                        TwoBiteEdgeCoordinateValue branch e)
                  | Sum.inr _ => True) →
                ∃ J : BlueLabel,
                  blueSupport branch J =
                    (TwoBiteStagedOpenPairs ω ε I).filter
                      (fun e =>
                        TwoBiteEdgeCoordinateValue ω e ∧
                          match e with
                          | Sum.inl _ => False
                          | Sum.inr _ => True) ∧
                  (blueSupport branch J).card = uB ∧
                  blueSupport branch J ⊆ terminal ∧
                  ∀ e,
                    e ∈ blueSupport branch J →
                      match e with
                      | Sum.inl _ => False
                      | Sum.inr _ => True := by
-- BODY
  classical
  intro n m k uB p ε ε1 ε2 I hist target recorded terminal
    hDecRed hDecBlue hGlobal hTargetHist hTargetRegular hTargetIndep
    hBlueCount
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
  rcases hGlobal with ⟨NB0, hNB0_bound, hBranchPackage⟩
  let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
  let EBof : TwoBiteSample n m p → Finset Coord := fun branch =>
    if h : hist branch then Classical.choose (hBranchPackage branch h) else ∅
  have hEBof_spec :
      ∀ branch (hbranch : hist branch),
        EBof branch ⊆ terminal ∧
        ((EBof branch).card : ℝ) ≤ (NB0 : ℝ) ∧
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
              | Sum.inl _ =>
                  (TwoBiteEdgeCoordinateValue ω e ↔
                    TwoBiteEdgeCoordinateValue branch e)
              | Sum.inr _ => True) →
          TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
            ∀ e,
              e ∈ TwoBiteStagedOpenPairs ω ε I →
              TwoBiteEdgeCoordinateValue ω e →
              (match e with
              | Sum.inl _ => False
              | Sum.inr _ => True) →
              (TwoBiteFinalGraph ω).2.2.IsIndepSet
                (↑I : Set (Fin n)) →
              e ∈ EBof branch := by
    intro branch hbranch
    simpa [EBof, hbranch] using
      Classical.choose_spec (hBranchPackage branch hbranch)
  let embOf :
      (branch : TwoBiteSample n m p) →
        ({e // e ∈ EBof branch} ↪ Fin NB0) := fun branch =>
    Classical.choice <|
      Function.Embedding.nonempty_of_card_le
        (α := {e // e ∈ EBof branch}) (β := Fin NB0) (by
          by_cases hbranch : hist branch
          · have hcardReal : ((EBof branch).card : ℝ) ≤ (NB0 : ℝ) :=
              (hEBof_spec branch hbranch).2.1
            have hcardNat : (EBof branch).card ≤ NB0 := by
              exact_mod_cast hcardReal
            simpa using hcardNat
          · have hEmpty : EBof branch = ∅ := by
              simp [EBof, hbranch]
            simp [hEmpty])
  let BlueLabel :=
    {J : Finset (Fin NB0) //
      J ∈ (Finset.univ : Finset (Fin NB0)).powersetCard uB}
  letI : Fintype BlueLabel := by
    infer_instance
  let blueSupport :
      TwoBiteSample n m p → BlueLabel → Finset Coord := fun branch J =>
    (EBof branch).filter
      (fun e => ∃ h : e ∈ EBof branch, embOf branch ⟨e, h⟩ ∈ J.1)
  refine ⟨NB0, hNB0_bound, BlueLabel, inferInstance, ?_, blueSupport, ?_⟩
  · have hCardEq : Fintype.card BlueLabel = Nat.choose NB0 uB := by
      dsimp [BlueLabel]
      rw [Fintype.card_subtype]
      rw [show
          (Finset.univ.filter
              (fun J : Finset (Fin NB0) =>
                J ∈ (Finset.univ : Finset (Fin NB0)).powersetCard uB)) =
            (Finset.univ : Finset (Fin NB0)).powersetCard uB by
        ext J
        simp]
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    exact le_of_eq hCardEq
  · intro branch ω hω hbranch hSameEmbedding hRecordedCompat
      hTerminalRedCompat
    let Bω : Finset Coord :=
      (TwoBiteStagedOpenPairs ω ε I).filter
        (fun e =>
          TwoBiteEdgeCoordinateValue ω e ∧
            match e with
            | Sum.inl _ => False
            | Sum.inr _ => True)
    have hBω_eq :
        Bω =
          (TwoBiteStagedOpenPairs ω ε I).filter
            (fun e =>
              TwoBiteEdgeCoordinateValue ω e ∧
                match e with
                | Sum.inl _ => False
                | Sum.inr _ => True) := by
      ext e
      constructor
      · intro he
        simpa [Bω] using he
      · intro he
        simpa [Bω] using he
    have hωHist : hist ω := hTargetHist ω hω
    have hEBspec := hEBof_spec branch hbranch
    have hBω_subset_EB : Bω ⊆ EBof branch := by
      intro e he
      have hStage : e ∈ TwoBiteStagedOpenPairs ω ε I :=
        (Finset.mem_filter.mp he).1
      have hPresent : TwoBiteEdgeCoordinateValue ω e :=
        (Finset.mem_filter.mp he).2.1
      cases e with
      | inl q =>
          exact False.elim (Finset.mem_filter.mp he).2.2
      | inr q =>
          exact
            hEBspec.2.2 ω hωHist hSameEmbedding hRecordedCompat
              hTerminalRedCompat (hTargetRegular ω hω) (Sum.inr q)
              hStage hPresent trivial (hTargetIndep ω hω)
    let Jset : Finset (Fin NB0) :=
      Bω.attach.image
        (fun e : {e // e ∈ Bω} =>
          embOf branch ⟨e.1, hBω_subset_EB e.2⟩)
    have hJset_card : Jset.card = uB := by
      have hinj :
          Function.Injective
            (fun e : {e // e ∈ Bω} =>
              embOf branch ⟨e.1, hBω_subset_EB e.2⟩) := by
        intro a b hab
        apply Subtype.ext
        have hsub :
            (⟨a.1, hBω_subset_EB a.2⟩ :
                {e // e ∈ EBof branch}) =
              ⟨b.1, hBω_subset_EB b.2⟩ :=
          (embOf branch).injective hab
        exact congrArg (fun z : {e // e ∈ EBof branch} => z.1) hsub
      calc
        Jset.card = Bω.attach.card := by
          dsimp [Jset]
          rw [Finset.card_image_of_injective _ hinj]
        _ = Bω.card := by simp
        _ = uB := by
          rw [hBω_eq]
          exact hBlueCount ω hω
    have hJset_mem :
        Jset ∈ (Finset.univ : Finset (Fin NB0)).powersetCard uB := by
      exact Finset.mem_powersetCard.mpr
        ⟨by intro x hx; simp, hJset_card⟩
    let J : BlueLabel := ⟨Jset, hJset_mem⟩
    have hSupport_eq : blueSupport branch J = Bω := by
      ext e
      constructor
      · intro he
        have heFilter :
            e ∈ (EBof branch).filter
              (fun e =>
                ∃ h : e ∈ EBof branch,
                  embOf branch ⟨e, h⟩ ∈ J.1) := by
          simpa [blueSupport] using he
        rcases (Finset.mem_filter.mp heFilter).2 with ⟨heEB, heJ⟩
        have heJ' : embOf branch ⟨e, heEB⟩ ∈ Jset := by
          simpa [J] using heJ
        rcases Finset.mem_image.mp heJ' with ⟨a, _ha, haeq⟩
        have hsub :
            (⟨a.1, hBω_subset_EB a.2⟩ :
                {e // e ∈ EBof branch}) =
              ⟨e, heEB⟩ :=
          (embOf branch).injective haeq
        have hae : a.1 = e :=
          congrArg (fun z : {e // e ∈ EBof branch} => z.1) hsub
        simpa [hae] using a.2
      · intro heB
        have heEB : e ∈ EBof branch := hBω_subset_EB heB
        have heFilter :
            e ∈ (EBof branch).filter
              (fun e =>
                ∃ h : e ∈ EBof branch,
                  embOf branch ⟨e, h⟩ ∈ J.1) := by
          refine Finset.mem_filter.mpr ⟨heEB, ?_⟩
          refine ⟨heEB, ?_⟩
          have hmemJset : embOf branch ⟨e, heEB⟩ ∈ Jset := by
            dsimp [Jset]
            exact Finset.mem_image.mpr ⟨⟨e, heB⟩, by simp, rfl⟩
          simpa [J] using hmemJset
        simpa [blueSupport] using heFilter
    refine ⟨J, ?_, ?_, ?_, ?_⟩
    · exact hSupport_eq.trans hBω_eq
    · rw [hSupport_eq]
      rw [hBω_eq]
      exact hBlueCount ω hω
    · rw [hSupport_eq]
      exact fun e he => hEBspec.1 (hBω_subset_EB he)
    · intro e he
      rw [hSupport_eq] at he
      exact (Finset.mem_filter.mp he).2.2
