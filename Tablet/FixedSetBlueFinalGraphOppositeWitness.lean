import Tablet.FinPairRankThirdLessOfLatest
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBiteStagedOpenPairs
import Tablet.TwoBiteFinalPairs
import Tablet.TwoBiteProjectionPairSameColorClosed
import Tablet.TwoBiteX
import Tablet.TwoBiteXPlus

-- [TABLET NODE: FixedSetBlueFinalGraphOppositeWitness]

theorem FixedSetBlueFinalGraphOppositeWitness
    {n m : ℕ} {p ε : ℝ} (ω : TwoBiteSample n m p)
    (I : Finset (Fin n)) (q : Fin m × Fin m) :
    Sum.inr q ∈ TwoBiteStagedOpenPairs ω ε I →
    (TwoBiteBlueGraph ω).Adj q.1 q.2 →
    (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) →
    ∃ r : Fin m,
      q ∈
        TwoBiteBasePairs
          ((TwoBiteX ω I (Sum.inl r)).image
            (TwoBiteBlueProjection ω)) := by
-- BODY
  classical
  intro heT hpresent hIndep
  have hOpen := heT
  simp [TwoBiteStagedOpenPairs] at hOpen
  have hPairSet : Sum.inr q ∈ TwoBiteProjectionPairSet ω I := hOpen.1
  have hqI : q ∈ TwoBiteBasePairs (I.image (TwoBiteBlueProjection ω)) := by
    have hps := hPairSet
    simp [TwoBiteProjectionPairSet] at hps
    exact hps
  have hProjectedPair_has_final_pair :
      ∀ (proj : Fin n → Fin m) (X : Finset (Fin n)) (q : Fin m × Fin m),
        q ∈ TwoBiteBasePairs (X.image proj) →
          ∃ a : Fin n × Fin n,
            a ∈ TwoBiteFinalPairs X ∧
              ((proj a.1 = q.1 ∧ proj a.2 = q.2) ∨
                (proj a.1 = q.2 ∧ proj a.2 = q.1)) := by
    intro proj X q hq
    simp [TwoBiteBasePairs, TwoBitePairsInSet] at hq
    rcases hq with ⟨⟨hq1, hq2⟩, hqrank⟩
    rcases hq1 with ⟨u, huX, huproj⟩
    rcases hq2 with ⟨v, hvX, hvproj⟩
    have huv_ne : u ≠ v := by
      intro huv
      have hqeq : q.1 = q.2 := by
        calc
          q.1 = proj u := huproj.symm
          _ = proj v := by rw [huv]
          _ = q.2 := hvproj
      rw [hqeq] at hqrank
      exact (lt_irrefl q.2) hqrank
    by_cases huv_rank : u.val < v.val
    · refine ⟨(u, v), ?_, Or.inl ?_⟩
      · simpa [TwoBiteFinalPairs, TwoBitePairsInSet, huX, hvX] using huv_rank
      · exact ⟨huproj, hvproj⟩
    · have hval_ne : u.val ≠ v.val := by
        intro hval
        exact huv_ne (Fin.ext hval)
      have hvu_rank : v.val < u.val := by
        have hle : v.val ≤ u.val := Nat.le_of_not_gt huv_rank
        exact lt_of_le_of_ne hle (Ne.symm hval_ne)
      refine ⟨(v, u), ?_, Or.inr ?_⟩
      · simpa [TwoBiteFinalPairs, TwoBitePairsInSet, hvX, huX] using hvu_rank
      · exact ⟨hvproj, huproj⟩
  rcases hProjectedPair_has_final_pair (TwoBiteBlueProjection ω) I q hqI with
    ⟨a, haFinal, hproj⟩
  have haFinal' := haFinal
  simp [TwoBiteFinalPairs, TwoBitePairsInSet] at haFinal'
  rcases haFinal' with ⟨⟨huI, hvI⟩, huv_rank⟩
  have huv_ne : a.1 ≠ a.2 := by
    intro h
    have : a.1.val = a.2.val := by rw [h]
    omega
  have hOverlayBlue : (TwoBiteOverlay ω).2.Adj a.1 a.2 := by
    dsimp [TwoBiteOverlay]
    refine ⟨huv_ne, ?_⟩
    rcases hproj with hdir | hrev
    · simpa [hdir.1, hdir.2] using hpresent
    · have hpresent' := (TwoBiteBlueGraph ω).symm hpresent
      simpa [hrev.1, hrev.2] using hpresent'
  let pairRank : Fin m → Fin m → ℕ :=
    fun a b => Nat.min a.val b.val * m + Nat.max a.val b.val
  let blueLatest : Fin n → Fin n → Fin n → Prop :=
    fun u v w =>
      pairRank (TwoBiteBlueProjection ω u) (TwoBiteBlueProjection ω w) <
          pairRank (TwoBiteBlueProjection ω u) (TwoBiteBlueProjection ω v) ∧
        pairRank (TwoBiteBlueProjection ω v) (TwoBiteBlueProjection ω w) <
          pairRank (TwoBiteBlueProjection ω u) (TwoBiteBlueProjection ω v)
  let blueDeletedDirected : Fin n → Fin n → Prop :=
    fun u v =>
      (∃ w : Fin n,
        (TwoBiteOverlay ω).2.Adj u v ∧
          (TwoBiteOverlay ω).2.Adj u w ∧
          (TwoBiteOverlay ω).2.Adj v w ∧
          blueLatest u v w) ∨
        (∃ center : Fin n,
          (TwoBiteOverlay ω).1.Adj center u ∧
            (TwoBiteOverlay ω).1.Adj center v ∧
            (TwoBiteOverlay ω).2.Adj u v)
  let blueDeleted : Fin n → Fin n → Prop :=
    fun u v => blueDeletedDirected u v ∨ blueDeletedDirected v u
  have hDeleted : blueDeleted a.1 a.2 := by
    by_contra hNotDeleted
    have hShadow : (TwoBiteFinalGraph ω).2.2.Adj a.1 a.2 := by
      unfold TwoBiteFinalGraph
      dsimp only
      rw [SimpleGraph.fromRel_adj]
      refine ⟨huv_ne, Or.inl ?_⟩
      right
      rw [SimpleGraph.fromRel_adj]
      refine ⟨huv_ne, Or.inl ?_⟩
      exact ⟨hOverlayBlue, by
        simpa [pairRank, blueLatest, blueDeletedDirected, blueDeleted] using hNotDeleted⟩
    exact hIndep huI hvI huv_ne hShadow
  have hqrank : q.1.val < q.2.val := by
    have hqI' := hqI
    simp [TwoBiteBasePairs, TwoBitePairsInSet] at hqI'
    exact hqI'.2
  have hPairOfEndpoints :
      ∀ {X : Finset (Fin n)}, a.1 ∈ X → a.2 ∈ X →
        q ∈ TwoBiteBasePairs (X.image (TwoBiteBlueProjection ω)) := by
    intro X ha1X ha2X
    simp [TwoBiteBasePairs, TwoBitePairsInSet]
    rcases hproj with hdir | hrev
    · exact ⟨⟨⟨a.1, ha1X, hdir.1⟩, ⟨a.2, ha2X, hdir.2⟩⟩, hqrank⟩
    · exact ⟨⟨⟨a.2, ha2X, hrev.2⟩, ⟨a.1, ha1X, hrev.1⟩⟩, hqrank⟩
  have hBlueProj_ne : TwoBiteBlueProjection ω a.1 ≠ TwoBiteBlueProjection ω a.2 := by
    intro hEq
    rcases hproj with hdir | hrev
    · have hqeq : q.1 = q.2 := by
        calc
          q.1 = TwoBiteBlueProjection ω a.1 := hdir.1.symm
          _ = TwoBiteBlueProjection ω a.2 := hEq
          _ = q.2 := hdir.2
      simp [hqeq] at hqrank
    · have hqeq : q.2 = q.1 := by
        calc
          q.2 = TwoBiteBlueProjection ω a.1 := hrev.1.symm
          _ = TwoBiteBlueProjection ω a.2 := hEq
          _ = q.1 := hrev.2
      simp [hqeq] at hqrank
  have hMixedWitness :
      (∃ center : Fin n,
          (TwoBiteOverlay ω).1.Adj center a.1 ∧
            (TwoBiteOverlay ω).1.Adj center a.2 ∧
            (TwoBiteOverlay ω).2.Adj a.1 a.2) →
        ∃ r : Fin m,
          q ∈ TwoBiteBasePairs
            ((TwoBiteX ω I (Sum.inl r)).image (TwoBiteBlueProjection ω)) := by
    rintro ⟨center, hc1, hc2, _⟩
    let r : Fin m := TwoBiteRedProjection ω center
    have hRed1 : (TwoBiteRedGraph ω).Adj r (TwoBiteRedProjection ω a.1) := by
      have h := hc1
      dsimp [TwoBiteOverlay, r] at h
      exact h.2
    have hRed2 : (TwoBiteRedGraph ω).Adj r (TwoBiteRedProjection ω a.2) := by
      have h := hc2
      dsimp [TwoBiteOverlay, r] at h
      exact h.2
    have ha1X : a.1 ∈ TwoBiteX ω I (Sum.inl r) := by
      simp [TwoBiteX, TwoBiteLiftedNeighborhood, r, huI, hRed1]
    have ha2X : a.2 ∈ TwoBiteX ω I (Sum.inl r) := by
      simp [TwoBiteX, TwoBiteLiftedNeighborhood, r, hvI, hRed2]
    exact ⟨r, hPairOfEndpoints ha1X ha2X⟩
  have hSameContradiction :
      (∃ w : Fin n,
          (TwoBiteOverlay ω).2.Adj a.1 a.2 ∧
            (TwoBiteOverlay ω).2.Adj a.1 w ∧
            (TwoBiteOverlay ω).2.Adj a.2 w ∧
            blueLatest a.1 a.2 w) →
        False := by
    rintro ⟨w, _, h1w, h2w, hlatest⟩
    let b : Fin m := TwoBiteBlueProjection ω w
    have hlt :=
      FinPairRankThirdLessOfLatest
        (x := TwoBiteBlueProjection ω a.1)
        (y := TwoBiteBlueProjection ω a.2)
        (z := b) hBlueProj_ne hlatest.1 hlatest.2
    have hBlue1 : (TwoBiteBlueGraph ω).Adj b (TwoBiteBlueProjection ω a.1) := by
      have h := ((TwoBiteOverlay ω).2).symm h1w
      dsimp [TwoBiteOverlay, b] at h
      exact h.2
    have hBlue2 : (TwoBiteBlueGraph ω).Adj b (TwoBiteBlueProjection ω a.2) := by
      have h := ((TwoBiteOverlay ω).2).symm h2w
      dsimp [TwoBiteOverlay, b] at h
      exact h.2
    have ha1X : a.1 ∈ TwoBiteXPlus ω I (Sum.inr b) := by
      simp [TwoBiteXPlus, TwoBiteLiftedPositiveNeighborhood, b, huI, hBlue1]
      exact hlt.1
    have ha2X : a.2 ∈ TwoBiteXPlus ω I (Sum.inr b) := by
      simp [TwoBiteXPlus, TwoBiteLiftedPositiveNeighborhood, b, hvI, hBlue2]
      exact hlt.2
    have hClosed : TwoBiteProjectionPairSameColorClosed ω I (Sum.inr q) := by
      exact ⟨b, hPairOfEndpoints ha1X ha2X⟩
    exact hOpen.2.1 hClosed
  have hSameContradiction_rev :
      (∃ w : Fin n,
          (TwoBiteOverlay ω).2.Adj a.2 a.1 ∧
            (TwoBiteOverlay ω).2.Adj a.2 w ∧
            (TwoBiteOverlay ω).2.Adj a.1 w ∧
            blueLatest a.2 a.1 w) →
        False := by
    rintro ⟨w, _, h2w, h1w, hlatest⟩
    let b : Fin m := TwoBiteBlueProjection ω w
    have hlt :=
      FinPairRankThirdLessOfLatest
        (x := TwoBiteBlueProjection ω a.2)
        (y := TwoBiteBlueProjection ω a.1)
        (z := b) (Ne.symm hBlueProj_ne) hlatest.1 hlatest.2
    have hBlue1 : (TwoBiteBlueGraph ω).Adj b (TwoBiteBlueProjection ω a.1) := by
      have h := ((TwoBiteOverlay ω).2).symm h1w
      dsimp [TwoBiteOverlay, b] at h
      exact h.2
    have hBlue2 : (TwoBiteBlueGraph ω).Adj b (TwoBiteBlueProjection ω a.2) := by
      have h := ((TwoBiteOverlay ω).2).symm h2w
      dsimp [TwoBiteOverlay, b] at h
      exact h.2
    have ha1X : a.1 ∈ TwoBiteXPlus ω I (Sum.inr b) := by
      simp [TwoBiteXPlus, TwoBiteLiftedPositiveNeighborhood, b, huI, hBlue1]
      exact hlt.2
    have ha2X : a.2 ∈ TwoBiteXPlus ω I (Sum.inr b) := by
      simp [TwoBiteXPlus, TwoBiteLiftedPositiveNeighborhood, b, hvI, hBlue2]
      exact hlt.1
    have hClosed : TwoBiteProjectionPairSameColorClosed ω I (Sum.inr q) := by
      exact ⟨b, hPairOfEndpoints ha1X ha2X⟩
    exact hOpen.2.1 hClosed
  rcases hDeleted with hdir | hrev
  · rcases hdir with hsame | hmixed
    · exact False.elim (hSameContradiction hsame)
    · exact hMixedWitness hmixed
  · rcases hrev with hsame | hmixed
    · exact False.elim (hSameContradiction_rev hsame)
    · rcases hmixed with ⟨center, hc2, hc1, hblue21⟩
      exact hMixedWitness ⟨center, hc1, hc2, ((TwoBiteOverlay ω).2).symm hblue21⟩
