import Tablet.FinPairRankThirdLessOfLatest
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBiteStagedOpenPairs
import Tablet.TwoBiteFinalPairs
import Tablet.TwoBiteProjectionPairSameColorClosed
import Tablet.TwoBiteX
import Tablet.TwoBiteXPlus

-- [TABLET NODE: FixedSetRedFinalGraphOppositeWitness]

theorem FixedSetRedFinalGraphOppositeWitness
    {n m : ℕ} {p ε : ℝ} (ω : TwoBiteSample n m p)
    (I : Finset (Fin n)) (q : Fin m × Fin m) :
    Sum.inl q ∈ TwoBiteStagedOpenPairs ω ε I →
    (TwoBiteRedGraph ω).Adj q.1 q.2 →
    (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) →
    ∃ b : Fin m,
      q ∈
        TwoBiteBasePairs
          ((TwoBiteX ω I (Sum.inr b)).image
            (TwoBiteRedProjection ω)) := by
-- BODY
  classical
  intro heT hpresent hIndep
  have hOpen := heT
  simp [TwoBiteStagedOpenPairs] at hOpen
  have hPairSet : Sum.inl q ∈ TwoBiteProjectionPairSet ω I := hOpen.1
  have hqI : q ∈ TwoBiteBasePairs (I.image (TwoBiteRedProjection ω)) := by
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
  rcases hProjectedPair_has_final_pair (TwoBiteRedProjection ω) I q hqI with
    ⟨a, haFinal, hproj⟩
  have haFinal' := haFinal
  simp [TwoBiteFinalPairs, TwoBitePairsInSet] at haFinal'
  rcases haFinal' with ⟨⟨huI, hvI⟩, huv_rank⟩
  have huv_ne : a.1 ≠ a.2 := by
    intro h
    have : a.1.val = a.2.val := by rw [h]
    omega
  have hOverlayRed : (TwoBiteOverlay ω).1.Adj a.1 a.2 := by
    dsimp [TwoBiteOverlay]
    refine ⟨huv_ne, ?_⟩
    rcases hproj with hdir | hrev
    · simpa [hdir.1, hdir.2] using hpresent
    · have hpresent' := (TwoBiteRedGraph ω).symm hpresent
      simpa [hrev.1, hrev.2] using hpresent'
  let pairRank : Fin m → Fin m → ℕ :=
    fun a b => Nat.min a.val b.val * m + Nat.max a.val b.val
  let redLatest : Fin n → Fin n → Fin n → Prop :=
    fun u v w =>
      pairRank (TwoBiteRedProjection ω u) (TwoBiteRedProjection ω w) <
          pairRank (TwoBiteRedProjection ω u) (TwoBiteRedProjection ω v) ∧
        pairRank (TwoBiteRedProjection ω v) (TwoBiteRedProjection ω w) <
          pairRank (TwoBiteRedProjection ω u) (TwoBiteRedProjection ω v)
  let redDeletedDirected : Fin n → Fin n → Prop :=
    fun u v =>
      (∃ w : Fin n,
        (TwoBiteOverlay ω).1.Adj u v ∧
          (TwoBiteOverlay ω).1.Adj u w ∧
          (TwoBiteOverlay ω).1.Adj v w ∧
          redLatest u v w) ∨
        (∃ center : Fin n,
          (TwoBiteOverlay ω).2.Adj center u ∧
            (TwoBiteOverlay ω).2.Adj center v ∧
            (TwoBiteOverlay ω).1.Adj u v)
  let redDeleted : Fin n → Fin n → Prop :=
    fun u v => redDeletedDirected u v ∨ redDeletedDirected v u
  have hDeleted : redDeleted a.1 a.2 := by
    by_contra hNotDeleted
    have hShadow : (TwoBiteFinalGraph ω).2.2.Adj a.1 a.2 := by
      unfold TwoBiteFinalGraph
      dsimp only
      rw [SimpleGraph.fromRel_adj]
      refine ⟨huv_ne, Or.inl ?_⟩
      left
      rw [SimpleGraph.fromRel_adj]
      refine ⟨huv_ne, Or.inl ?_⟩
      exact ⟨hOverlayRed, by
        simpa [pairRank, redLatest, redDeletedDirected, redDeleted] using hNotDeleted⟩
    exact hIndep huI hvI huv_ne hShadow
  have hqrank : q.1.val < q.2.val := by
    have hqI' := hqI
    simp [TwoBiteBasePairs, TwoBitePairsInSet] at hqI'
    exact hqI'.2
  have hPairOfEndpoints :
      ∀ {X : Finset (Fin n)}, a.1 ∈ X → a.2 ∈ X →
        q ∈ TwoBiteBasePairs (X.image (TwoBiteRedProjection ω)) := by
    intro X ha1X ha2X
    simp [TwoBiteBasePairs, TwoBitePairsInSet]
    rcases hproj with hdir | hrev
    · exact ⟨⟨⟨a.1, ha1X, hdir.1⟩, ⟨a.2, ha2X, hdir.2⟩⟩, hqrank⟩
    · exact ⟨⟨⟨a.2, ha2X, hrev.2⟩, ⟨a.1, ha1X, hrev.1⟩⟩, hqrank⟩
  have hRedProj_ne : TwoBiteRedProjection ω a.1 ≠ TwoBiteRedProjection ω a.2 := by
    intro hEq
    rcases hproj with hdir | hrev
    · have hqeq : q.1 = q.2 := by
        calc
          q.1 = TwoBiteRedProjection ω a.1 := hdir.1.symm
          _ = TwoBiteRedProjection ω a.2 := hEq
          _ = q.2 := hdir.2
      simp [hqeq] at hqrank
    · have hqeq : q.2 = q.1 := by
        calc
          q.2 = TwoBiteRedProjection ω a.1 := hrev.1.symm
          _ = TwoBiteRedProjection ω a.2 := hEq
          _ = q.1 := hrev.2
      simp [hqeq] at hqrank
  have hMixedWitness :
      (∃ center : Fin n,
          (TwoBiteOverlay ω).2.Adj center a.1 ∧
            (TwoBiteOverlay ω).2.Adj center a.2 ∧
            (TwoBiteOverlay ω).1.Adj a.1 a.2) →
        ∃ b : Fin m,
          q ∈ TwoBiteBasePairs
            ((TwoBiteX ω I (Sum.inr b)).image (TwoBiteRedProjection ω)) := by
    rintro ⟨center, hc1, hc2, _⟩
    let b : Fin m := TwoBiteBlueProjection ω center
    have hBlue1 : (TwoBiteBlueGraph ω).Adj b (TwoBiteBlueProjection ω a.1) := by
      have h := hc1
      dsimp [TwoBiteOverlay, b] at h
      exact h.2
    have hBlue2 : (TwoBiteBlueGraph ω).Adj b (TwoBiteBlueProjection ω a.2) := by
      have h := hc2
      dsimp [TwoBiteOverlay, b] at h
      exact h.2
    have ha1X : a.1 ∈ TwoBiteX ω I (Sum.inr b) := by
      simp [TwoBiteX, TwoBiteLiftedNeighborhood, b, huI, hBlue1]
    have ha2X : a.2 ∈ TwoBiteX ω I (Sum.inr b) := by
      simp [TwoBiteX, TwoBiteLiftedNeighborhood, b, hvI, hBlue2]
    exact ⟨b, hPairOfEndpoints ha1X ha2X⟩
  have hSameContradiction :
      (∃ w : Fin n,
          (TwoBiteOverlay ω).1.Adj a.1 a.2 ∧
            (TwoBiteOverlay ω).1.Adj a.1 w ∧
            (TwoBiteOverlay ω).1.Adj a.2 w ∧
            redLatest a.1 a.2 w) →
        False := by
    rintro ⟨w, _, h1w, h2w, hlatest⟩
    let r : Fin m := TwoBiteRedProjection ω w
    have hlt :=
      FinPairRankThirdLessOfLatest
        (x := TwoBiteRedProjection ω a.1)
        (y := TwoBiteRedProjection ω a.2)
        (z := r) hRedProj_ne hlatest.1 hlatest.2
    have hRed1 : (TwoBiteRedGraph ω).Adj r (TwoBiteRedProjection ω a.1) := by
      have h := ((TwoBiteOverlay ω).1).symm h1w
      dsimp [TwoBiteOverlay, r] at h
      exact h.2
    have hRed2 : (TwoBiteRedGraph ω).Adj r (TwoBiteRedProjection ω a.2) := by
      have h := ((TwoBiteOverlay ω).1).symm h2w
      dsimp [TwoBiteOverlay, r] at h
      exact h.2
    have ha1X : a.1 ∈ TwoBiteXPlus ω I (Sum.inl r) := by
      simp [TwoBiteXPlus, TwoBiteLiftedPositiveNeighborhood, r, huI, hRed1]
      exact hlt.1
    have ha2X : a.2 ∈ TwoBiteXPlus ω I (Sum.inl r) := by
      simp [TwoBiteXPlus, TwoBiteLiftedPositiveNeighborhood, r, hvI, hRed2]
      exact hlt.2
    have hClosed : TwoBiteProjectionPairSameColorClosed ω I (Sum.inl q) := by
      exact ⟨r, hPairOfEndpoints ha1X ha2X⟩
    exact hOpen.2.1 hClosed
  have hSameContradiction_rev :
      (∃ w : Fin n,
          (TwoBiteOverlay ω).1.Adj a.2 a.1 ∧
            (TwoBiteOverlay ω).1.Adj a.2 w ∧
            (TwoBiteOverlay ω).1.Adj a.1 w ∧
            redLatest a.2 a.1 w) →
        False := by
    rintro ⟨w, _, h2w, h1w, hlatest⟩
    let r : Fin m := TwoBiteRedProjection ω w
    have hlt :=
      FinPairRankThirdLessOfLatest
        (x := TwoBiteRedProjection ω a.2)
        (y := TwoBiteRedProjection ω a.1)
        (z := r) (Ne.symm hRedProj_ne) hlatest.1 hlatest.2
    have hRed1 : (TwoBiteRedGraph ω).Adj r (TwoBiteRedProjection ω a.1) := by
      have h := ((TwoBiteOverlay ω).1).symm h1w
      dsimp [TwoBiteOverlay, r] at h
      exact h.2
    have hRed2 : (TwoBiteRedGraph ω).Adj r (TwoBiteRedProjection ω a.2) := by
      have h := ((TwoBiteOverlay ω).1).symm h2w
      dsimp [TwoBiteOverlay, r] at h
      exact h.2
    have ha1X : a.1 ∈ TwoBiteXPlus ω I (Sum.inl r) := by
      simp [TwoBiteXPlus, TwoBiteLiftedPositiveNeighborhood, r, huI, hRed1]
      exact hlt.2
    have ha2X : a.2 ∈ TwoBiteXPlus ω I (Sum.inl r) := by
      simp [TwoBiteXPlus, TwoBiteLiftedPositiveNeighborhood, r, hvI, hRed2]
      exact hlt.1
    have hClosed : TwoBiteProjectionPairSameColorClosed ω I (Sum.inl q) := by
      exact ⟨r, hPairOfEndpoints ha1X ha2X⟩
    exact hOpen.2.1 hClosed
  rcases hDeleted with hdir | hrev
  · rcases hdir with hsame | hmixed
    · exact False.elim (hSameContradiction hsame)
    · exact hMixedWitness hmixed
  · rcases hrev with hsame | hmixed
    · exact False.elim (hSameContradiction_rev hsame)
    · rcases hmixed with ⟨center, hc2, hc1, hred21⟩
      exact hMixedWitness ⟨center, hc1, hc2, ((TwoBiteOverlay ω).1).symm hred21⟩
