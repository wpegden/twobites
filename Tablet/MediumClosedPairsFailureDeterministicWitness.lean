import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Tablet.FinalPairsCardLeHalfSq
import Tablet.FiberAndDegreeEvent
import Tablet.MediumClosedPairsDeterministicReduction
import Tablet.NormalizePairImageCardBound
import Tablet.ProjectionFiberCardBound
import Tablet.TwoBiteClosedPairsInClass
import Tablet.TwoBiteMediumClosedPairsEvent
import Tablet.TwoBiteMediumClass
import Tablet.TwoBiteRedGraph
import Tablet.TwoBiteBlueGraph
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection

-- [TABLET NODE: MediumClosedPairsFailureDeterministicWitness]

open scoped BigOperators

theorem MediumClosedPairsFailureDeterministicWitness {n m k : ℕ} {p : ℝ}
    (ε ε1 ε2 : ℝ) (ω : TwoBiteSample n m p)
    (hRegular : FiberAndDegreeEvent ω ε2)
    (hBad : ¬ TwoBiteMediumClosedPairsEvent (k := k) ε ε1 ω)
    (hA_nonneg :
      0 ≤ (k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε))
    (hLargeCutoff_pos : 0 < TwoBiteLargeCutoff ε n)
    (hScale :
      TwoBiteLargeCutoff ε n *
          ((k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε))
        ≤ ε1 * (k : ℝ) ^ 2)
    (hChargeFactor :
      (1 + ε2) * (Real.log (n : ℝ)) ^ 2
        ≤ 3 * (Real.log (n : ℝ)) ^ 2)
    (hL_pos : 0 < 3 * (Real.log (n : ℝ)) ^ 2) :
    ∃ I : Finset (Fin n),
      I.card = k ∧
      ¬ ClosedPairsBound
        ((TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I)).card : ℝ)
        ε1 (k : ℝ) ∧
      ∃ B : Finset (TwoBiteBaseVertex m),
        let A0 := (k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε)
        B.Nonempty ∧
        (∀ x ∈ B, TwoBiteMediumClass ω ε I x) ∧
        A0 < (∑ x ∈ B, ((TwoBiteX ω I x).card : ℝ)) ∧
        (∑ x ∈ B, ((TwoBiteX ω I x).card : ℝ))
          ≤ A0 + TwoBiteLargeCutoff ε n ∧
        (B.card : ℝ) * TwoBiteSmallCutoff ε n
          ≤ A0 + TwoBiteLargeCutoff ε n ∧
        (let redCenters : Finset (Fin m) :=
            Finset.univ.filter (fun r : Fin m => Sum.inl r ∈ B)
         let blueCenters : Finset (Fin m) :=
            Finset.univ.filter (fun b : Fin m => Sum.inr b ∈ B)
         let redProjection : Finset (Fin m) := I.image (TwoBiteRedProjection ω)
         let blueProjection : Finset (Fin m) := I.image (TwoBiteBlueProjection ω)
         let normalize : Fin m × Fin m → Fin m × Fin m :=
            fun e => if e.1.val < e.2.val then e else (e.2, e.1)
         let redOrdered : Finset (Fin m × Fin m) :=
            @Finset.filter (Fin m × Fin m)
              (fun e => (TwoBiteRedGraph ω).Adj e.1 e.2)
              (Classical.decPred _)
              (redCenters.product redProjection)
         let blueOrdered : Finset (Fin m × Fin m) :=
            @Finset.filter (Fin m × Fin m)
              (fun e => (TwoBiteBlueGraph ω).Adj e.1 e.2)
              (Classical.decPred _)
              (blueCenters.product blueProjection)
         let redEdges : Finset (Fin m × Fin m) := redOrdered.image normalize
         let blueEdges : Finset (Fin m × Fin m) := blueOrdered.image normalize
        A0 / (6 * (Real.log (n : ℝ)) ^ 2) <
         ((redEdges.card + blueEdges.card : ℕ) : ℝ)) := by
-- BODY
  classical
  rw [TwoBiteMediumClosedPairsEvent] at hBad
  push Not at hBad
  rcases hBad with ⟨I, hIcard, hIbad⟩
  let A0 : ℝ := (k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε)
  let M : Finset (TwoBiteBaseVertex m) :=
    (Finset.univ : Finset (TwoBiteBaseVertex m)).filter
      (fun x => TwoBiteMediumClass ω ε I x)
  let w : TwoBiteBaseVertex m → ℕ := fun x => (TwoBiteX ω I x).card
  let L : ℝ := 3 * (Real.log (n : ℝ)) ^ 2
  let t2 : ℝ := TwoBiteLargeCutoff ε n
  let lower : ℝ := TwoBiteSmallCutoff ε n
  let redCentersOf (B : Finset (TwoBiteBaseVertex m)) : Finset (Fin m) :=
    Finset.univ.filter (fun r : Fin m => Sum.inl r ∈ B)
  let blueCentersOf (B : Finset (TwoBiteBaseVertex m)) : Finset (Fin m) :=
    Finset.univ.filter (fun b : Fin m => Sum.inr b ∈ B)
  let redProjection : Finset (Fin m) := I.image (TwoBiteRedProjection ω)
  let blueProjection : Finset (Fin m) := I.image (TwoBiteBlueProjection ω)
  let redOrderedOf (B : Finset (TwoBiteBaseVertex m)) : Finset (Fin m × Fin m) :=
    @Finset.filter (Fin m × Fin m)
      (fun e => (TwoBiteRedGraph ω).Adj e.1 e.2)
      (Classical.decPred _)
      ((redCentersOf B).product redProjection)
  let blueOrderedOf (B : Finset (TwoBiteBaseVertex m)) : Finset (Fin m × Fin m) :=
    @Finset.filter (Fin m × Fin m)
      (fun e => (TwoBiteBlueGraph ω).Adj e.1 e.2)
      (Classical.decPred _)
      ((blueCentersOf B).product blueProjection)
  let edgeCount : Finset (TwoBiteBaseVertex m) → ℕ :=
    fun B => (redOrderedOf B).card + (blueOrderedOf B).card
  have hlarge : A0 < ∑ x ∈ M, (w x : ℝ) := by
    have hClosed_gt :
        ε1 * (k : ℝ) ^ 2 <
          ((TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I)).card : ℝ) := by
      unfold ClosedPairsBound at hIbad
      exact not_le.mp hIbad
    have hClosed_eq :
        TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I) =
          M.biUnion (fun x => TwoBiteFinalPairs (TwoBiteX ω I x)) := by
      rfl
    have hClosed_card_le_sum :
        ((TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I)).card : ℝ) ≤
          ∑ x ∈ M, ((TwoBiteFinalPairs (TwoBiteX ω I x)).card : ℝ) := by
      rw [hClosed_eq]
      exact_mod_cast
        (Finset.card_biUnion_le
          (s := M) (t := fun x => TwoBiteFinalPairs (TwoBiteX ω I x)))
    have hPair_le :
        ∀ x ∈ M,
          ((TwoBiteFinalPairs (TwoBiteX ω I x)).card : ℝ) ≤
            t2 * ((TwoBiteX ω I x).card : ℝ) := by
      intro x hx
      have hxmed : TwoBiteMediumClass ω ε I x := by
        simpa [M] using hx
      set c : ℝ := ((TwoBiteX ω I x).card : ℝ) with hc
      have hc_nonneg : 0 ≤ c := by
        rw [hc]
        exact_mod_cast Nat.zero_le (TwoBiteX ω I x).card
      have hc_le_t2 : c ≤ t2 := by
        simpa [c, t2, hc] using hxmed.2
      have ht2_nonneg : 0 ≤ t2 := le_of_lt hLargeCutoff_pos
      have hhalf : ((TwoBiteFinalPairs (TwoBiteX ω I x)).card : ℝ) ≤ c ^ 2 / 2 := by
        simpa [c, hc] using FinalPairsCardLeHalfSq (TwoBiteX ω I x)
      have hsq_le : c ^ 2 ≤ t2 * c := by
        calc
          c ^ 2 = c * c := by ring
          _ ≤ t2 * c := mul_le_mul_of_nonneg_right hc_le_t2 hc_nonneg
      have htarget_nonneg : 0 ≤ t2 * c := mul_nonneg ht2_nonneg hc_nonneg
      calc
        ((TwoBiteFinalPairs (TwoBiteX ω I x)).card : ℝ) ≤ c ^ 2 / 2 := hhalf
        _ ≤ (t2 * c) / 2 := by linarith
        _ ≤ t2 * c := by linarith
        _ = t2 * ((TwoBiteX ω I x).card : ℝ) := by rw [hc]
    have hPairs_sum_le :
        (∑ x ∈ M, ((TwoBiteFinalPairs (TwoBiteX ω I x)).card : ℝ)) ≤
          ∑ x ∈ M, t2 * ((TwoBiteX ω I x).card : ℝ) := by
      exact Finset.sum_le_sum hPair_le
    have hWeighted_eq :
        (∑ x ∈ M, t2 * ((TwoBiteX ω I x).card : ℝ)) =
          t2 * (∑ x ∈ M, (w x : ℝ)) := by
      dsimp [w]
      simpa [mul_assoc] using
        (Finset.mul_sum M
          (fun x => ((TwoBiteX ω I x).card : ℝ)) t2).symm
    have hClosed_le_weighted :
        ((TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I)).card : ℝ) ≤
          t2 * (∑ x ∈ M, (w x : ℝ)) := by
      calc
        ((TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I)).card : ℝ)
            ≤ ∑ x ∈ M, ((TwoBiteFinalPairs (TwoBiteX ω I x)).card : ℝ) :=
              hClosed_card_le_sum
        _ ≤ ∑ x ∈ M, t2 * ((TwoBiteX ω I x).card : ℝ) := hPairs_sum_le
        _ = t2 * (∑ x ∈ M, (w x : ℝ)) := hWeighted_eq
    have hA_t2_lt :
        t2 * A0 < t2 * (∑ x ∈ M, (w x : ℝ)) := by
      calc
        t2 * A0 ≤ ε1 * (k : ℝ) ^ 2 := by
          simpa [t2, A0] using hScale
        _ < ((TwoBiteClosedPairsInClass ω I (TwoBiteMediumClass ω ε I)).card : ℝ) :=
          hClosed_gt
        _ ≤ t2 * (∑ x ∈ M, (w x : ℝ)) := hClosed_le_weighted
    have ht2_pos : 0 < t2 := by
      simpa [t2] using hLargeCutoff_pos
    nlinarith
  have hupper : ∀ x ∈ M, (w x : ℝ) ≤ t2 := by
    intro x hx
    have hxmed : TwoBiteMediumClass ω ε I x := by
      simpa [M] using hx
    exact hxmed.2
  have hlower : ∀ x ∈ M, lower ≤ (w x : ℝ) := by
    intro x hx
    have hxmed : TwoBiteMediumClass ω ε I x := by
      simpa [M] using hx
    exact le_of_lt hxmed.1
  have hcharge :
      ∀ B : Finset (TwoBiteBaseVertex m), B ⊆ M →
        ∑ x ∈ B, (w x : ℝ) ≤ L * (edgeCount B : ℝ) := by
    intro B hBM_sub
    let inc : Finset (Sigma fun _ : TwoBiteBaseVertex m => Fin n) :=
      B.sigma (fun x => TwoBiteX ω I x)
    let encode : (Sigma fun _ : TwoBiteBaseVertex m => Fin n) →
        Sum (Fin m × Fin m) (Fin m × Fin m) :=
      fun z =>
        match z.1 with
        | Sum.inl r => Sum.inl (r, TwoBiteRedProjection ω z.2)
        | Sum.inr b => Sum.inr (b, TwoBiteBlueProjection ω z.2)
    have hRedWithin :
        ∀ r : Fin m,
          WithinRelativeError ε2 ((Real.log (n : ℝ)) ^ 2)
            ((RedFiber ω r).card : ℝ) := by
      simpa [FiberAndDegreeEvent] using hRegular.1
    have hBlueWithin :
        ∀ b : Fin m,
          WithinRelativeError ε2 ((Real.log (n : ℝ)) ^ 2)
            ((BlueFiber ω b).card : ℝ) := by
      simpa [FiberAndDegreeEvent] using hRegular.2.1
    have hRedFiber_le :
        ∀ r : Fin m, ((RedFiber ω r).card : ℝ) ≤ L := by
      intro r
      have hrel := hRedWithin r
      unfold WithinRelativeError at hrel
      have hdiff :
          ((RedFiber ω r).card : ℝ) - (Real.log (n : ℝ)) ^ 2
            ≤ ε2 * (Real.log (n : ℝ)) ^ 2 :=
        le_trans (le_abs_self _) hrel
      have hto_factor :
          ((RedFiber ω r).card : ℝ) ≤
            (1 + ε2) * (Real.log (n : ℝ)) ^ 2 := by
        linarith
      exact le_trans hto_factor (by simpa [L] using hChargeFactor)
    have hBlueFiber_le :
        ∀ b : Fin m, ((BlueFiber ω b).card : ℝ) ≤ L := by
      intro b
      have hrel := hBlueWithin b
      unfold WithinRelativeError at hrel
      have hdiff :
          ((BlueFiber ω b).card : ℝ) - (Real.log (n : ℝ)) ^ 2
            ≤ ε2 * (Real.log (n : ℝ)) ^ 2 :=
        le_trans (le_abs_self _) hrel
      have hto_factor :
          ((BlueFiber ω b).card : ℝ) ≤
            (1 + ε2) * (Real.log (n : ℝ)) ^ 2 := by
        linarith
      exact le_trans hto_factor (by simpa [L] using hChargeFactor)
    have hfiber :
        ∀ y, y ∈ inc.image encode →
          (((inc.filter (fun z => encode z = y)).card : ℝ) ≤ L) := by
      intro y hy
      cases y with
      | inl q =>
          have hcard_le :
              (inc.filter (fun z => encode z = Sum.inl q)).card ≤
                (RedFiber ω q.2).card := by
            refine Finset.card_le_card_of_injOn (fun z => z.2) ?_ ?_
            · intro z hz
              have hzfin : z ∈ inc.filter (fun z => encode z = Sum.inl q) := by
                simpa using hz
              rw [Finset.mem_filter] at hzfin
              have henc : encode z = Sum.inl q := hzfin.2
              rcases z with ⟨x, v⟩
              cases x with
              | inl r =>
                  simp [encode] at henc
                  have hvproj : TwoBiteRedProjection ω v = q.2 :=
                    congrArg (fun e : Fin m × Fin m => e.2) henc
                  simp [RedFiber, hvproj]
              | inr b =>
                  simp [encode] at henc
            · intro z hz z' hz' hv
              have hzfin : z ∈ inc.filter (fun z => encode z = Sum.inl q) := by
                simpa using hz
              have hzfin' : z' ∈ inc.filter (fun z => encode z = Sum.inl q) := by
                simpa using hz'
              rw [Finset.mem_filter] at hzfin hzfin'
              have henc : encode z = Sum.inl q := hzfin.2
              have henc' : encode z' = Sum.inl q := hzfin'.2
              rcases z with ⟨x, v⟩
              rcases z' with ⟨x', v'⟩
              cases x with
              | inl r =>
                  cases x' with
                  | inl r' =>
                      simp [encode] at henc henc'
                      have hr : r = q.1 :=
                        congrArg (fun e : Fin m × Fin m => e.1) henc
                      have hr' : r' = q.1 :=
                        congrArg (fun e : Fin m × Fin m => e.1) henc'
                      change v = v' at hv
                      subst v'
                      have hrr : r = r' := hr.trans hr'.symm
                      subst r'
                      cases hr
                      rfl
                  | inr b' =>
                      simp [encode] at henc'
              | inr b =>
                  simp [encode] at henc
          exact le_trans (by exact_mod_cast hcard_le) (hRedFiber_le q.2)
      | inr q =>
          have hcard_le :
              (inc.filter (fun z => encode z = Sum.inr q)).card ≤
                (BlueFiber ω q.2).card := by
            refine Finset.card_le_card_of_injOn (fun z => z.2) ?_ ?_
            · intro z hz
              have hzfin : z ∈ inc.filter (fun z => encode z = Sum.inr q) := by
                simpa using hz
              rw [Finset.mem_filter] at hzfin
              have henc : encode z = Sum.inr q := hzfin.2
              rcases z with ⟨x, v⟩
              cases x with
              | inl r =>
                  simp [encode] at henc
              | inr b =>
                  simp [encode] at henc
                  have hvproj : TwoBiteBlueProjection ω v = q.2 :=
                    by
                      cases henc
                      rfl
                  simp [BlueFiber, hvproj]
            · intro z hz z' hz' hv
              have hzfin : z ∈ inc.filter (fun z => encode z = Sum.inr q) := by
                simpa using hz
              have hzfin' : z' ∈ inc.filter (fun z => encode z = Sum.inr q) := by
                simpa using hz'
              rw [Finset.mem_filter] at hzfin hzfin'
              have henc : encode z = Sum.inr q := hzfin.2
              have henc' : encode z' = Sum.inr q := hzfin'.2
              rcases z with ⟨x, v⟩
              rcases z' with ⟨x', v'⟩
              cases x with
              | inl r =>
                  simp [encode] at henc
              | inr b =>
                  cases x' with
                  | inl r' =>
                      simp [encode] at henc'
                  | inr b' =>
                      simp [encode] at henc henc'
                      have hb : b = q.1 :=
                        congrArg (fun e : Fin m × Fin m => e.1) henc
                      have hb' : b' = q.1 :=
                        congrArg (fun e : Fin m × Fin m => e.1) henc'
                      change v = v' at hv
                      subst v'
                      have hbb : b = b' := hb.trans hb'.symm
                      subst b'
                      cases hb
                      rfl
          exact le_trans (by exact_mod_cast hcard_le) (hBlueFiber_le q.2)
    have hinc_bound :
        (inc.card : ℝ) ≤ L * (((inc.image encode).card : ℕ) : ℝ) :=
      ProjectionFiberCardBound inc encode L hfiber
    have himage_subset :
        inc.image encode ⊆
          (redOrderedOf B).image
              (fun e => (Sum.inl e :
                Sum (Fin m × Fin m) (Fin m × Fin m))) ∪
            (blueOrderedOf B).image
              (fun e => (Sum.inr e :
                Sum (Fin m × Fin m) (Fin m × Fin m))) := by
      intro y hy
      rw [Finset.mem_image] at hy
      rcases hy with ⟨z, hzinc, rfl⟩
      rw [Finset.mem_union]
      rcases z with ⟨x, v⟩
      have hzmem := (Finset.mem_sigma.mp hzinc)
      rcases hzmem with ⟨hxB, hvX⟩
      cases x with
      | inl r =>
          left
          rw [Finset.mem_image]
          refine ⟨(r, TwoBiteRedProjection ω v), ?_, rfl⟩
          have hvX' := hvX
          rw [TwoBiteX, Finset.mem_filter] at hvX'
          have hvI : v ∈ I := hvX'.1
          have hvN : v ∈ TwoBiteLiftedNeighborhood ω (Sum.inl r) := hvX'.2
          have hvN' := hvN
          rw [TwoBiteLiftedNeighborhood, Finset.mem_filter] at hvN'
          have hadj : (TwoBiteRedGraph ω).Adj r (TwoBiteRedProjection ω v) := hvN'.2
          have hrCenter : r ∈ redCentersOf B := by
            simp [redCentersOf, hxB]
          have hproj : TwoBiteRedProjection ω v ∈ redProjection := by
            exact Finset.mem_image.mpr ⟨v, hvI, rfl⟩
          simp [redOrderedOf, hrCenter, hproj, hadj]
      | inr b =>
          right
          rw [Finset.mem_image]
          refine ⟨(b, TwoBiteBlueProjection ω v), ?_, rfl⟩
          have hvX' := hvX
          rw [TwoBiteX, Finset.mem_filter] at hvX'
          have hvI : v ∈ I := hvX'.1
          have hvN : v ∈ TwoBiteLiftedNeighborhood ω (Sum.inr b) := hvX'.2
          have hvN' := hvN
          rw [TwoBiteLiftedNeighborhood, Finset.mem_filter] at hvN'
          have hadj : (TwoBiteBlueGraph ω).Adj b (TwoBiteBlueProjection ω v) := hvN'.2
          have hbCenter : b ∈ blueCentersOf B := by
            simp [blueCentersOf, hxB]
          have hproj : TwoBiteBlueProjection ω v ∈ blueProjection := by
            exact Finset.mem_image.mpr ⟨v, hvI, rfl⟩
          simp [blueOrderedOf, hbCenter, hproj, hadj]
    have himage_card_le :
        ((inc.image encode).card : ℝ) ≤ (edgeCount B : ℝ) := by
      have hnat :
          (inc.image encode).card ≤ edgeCount B := by
        calc
          (inc.image encode).card
              ≤ ((redOrderedOf B).image
                    (fun e => (Sum.inl e :
                      Sum (Fin m × Fin m) (Fin m × Fin m))) ∪
                  (blueOrderedOf B).image
                    (fun e => (Sum.inr e :
                      Sum (Fin m × Fin m) (Fin m × Fin m)))).card :=
                Finset.card_le_card himage_subset
          _ ≤ ((redOrderedOf B).image
                    (fun e => (Sum.inl e :
                      Sum (Fin m × Fin m) (Fin m × Fin m)))).card +
                ((blueOrderedOf B).image
                    (fun e => (Sum.inr e :
                      Sum (Fin m × Fin m) (Fin m × Fin m)))).card :=
                Finset.card_union_le _ _
          _ ≤ (redOrderedOf B).card + (blueOrderedOf B).card :=
                Nat.add_le_add Finset.card_image_le Finset.card_image_le
          _ = edgeCount B := rfl
      exact_mod_cast hnat
    have hsum_inc :
        (∑ x ∈ B, (w x : ℝ)) = (inc.card : ℝ) := by
      dsimp [inc, w]
      exact_mod_cast
        (Finset.card_sigma (s := B)
          (t := fun x => TwoBiteX ω I x)).symm
    calc
      ∑ x ∈ B, (w x : ℝ) = (inc.card : ℝ) := hsum_inc
      _ ≤ L * (((inc.image encode).card : ℕ) : ℝ) := hinc_bound
      _ ≤ L * (edgeCount B : ℝ) :=
        mul_le_mul_of_nonneg_left himage_card_le (le_of_lt hL_pos)
  obtain ⟨B, hBne, hBM, hBlarge, hBupper, hBcard, hBedge⟩ :=
    MediumClosedPairsDeterministicReduction M w edgeCount A0 L t2 lower
      hA_nonneg hL_pos hlarge hupper hlower hcharge
  refine ⟨I, hIcard, hIbad, B, ?_⟩
  dsimp only
  refine ⟨hBne, ?_, hBlarge, hBupper, hBcard, ?_⟩
  · intro x hx
    simpa [M] using hBM hx
  · let normalize : Fin m × Fin m → Fin m × Fin m :=
      fun e => if e.1.val < e.2.val then e else (e.2, e.1)
    let redEdges : Finset (Fin m × Fin m) := (redOrderedOf B).image normalize
    let blueEdges : Finset (Fin m × Fin m) := (blueOrderedOf B).image normalize
    have hred_norm :
        ((redOrderedOf B).card : ℝ) ≤
          2 * (((redEdges.card : ℕ) : ℝ)) := by
      simpa [redEdges, normalize] using
        (NormalizePairImageCardBound (redOrderedOf B))
    have hblue_norm :
        ((blueOrderedOf B).card : ℝ) ≤
          2 * (((blueEdges.card : ℕ) : ℝ)) := by
      simpa [blueEdges, normalize] using
        (NormalizePairImageCardBound (blueOrderedOf B))
    have hordered_le :
        (edgeCount B : ℝ) ≤
          2 * (((redEdges.card + blueEdges.card : ℕ) : ℝ)) := by
      calc
        (edgeCount B : ℝ)
            = ((redOrderedOf B).card : ℝ) + ((blueOrderedOf B).card : ℝ) := by
              simp [edgeCount]
        _ ≤ 2 * ((redEdges.card : ℝ)) + 2 * ((blueEdges.card : ℝ)) := by
              linarith
        _ = 2 * (((redEdges.card + blueEdges.card : ℕ) : ℝ)) := by
              norm_num
              ring
    have htwo_tail :
        A0 / (2 * L) <
          (((redEdges.card + blueEdges.card : ℕ) : ℝ)) := by
      let S : ℝ := (((redEdges.card + blueEdges.card : ℕ) : ℝ))
      have hlt_two :
          A0 / L < 2 * S := by
        dsimp [S]
        exact lt_of_lt_of_le hBedge hordered_le
      have hLpos_local : 0 < L := by
        simpa [L] using hL_pos
      have htwoL_pos : 0 < 2 * L := by
        nlinarith
      have hlt_mul : A0 < (2 * S) * L := by
        rwa [div_lt_iff₀ hLpos_local] at hlt_two
      have hgoal_mul : A0 < S * (2 * L) := by
        nlinarith
      exact (div_lt_iff₀ htwoL_pos).mpr hgoal_mul
    have hden :
        2 * L = 6 * (Real.log (n : ℝ)) ^ 2 := by
      dsimp [L]
      ring
    have htwo_tail' :
        A0 / (6 * (Real.log (n : ℝ)) ^ 2) <
          (((redEdges.card + blueEdges.card : ℕ) : ℝ)) := by
      simpa [hden] using htwo_tail
    simpa [A0, normalize, redEdges, blueEdges, redOrderedOf, blueOrderedOf,
      redCentersOf, blueCentersOf, redProjection, blueProjection] using htwo_tail'
