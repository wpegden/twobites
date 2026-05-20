import Tablet.ClosedPairsBound
import Tablet.FixedSetHistoryCellCountPairSummation
import Tablet.FixedSetHistoryCellBinomialExponentialEstimate
import Tablet.FixedSetHistoryCellBranchAveraging
import Tablet.FixedSetHistoryCellFixedCountProductBound
import Tablet.ProjectionOpenPairFunction
import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBitePreTerminalRecordedPairs
import Tablet.TwoBiteProjectionPairSameColorClosed
import Tablet.TwoBiteProjectionPairTouched
import Tablet.TwoBiteProjectionSizeEvent
import Tablet.TwoBiteRegularityEvent
import Tablet.TwoBiteStagedOpenPairs
import Tablet.TwoBiteTerminalCoordinateUniverse

-- [TABLET NODE: FixedSetHistoryCellAdaptiveProductBound]

theorem FixedSetHistoryCellAdaptiveProductBound :
    ∀ {n m k ℓR ℓB : ℕ} {p ε ε1 ε2 : ℝ}
      (I : Finset (Fin n))
      (hist : TwoBiteSample n m p → Prop)
        (recorded terminal :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (order : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (redOrder : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (rep : TwoBiteSample n m p),
      0 ≤ ε1 →
      ε1 ≤ 1 →
      0 ≤ p →
      p ≤ (1 / 2 : ℝ) →
      I.card = k →
      hist rep →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
            (ℓB := ℓB) ω I) →
      (∀ ω : TwoBiteSample n m p,
        hist ω ↔
          (∀ x : Fin n, ω.2.2 x = rep.2.2 x) ∧
          (∀ e,
            e ∈ recorded →
              (TwoBiteEdgeCoordinateValue ω e ↔
                TwoBiteEdgeCoordinateValue rep e))) →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          ∀ e,
            e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔
              e ∈ recorded) →
      (∀ e,
        e ∈ terminal ↔
          e ∈ TwoBiteTerminalCoordinateUniverse m ∧ e ∉ recorded) →
        order.Nodup →
        order.toFinset = terminal →
        TwoBiteTerminalOrderBlueBeforeRed terminal order →
        redOrder.Nodup →
        redOrder.toFinset = terminal →
        TwoBiteTerminalOrderRedBeforeBlue terminal redOrder →
        (∀ e, e ∈ terminal → e ∉ recorded) →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          ∀ e,
            e ∈ TwoBiteStagedOpenPairs ω ε I →
              e ∈ terminal) →
      (∀ A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
        A ⊆ terminal →
          TwoBiteConditionalProbability n m p
            (fun ω =>
              ∀ e, e ∈ terminal →
                (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A))
            hist =
            p ^ A.card *
              ((1 : ℝ) - p) ^ (terminal.card - A.card)) →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          ∀ (pre : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
            (e : Sum (Fin m × Fin m) (Fin m × Fin m))
            (suffix : List (Sum (Fin m × Fin m) (Fin m × Fin m))),
            order = pre ++ e :: suffix →
              ∀ ω' : TwoBiteSample n m p,
                (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) →
                (∀ c,
                  c ∈ recorded →
                    (TwoBiteEdgeCoordinateValue ω c ↔
                      TwoBiteEdgeCoordinateValue ω' c)) →
                (∀ c,
                  c ∈ pre.toFinset →
                    (TwoBiteEdgeCoordinateValue ω c ↔
                      TwoBiteEdgeCoordinateValue ω' c)) →
                  (e ∈ TwoBiteStagedOpenPairs ω ε I ↔
                    e ∈ TwoBiteStagedOpenPairs ω' ε I) ∧
                  (TwoBiteProjectionPairTouched ω ε I e ↔
                    TwoBiteProjectionPairTouched ω' ε I e) ∧
                  (TwoBiteProjectionPairSameColorClosed ω I e ↔
                    TwoBiteProjectionPairSameColorClosed ω' I e) ∧
                    (e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔
                      e ∈ TwoBitePreTerminalRecordedPairs ω' ε I)) →
        (∀ ω : TwoBiteSample n m p,
          hist ω →
            ∀ (pre : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
              (e : Sum (Fin m × Fin m) (Fin m × Fin m))
              (suffix : List (Sum (Fin m × Fin m) (Fin m × Fin m))),
              redOrder = pre ++ e :: suffix →
                ∀ ω' : TwoBiteSample n m p,
                  (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) →
                  (∀ c,
                    c ∈ recorded →
                      (TwoBiteEdgeCoordinateValue ω c ↔
                        TwoBiteEdgeCoordinateValue ω' c)) →
                  (∀ c,
                    c ∈ pre.toFinset →
                      (TwoBiteEdgeCoordinateValue ω c ↔
                        TwoBiteEdgeCoordinateValue ω' c)) →
                    (e ∈ TwoBiteStagedOpenPairs ω ε I ↔
                      e ∈ TwoBiteStagedOpenPairs ω' ε I) ∧
                    (TwoBiteProjectionPairTouched ω ε I e ↔
                      TwoBiteProjectionPairTouched ω' ε I e) ∧
                    (TwoBiteProjectionPairSameColorClosed ω I e ↔
                      TwoBiteProjectionPairSameColorClosed ω' I e) ∧
                    (e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔
                      e ∈ TwoBitePreTerminalRecordedPairs ω' ε I)) →
      (∀ ω : TwoBiteSample n m p,
        TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
        TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
          (ℓB := ℓB) ω I →
        ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
            (k : ℝ) p (n : ℝ) - 10 * ε1 * (k : ℝ) ^ 2
          ≤ ((TwoBiteStagedOpenPairs ω ε I).card : ℝ)) →
      (∀ branch : TwoBiteSample n m p,
        hist branch →
          ∃ ER EB : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
            ER ⊆ terminal ∧
            EB ⊆ terminal ∧
            (∀ ω : TwoBiteSample n m p,
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
                ClosedPairsBound ((ER.card : ℝ)) (3 * ε1) (k : ℝ) ∧
                (∀ e,
                  e ∈ TwoBiteStagedOpenPairs ω ε I →
                  TwoBiteEdgeCoordinateValue ω e →
                  (match e with
                  | Sum.inl _ => True
                  | Sum.inr _ => False) →
                  (TwoBiteFinalGraph ω).2.2.IsIndepSet
                    (↑I : Set (Fin n)) →
                    e ∈ ER)) ∧
            (∀ ω : TwoBiteSample n m p,
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
                ClosedPairsBound ((EB.card : ℝ)) (3 * ε1) (k : ℝ) ∧
                (∀ e,
                  e ∈ TwoBiteStagedOpenPairs ω ε I →
                  TwoBiteEdgeCoordinateValue ω e →
                  (match e with
                  | Sum.inl _ => False
                  | Sum.inr _ => True) →
                  (TwoBiteFinalGraph ω).2.2.IsIndepSet
                    (↑I : Set (Fin n)) →
                    e ∈ EB))) →
      TwoBiteConditionalProbability n m p
          (fun ω =>
            (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) ∧
              TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω)
          hist
        ≤
        max (1 : ℝ) ((k : ℝ) ^ 4) *
          Real.exp
            (8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 -
              p *
                (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
                  (k : ℝ) p (n : ℝ) -
                  10 * ε1 * (k : ℝ) ^ 2)) := by
-- BODY
  intro n m k ℓR ℓB p ε ε1 ε2 I hist recorded terminal order redOrder rep
    hε1_nonneg hε1_le_one hp_nonneg hp_le_half hI_card hhist_rep hprojSize
    hhist_desc hrecorded hterminal horder_nodup horder_finset hblue_before_red
    hredOrder_nodup hredOrder_finset hred_before_blue hterminal_not_recorded
    hstaged_terminal hproductLaw hprefix_safe hred_prefix_safe hopen_lower hbranch_pkg
  classical
  let target : TwoBiteSample n m p → Prop := fun ω =>
    (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) ∧
      TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω
  let a : ℝ :=
    ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ) (k : ℝ) p (n : ℝ) -
      10 * ε1 * (k : ℝ) ^ 2
  let B : ℝ :=
    max (1 : ℝ) ((k : ℝ) ^ 4) *
      Real.exp (8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 - p * a)
  have hp_le_one : p ≤ 1 := by
    linarith
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact
      mul_nonneg
        (le_trans zero_le_one (le_max_left (1 : ℝ) ((k : ℝ) ^ 4)))
        (Real.exp_pos _).le
  have htarget_hist_projection :
      ∀ ω : TwoBiteSample n m p, hist ω → target ω →
        a ≤ ((TwoBiteStagedOpenPairs ω ε I).card : ℝ) := by
    intro ω hhist htarget
    exact hopen_lower ω htarget.2 (hprojSize ω hhist)
  have hrep_projection :
      TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR) (ℓB := ℓB) rep I :=
    hprojSize rep hhist_rep
  obtain ⟨ER_rep, EB_rep, hER_rep_subset, hEB_rep_subset, hER_rep, hEB_rep⟩ :=
    hbranch_pkg rep hhist_rep
  have hfixed_count_binomial :
      ∀ {uR uB NR NB : ℕ},
        uB ≤ uR →
        (NR : ℝ) ≤ 3 * ε1 * (k : ℝ) ^ 2 →
        (NB : ℝ) ≤ (k : ℝ) ^ 2 →
          (Nat.choose NR uR : ℝ) * p ^ uR *
              (Nat.choose NB uB : ℝ) * p ^ uB *
            Real.rpow ((1 : ℝ) - p)
              (max 0 (a - (uR : ℝ) - (uB : ℝ)))
            ≤
            Real.exp
              (8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 - p * a) := by
    intro uR uB NR NB hu hNR hNB
    simpa [a] using
      FixedSetHistoryCellBinomialExponentialEstimate
        (k := k) (uR := uR) (uB := uB) (NR := NR) (NB := NB)
        (p := p) (ε1 := ε1) (a := a)
        hε1_nonneg hε1_le_one hp_nonneg hp_le_half hu hNR hNB
  have hbranch_averaging_ready :
      ∀ {Branch : Type} [Fintype Branch]
        (fixedCount : TwoBiteSample n m p → Prop)
        (firstBranch : Branch → TwoBiteSample n m p → Prop),
        (∀ ω : TwoBiteSample n m p, fixedCount ω → hist ω) →
        (∀ b : Branch, ∀ ω : TwoBiteSample n m p, firstBranch b ω → hist ω) →
        (∀ ω : TwoBiteSample n m p,
          hist ω → fixedCount ω → ∃ b : Branch, firstBranch b ω) →
        (∀ b c : Branch, b ≠ c →
          ∀ ω : TwoBiteSample n m p,
            ¬ (firstBranch b ω ∧ firstBranch c ω)) →
        (∀ b : Branch,
          TwoBiteEventProbability n m p
              (fun ω => target ω ∧ fixedCount ω ∧ firstBranch b ω)
            ≤ B * TwoBiteEventProbability n m p (firstBranch b)) →
        TwoBiteConditionalProbability n m p
            (fun ω => target ω ∧ fixedCount ω)
            hist
          ≤ B := by
    intro Branch _ fixedCount firstBranch hFixedHist hBranchHist hCover hDisjoint
      hBranchBound
    exact
      FixedSetHistoryCellBranchAveraging
        (n := n) (m := m) (p := p) (B := B)
        hist fixedCount target (Branch := Branch) firstBranch
        hp_nonneg hp_le_one hB_nonneg hFixedHist hBranchHist hCover hDisjoint
        hBranchBound
  have hcount_multiplier_nonneg :
      0 ≤ max (1 : ℝ) ((k : ℝ) ^ 4) :=
    le_trans zero_le_one (le_max_left (1 : ℝ) ((k : ℝ) ^ 4))
  have hexponential_bound_nonneg :
      0 ≤
        Real.exp
          (8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 - p * a) :=
    (Real.exp_pos _).le
  have hfixed_count_product :
      ∀ uR uB : ℕ,
        TwoBiteConditionalProbability n m p
          (fun ω =>
            target ω ∧
              (((TwoBiteStagedOpenPairs ω ε I).filter
                (fun e =>
                  TwoBiteEdgeCoordinateValue ω e ∧
                    match e with
                    | Sum.inl _ => True
                    | Sum.inr _ => False)).card = uR) ∧
              (((TwoBiteStagedOpenPairs ω ε I).filter
                (fun e =>
                  TwoBiteEdgeCoordinateValue ω e ∧
                    match e with
                    | Sum.inl _ => False
                    | Sum.inr _ => True)).card = uB))
          hist
          ≤ Real.exp
              (8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 - p * a) := by
    intro uR uB
    simpa [target, a] using
      FixedSetHistoryCellFixedCountProductBound
        (n := n) (m := m) (k := k) (ℓR := ℓR) (ℓB := ℓB)
        (p := p) (ε := ε) (ε1 := ε1) (ε2 := ε2)
          I hist recorded terminal order redOrder rep uR uB
          hε1_nonneg hε1_le_one hp_nonneg hp_le_half hI_card
          hhist_rep hprojSize hhist_desc hrecorded hterminal horder_nodup
          horder_finset hblue_before_red hredOrder_nodup hredOrder_finset
          hred_before_blue hterminal_not_recorded hstaged_terminal hproductLaw
          hprefix_safe hred_prefix_safe hopen_lower hbranch_pkg
  have hcount_pair_sum :
      TwoBiteConditionalProbability n m p target hist
        ≤
        max (1 : ℝ) ((k : ℝ) ^ 4) *
          Real.exp
            (8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 - p * a) := by
    exact
      FixedSetHistoryCellCountPairSummation
        (n := n) (m := m) (k := k) (p := p) (ε := ε)
        (C :=
          Real.exp
            (8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 - p * a))
        I hist target hp_nonneg hp_le_one hexponential_bound_nonneg hI_card
        hfixed_count_product
  simpa [target, a] using hcount_pair_sum
