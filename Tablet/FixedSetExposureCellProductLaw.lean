import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBiteRegularityEvent
import Tablet.TwoBiteProjectionSizeEvent
import Tablet.TwoBiteStagedOpenPairs
import Tablet.TwoBiteRedGraph
import Tablet.TwoBiteBlueGraph
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteProjectionPairTouched
import Tablet.TwoBiteProjectionPairSameColorClosed
import Tablet.TwoBiteTerminalCoordinateUniverse
import Tablet.TwoBitePreTerminalRecordedPairs
import Tablet.FixedSetExposureHistoryCylinder
import Tablet.FixedSetCylinderProductLaw

-- [TABLET NODE: FixedSetExposureCellProductLaw]

theorem FixedSetExposureCellProductLaw :
    ∀ {n m k ℓR ℓB : ℕ} {p ε ε1 ε2 : ℝ} (I : Finset (Fin n)),
      0 < p →
      p < 1 →
      ∃ ι : Type, ∃ _ : Fintype ι, ∃ hist : ι → TwoBiteSample n m p → Prop,
        (∀ ω : TwoBiteSample n m p,
          TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I
            ↔ ∃ i : ι, hist i ω) ∧
        (∀ i j : ι, i ≠ j → ∀ ω : TwoBiteSample n m p,
          ¬ (hist i ω ∧ hist j ω)) ∧
        (∀ i : ι,
          ∃ recorded :
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
          ∃ terminal :
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
          ∃ order :
            List (Sum (Fin m × Fin m) (Fin m × Fin m)),
          ∃ rep : TwoBiteSample n m p,
            hist i rep ∧
            (∀ ω : TwoBiteSample n m p,
              hist i ω ↔
                (∀ x : Fin n, ω.2.2 x = rep.2.2 x) ∧
                (∀ e,
                  e ∈ recorded →
                    (TwoBiteEdgeCoordinateValue ω e ↔
                      TwoBiteEdgeCoordinateValue rep e))) ∧
            (∀ ω : TwoBiteSample n m p,
              hist i ω →
                ∀ e,
                  e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔
                    e ∈ recorded) ∧
            (∀ e, e ∈ recorded →
              match e with
              | Sum.inl q => q.1.val < q.2.val
              | Sum.inr q => q.1.val < q.2.val) ∧
            order.Nodup ∧
            order.toFinset = terminal ∧
            (∀ e, e ∈ terminal ↔
              e ∈ TwoBiteTerminalCoordinateUniverse m ∧ e ∉ recorded) ∧
            (∀ e, e ∈ terminal → e ∉ recorded) ∧
            (∀ e, e ∈ terminal →
              match e with
              | Sum.inl q => q.1.val < q.2.val
              | Sum.inr q => q.1.val < q.2.val) ∧
            (∀ ω : TwoBiteSample n m p,
              hist i ω →
                ∀ e,
                  e ∈ TwoBiteStagedOpenPairs ω ε I →
                    e ∈ terminal) ∧
            (∀ A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
              A ⊆ terminal →
                TwoBiteConditionalProbability n m p
                  (fun ω =>
                    ∀ e, e ∈ terminal →
                      (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A))
                  (hist i)
                  =
                    p ^ A.card *
                      ((1 : ℝ) - p) ^ (terminal.card - A.card)) ∧
            (∀ ω : TwoBiteSample n m p,
              hist i ω →
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
                          e ∈ TwoBitePreTerminalRecordedPairs ω' ε I))) ∧
        (∀ B : ℝ,
          0 ≤ B →
          (∀ i : ι,
            TwoBiteConditionalProbability n m p
              (fun ω =>
                (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) ∧
                  TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω)
              (hist i) ≤ B) →
            TwoBiteConditionalProbability n m p
              (fun ω =>
                (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) ∧
                  TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω)
              (fun ω =>
                TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
                  (ℓB := ℓB) ω I) ≤ B) := by
-- BODY
  intro n m k ℓR ℓB p ε ε1 ε2 I hp_pos hp_lt
  classical
  rcases
      FixedSetExposureHistoryCylinder
        (n := n) (m := m) (k := k) (ℓR := ℓR) (ℓB := ℓB)
        (p := p) (ε := ε) I with
    ⟨ι, instι, hist, recorded, terminal, order, rep,
      hCover, hDisjoint, hRepHist, hHistCylinder, hRecordedIdentity,
      hRecordedOriented, hCellProjection, hOrderFacts, hTerminalIff,
      hTerminalUnrecorded, hTerminalOriented, hStagedContainment,
      hPrefixSafe⟩
  refine ⟨ι, instι, hist, hCover, hDisjoint, ?_, ?_⟩
  · intro i
    refine
      ⟨recorded i, terminal i, order i, rep i,
        hRepHist i, hHistCylinder i, ?_, hRecordedOriented i,
        (hOrderFacts i).1, (hOrderFacts i).2, hTerminalIff i,
        hTerminalUnrecorded i, hTerminalOriented i,
        hStagedContainment i, ?_, hPrefixSafe i⟩
    · intro ω hω e
      exact hRecordedIdentity i ω hω e
    · exact
        FixedSetCylinderProductLaw
          (n := n) (m := m) (p := p)
          (hist i) (recorded i) (terminal i) (rep i)
          hp_pos hp_lt (hRepHist i) (hHistCylinder i)
          (hRecordedOriented i) (hTerminalUnrecorded i)
          (hTerminalOriented i)
  · intro B hB hCellBound
    let E : TwoBiteSample n m p → Prop :=
      fun ω =>
        (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) ∧
          TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω
    let S : TwoBiteSample n m p → Prop :=
      fun ω =>
        TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
          (ℓB := ℓB) ω I
    let prob : (TwoBiteSample n m p → Prop) → ℝ :=
      fun F => TwoBiteEventProbability n m p F
    have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
    have hp_le_one : p ≤ 1 := le_of_lt hp_lt
    have hweight : ∀ ω : TwoBiteSample n m p, 0 ≤ TwoBiteSampleWeight ω := by
      intro ω
      have hG1 : 0 ≤ GnpGraphWeight p ω.1 := by
        classical
        unfold GnpGraphWeight
        exact Finset.prod_nonneg (by
          intro e he
          by_cases hAdj : SimpleGraph.Adj ω.1 e.1 e.2
          · simp [hAdj, hp_nonneg]
          · have h : 0 ≤ 1 - p := sub_nonneg.mpr hp_le_one
            simp [hAdj, h])
      have hG2 : 0 ≤ GnpGraphWeight p ω.2.1 := by
        classical
        unfold GnpGraphWeight
        exact Finset.prod_nonneg (by
          intro e he
          by_cases hAdj : SimpleGraph.Adj ω.2.1 e.1 e.2
          · simp [hAdj, hp_nonneg]
          · have h : 0 ≤ 1 - p := sub_nonneg.mpr hp_le_one
            simp [hAdj, h])
      have hU : 0 ≤ UniformInjectionWeight n m := by
        unfold UniformInjectionWeight
        split_ifs <;> positivity
      unfold TwoBiteSampleWeight
      positivity
    have prob_nonneg :
        ∀ F : TwoBiteSample n m p → Prop, 0 ≤ prob F := by
      intro F
      unfold prob TwoBiteEventProbability
      exact Finset.sum_nonneg (by
        intro ω hω
        exact hweight ω)
    have prob_mono :
        ∀ {A C : TwoBiteSample n m p → Prop},
          (∀ ω, A ω → C ω) → prob A ≤ prob C := by
      intro A C hAC
      unfold prob TwoBiteEventProbability
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (by
          intro ω hω
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
          exact hAC ω hω)
        (by
          intro ω hωC hωnotA
          exact hweight ω)
    have hpartition :
        ∀ F : TwoBiteSample n m p → Prop,
          prob (fun ω => F ω ∧ S ω) =
            (Finset.univ : Finset ι).sum
              (fun i => prob (fun ω => F ω ∧ hist i ω)) := by
      intro F
      have hpoint :
          ∀ ω : TwoBiteSample n m p,
            (if F ω ∧ S ω then TwoBiteSampleWeight ω else 0) =
              (Finset.univ : Finset ι).sum
                (fun i =>
                  if F ω ∧ hist i ω then TwoBiteSampleWeight ω else 0) := by
        intro ω
        by_cases hF : F ω
        · by_cases hSω : S ω
          · rcases (hCover ω).1 hSω with ⟨i0, hi0⟩
            have hsum :
                (Finset.univ : Finset ι).sum
                  (fun i =>
                    if F ω ∧ hist i ω then TwoBiteSampleWeight ω else 0) =
                    TwoBiteSampleWeight ω := by
              rw [Finset.sum_eq_single i0]
              · simp [hF, hi0]
              · intro j hj hji
                have hnot : ¬ hist j ω := by
                  intro hjhist
                  exact (hDisjoint j i0 hji ω) ⟨hjhist, hi0⟩
                simp [hnot]
              · intro hi0_not_mem
                exact False.elim (hi0_not_mem (Finset.mem_univ i0))
            simpa [hF, hSω] using hsum.symm
          · have hnoHist : ∀ i : ι, ¬ hist i ω := by
              intro i hi
              exact hSω ((hCover ω).2 ⟨i, hi⟩)
            have hsum :
                (Finset.univ : Finset ι).sum
                  (fun i =>
                    if F ω ∧ hist i ω then TwoBiteSampleWeight ω else 0) =
                    0 := by
              exact Finset.sum_eq_zero (by
                intro i hi
                simp [hnoHist i])
            simpa [hF, hSω] using hsum.symm
        · have hsum :
              (Finset.univ : Finset ι).sum
                (fun i =>
                  if F ω ∧ hist i ω then TwoBiteSampleWeight ω else 0) =
                  0 := by
            exact Finset.sum_eq_zero (by
              intro i hi
              simp [hF])
          simp [hF]
      calc
        prob (fun ω => F ω ∧ S ω)
            =
          (Finset.univ : Finset (TwoBiteSample n m p)).sum
            (fun ω => if F ω ∧ S ω then TwoBiteSampleWeight ω else 0) := by
              dsimp [prob, TwoBiteEventProbability]
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl ?_
              intro ω hω
              by_cases h : F ω ∧ S ω <;> simp [h]
        _ =
          (Finset.univ : Finset ι).sum
            (fun i => prob (fun ω => F ω ∧ hist i ω)) := by
              calc
                (Finset.univ : Finset (TwoBiteSample n m p)).sum
                  (fun ω =>
                    if F ω ∧ S ω then TwoBiteSampleWeight ω else 0)
                    =
                  (Finset.univ : Finset (TwoBiteSample n m p)).sum
                    (fun ω =>
                      (Finset.univ : Finset ι).sum
                        (fun i =>
                          if F ω ∧ hist i ω then
                            TwoBiteSampleWeight ω
                          else
                            0)) := by
                      exact Finset.sum_congr rfl (by
                        intro ω hω
                        exact hpoint ω)
                _ =
                  (Finset.univ : Finset ι).sum
                    (fun i =>
                      (Finset.univ : Finset (TwoBiteSample n m p)).sum
                        (fun ω =>
                          if F ω ∧ hist i ω then
                            TwoBiteSampleWeight ω
                          else
                            0)) := by
                      rw [Finset.sum_comm]
                _ =
                  (Finset.univ : Finset ι).sum
                    (fun i => prob (fun ω => F ω ∧ hist i ω)) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      dsimp [prob, TwoBiteEventProbability]
                      rw [Finset.sum_filter]
                      refine Finset.sum_congr rfl ?_
                      intro ω hω
                      by_cases h : F ω ∧ hist i ω <;> simp [h]
    have hcell_inter_bound :
        ∀ i : ι,
          prob (fun ω => E ω ∧ hist i ω) ≤ B * prob (hist i) := by
      intro i
      by_cases hzero : prob (hist i) = 0
      · have hinter_le_cell :
            prob (fun ω => E ω ∧ hist i ω) ≤ prob (hist i) :=
          prob_mono (by
            intro ω hω
            exact hω.2)
        have hinter_eq_zero :
            prob (fun ω => E ω ∧ hist i ω) = 0 := by
          exact le_antisymm (by simpa [hzero] using hinter_le_cell)
            (prob_nonneg _)
        simp [hinter_eq_zero, hzero]
      · have hcell_pos : 0 < prob (hist i) :=
          lt_of_le_of_ne (prob_nonneg (hist i)) (Ne.symm hzero)
        have hcond :
            prob (fun ω => E ω ∧ hist i ω) / prob (hist i) ≤ B := by
          simpa [prob, E, TwoBiteConditionalProbability, hzero]
            using hCellBound i
        exact (div_le_iff₀ hcell_pos).mp hcond
    have hnum_le :
        prob (fun ω => E ω ∧ S ω) ≤ B * prob S := by
      have hpartE := hpartition E
      have hpartS : prob S =
          (Finset.univ : Finset ι).sum (fun i => prob (hist i)) := by
        have hpartTrue := hpartition (fun _ => True)
        simpa using hpartTrue
      rw [hpartE, hpartS]
      calc
        (Finset.univ : Finset ι).sum
            (fun i => prob (fun ω => E ω ∧ hist i ω))
            ≤
          (Finset.univ : Finset ι).sum
            (fun i => B * prob (hist i)) := by
              exact Finset.sum_le_sum (by
                intro i hi
                exact hcell_inter_bound i)
        _ = B * (Finset.univ : Finset ι).sum (fun i => prob (hist i)) := by
              exact
                (Finset.mul_sum (Finset.univ : Finset ι)
                  (fun i => prob (hist i)) B).symm
    unfold TwoBiteConditionalProbability
    by_cases hzero : prob S = 0
    · simp [prob, S, hzero, hB]
    · have hden_pos : 0 < prob S :=
        lt_of_le_of_ne (prob_nonneg S) (Ne.symm hzero)
      have hdiv :
          prob (fun ω => E ω ∧ S ω) / prob S ≤ B :=
        (div_le_iff₀ hden_pos).mpr hnum_le
      simpa [prob, E, S, hzero] using hdiv
