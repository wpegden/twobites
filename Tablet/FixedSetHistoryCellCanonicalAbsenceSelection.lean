import Mathlib.Tactic.Linarith
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBitePreTerminalRecordedPairs
import Tablet.TwoBiteProjectionPairSameColorClosed
import Tablet.TwoBiteProjectionPairTouched
import Tablet.TwoBiteStagedOpenPairs

-- [TABLET NODE: FixedSetHistoryCellCanonicalAbsenceSelection]

theorem FixedSetHistoryCellCanonicalAbsenceSelection :
    ∀ {n m : ℕ} {p ε a : ℝ}
      (I : Finset (Fin n))
      (hist : TwoBiteSample n m p → Prop)
      (recorded terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (order : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (R B : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (ω : TwoBiteSample n m p),
      hist ω →
      order.Nodup →
      order.toFinset = terminal →
      (∀ e,
        e ∈ TwoBiteStagedOpenPairs ω ε I →
          e ∈ terminal) →
        (∀ (pre suffix :
            List (Sum (Fin m × Fin m) (Fin m × Fin m)))
          (e : Sum (Fin m × Fin m) (Fin m × Fin m)),
          order = pre ++ e :: suffix →
          ∀ ω' : TwoBiteSample n m p,
            (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) →
            (∀ c,
              c ∈ recorded →
                (TwoBiteEdgeCoordinateValue ω c ↔
                  TwoBiteEdgeCoordinateValue ω' c)) →
            (∀ c,
                c ∈ List.toFinset pre →
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
      a ≤ ((TwoBiteStagedOpenPairs ω ε I).card : ℝ) →
      (∀ e, e ∈ R →
        e ∈ TwoBiteStagedOpenPairs ω ε I ∧
          TwoBiteEdgeCoordinateValue ω e) →
      (∀ e, e ∈ B →
        e ∈ TwoBiteStagedOpenPairs ω ε I ∧
          TwoBiteEdgeCoordinateValue ω e) →
      (∀ e,
        e ∈ TwoBiteStagedOpenPairs ω ε I →
          TwoBiteEdgeCoordinateValue ω e →
            e ∈ R ∨ e ∈ B) →
      ∃ Z : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
        Z = (TwoBiteStagedOpenPairs ω ε I).filter (fun e => e ∉ R ∪ B) ∧
        Z ⊆ terminal ∧
          Disjoint Z (R ∪ B) ∧
          (∀ e,
            e ∈ Z →
              e ∈ TwoBiteStagedOpenPairs ω ε I ∧
                ¬ TwoBiteEdgeCoordinateValue ω e ∧
                  ∃ (pre suffix :
                    List (Sum (Fin m × Fin m) (Fin m × Fin m))),
                    order = pre ++ e :: suffix ∧
                    ∀ ω' : TwoBiteSample n m p,
                      (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) →
                      (∀ c,
                        c ∈ recorded →
                          (TwoBiteEdgeCoordinateValue ω c ↔
                            TwoBiteEdgeCoordinateValue ω' c)) →
                      (∀ c,
                          c ∈ List.toFinset pre →
                          (TwoBiteEdgeCoordinateValue ω c ↔
                            TwoBiteEdgeCoordinateValue ω' c)) →
                        (e ∈ TwoBiteStagedOpenPairs ω ε I ↔
                          e ∈ TwoBiteStagedOpenPairs ω' ε I) ∧
                        (TwoBiteProjectionPairTouched ω ε I e ↔
                          TwoBiteProjectionPairTouched ω' ε I e) ∧
                        (TwoBiteProjectionPairSameColorClosed ω I e ↔
                          TwoBiteProjectionPairSameColorClosed ω' I e) ∧
                        (e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔
                          e ∈ TwoBitePreTerminalRecordedPairs ω' ε I)) ∧
          max 0 (a - (R.card : ℝ) - (B.card : ℝ)) ≤ (Z.card : ℝ) := by
-- BODY
  classical
  intro n m p ε a I hist recorded terminal order R B ω _hmem _horder_nodup
    horder hterminal hprefix hopen hR hB hpresent_cover
  let S : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    TwoBiteStagedOpenPairs ω ε I
  let U : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) := R ∪ B
  let Z : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    S.filter (fun e => e ∉ U)
  refine ⟨Z, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro e heZ
    have heS : e ∈ S := (Finset.mem_filter.mp heZ).1
    exact hterminal e (by simpa [S] using heS)
  · rw [Finset.disjoint_left]
    intro e heZ heU
    exact (Finset.mem_filter.mp heZ).2 heU
  · intro e heZ
    have heS : e ∈ S := (Finset.mem_filter.mp heZ).1
    have hnotU : e ∉ U := (Finset.mem_filter.mp heZ).2
    have hnotPresent : ¬ TwoBiteEdgeCoordinateValue ω e := by
      intro hpresent
      rcases hpresent_cover e (by simpa [S] using heS) hpresent with hRmem | hBmem
      · exact hnotU (by simp [U, hRmem])
      · exact hnotU (by simp [U, hBmem])
    have heTerminal : e ∈ terminal := hterminal e (by simpa [S] using heS)
    have heOrderFinset : e ∈ order.toFinset := by
      simpa [horder] using heTerminal
    have heOrder : e ∈ order := by
      simpa using heOrderFinset
    rcases (List.mem_iff_append.mp heOrder) with ⟨pre, suffix, hsplit⟩
    refine ⟨by simpa [S] using heS, hnotPresent, pre, suffix, hsplit, ?_⟩
    intro ω' hx hrecorded hpast
    exact hprefix pre suffix e hsplit ω' hx hrecorded hpast
  · let removed : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
      S.filter (fun e => e ∈ U)
    have hcard_partition : removed.card + Z.card = S.card := by
      simpa [removed, Z] using
        (Finset.card_filter_add_card_filter_not
          (s := S) (p := fun e => e ∈ U))
    have hremoved_subset : removed ⊆ U := by
      intro e he
      exact (Finset.mem_filter.mp he).2
    have hremoved_le_union : removed.card ≤ U.card :=
      Finset.card_le_card hremoved_subset
    have hunion_le : U.card ≤ R.card + B.card := by
      simpa [U] using (Finset.card_union_le R B)
    have hremoved_le : removed.card ≤ R.card + B.card :=
      le_trans hremoved_le_union hunion_le
    have hS_card_bound_nat : S.card ≤ Z.card + R.card + B.card := by
      calc
        S.card = removed.card + Z.card := hcard_partition.symm
        _ ≤ (R.card + B.card) + Z.card :=
          Nat.add_le_add_right hremoved_le Z.card
        _ = Z.card + R.card + B.card := by
          rw [Nat.add_comm (R.card + B.card) Z.card]
          rw [Nat.add_assoc]
    have hS_card_bound_real :
        (S.card : ℝ) ≤ (Z.card : ℝ) + (R.card : ℝ) + (B.card : ℝ) := by
      exact_mod_cast hS_card_bound_nat
    have hopen' : a ≤ (S.card : ℝ) := by
      simpa [S] using hopen
    have hmain :
        a - (R.card : ℝ) - (B.card : ℝ) ≤ (Z.card : ℝ) := by
      nlinarith
    have hzero : (0 : ℝ) ≤ (Z.card : ℝ) := by
      exact_mod_cast Nat.zero_le Z.card
    exact max_le hzero hmain
