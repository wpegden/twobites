import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.TwoBiteStagedOpenPairs

-- [TABLET NODE: FixedSetHistoryCellCountPairSummation]

theorem FixedSetHistoryCellCountPairSummation :
      ∀ {n m k : ℕ} {p ε C : ℝ}
        (I : Finset (Fin n))
        (hist target : TwoBiteSample n m p → Prop)
        [∀ (ω : TwoBiteSample n m p)
          (e : Sum (Fin m × Fin m) (Fin m × Fin m)),
          Decidable (TwoBiteEdgeCoordinateValue ω e)]
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
      0 ≤ p →
      p ≤ 1 →
      0 ≤ C →
      I.card = k →
      (∀ uR uB : ℕ,
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
          hist ≤ C) →
      TwoBiteConditionalProbability n m p target hist
        ≤ max (1 : ℝ) ((k : ℝ) ^ 4) * C := by
-- BODY
  classical
  intro n m k p ε C I hist target _hEdgeDec _hRedDec _hBlueDec hp0 hp1 hC hI hcell
  let Ω := TwoBiteSample n m p
  let prob : (Ω → Prop) → ℝ := fun E => TwoBiteEventProbability n m p E
  let redCount : Ω → ℕ := fun ω =>
    ((TwoBiteStagedOpenPairs ω ε I).filter
      (fun e =>
        TwoBiteEdgeCoordinateValue ω e ∧
          match e with
          | Sum.inl _ => True
          | Sum.inr _ => False)).card
  let blueCount : Ω → ℕ := fun ω =>
    ((TwoBiteStagedOpenPairs ω ε I).filter
      (fun e =>
        TwoBiteEdgeCoordinateValue ω e ∧
          match e with
          | Sum.inl _ => False
          | Sum.inr _ => True)).card
  let N : ℕ := max 1 (k ^ 2)
  let idx : Finset (ℕ × ℕ) := (Finset.range N) ×ˢ (Finset.range N)
  let cellEvent : ℕ × ℕ → Ω → Prop := fun ij ω =>
    target ω ∧ redCount ω = ij.1 ∧ blueCount ω = ij.2
  let cellWithHist : ℕ × ℕ → Ω → Prop := fun ij ω =>
    cellEvent ij ω ∧ hist ω
  have hweight : ∀ ω : Ω, 0 ≤ TwoBiteSampleWeight ω := by
    intro ω
    exact TwoBiteSampleWeightNonnegative ω hp0 hp1
  have prob_nonneg : ∀ E : Ω → Prop, 0 ≤ prob E := by
    intro E
    unfold prob TwoBiteEventProbability
    exact Finset.sum_nonneg (by
      intro ω hω
      exact hweight ω)
  have prob_mono :
      ∀ {A B : Ω → Prop}, (∀ ω, A ω → B ω) → prob A ≤ prob B := by
    intro A B hAB
    unfold prob TwoBiteEventProbability
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
        exact hAB ω hω)
      (by
        intro ω hωB hωnotA
        exact hweight ω)
  have prob_union_bound :
      ∀ {ι : Type} (s : Finset ι) (E : ι → Ω → Prop),
        prob (fun ω => ∃ i ∈ s, E i ω) ≤ s.sum (fun i => prob (E i)) := by
    intro ι s E
    let w : Ω → ℝ := fun ω => TwoBiteSampleWeight ω
    have hpoint :
        ∀ ω : Ω,
          (if ∃ i ∈ s, E i ω then w ω else 0) ≤
            s.sum (fun i => if E i ω then w ω else 0) := by
      intro ω
      by_cases h : ∃ i ∈ s, E i ω
      · rcases h with ⟨i, hi, hEi⟩
        have hex : ∃ i ∈ s, E i ω := ⟨i, hi, hEi⟩
        have hnonneg :
            ∀ j ∈ s, 0 ≤ (if E j ω then w ω else 0) := by
          intro j hj
          by_cases hEj : E j ω <;> simp [hEj, w, hweight ω]
        have hle :
            w ω ≤ s.sum (fun j => if E j ω then w ω else 0) := by
          simpa [hEi] using Finset.single_le_sum hnonneg hi
        simpa [hex] using hle
      · have hnonneg :
            0 ≤ s.sum (fun i => if E i ω then w ω else 0) := by
          exact Finset.sum_nonneg (by
            intro i hi
            by_cases hEi : E i ω <;> simp [hEi, w, hweight ω])
        simpa [h] using hnonneg
    calc
      prob (fun ω => ∃ i ∈ s, E i ω)
          = ∑ ω : Ω, if ∃ i ∈ s, E i ω then w ω else 0 := by
              unfold prob TwoBiteEventProbability
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl ?_
              intro ω hω
              by_cases h : ∃ i ∈ s, E i ω <;> simp [h, w]
      _ ≤ ∑ ω : Ω, s.sum (fun i => if E i ω then w ω else 0) := by
              exact Finset.sum_le_sum (by intro ω hω; exact hpoint ω)
      _ = s.sum (fun i => ∑ ω : Ω, if E i ω then w ω else 0) := by
              rw [Finset.sum_comm]
      _ = s.sum (fun i => prob (E i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              unfold prob TwoBiteEventProbability
              rw [Finset.sum_filter]
  have hBasePairs_card_le_sq :
      ∀ X : Finset (Fin m), (TwoBiteBasePairs X).card ≤ X.card ^ 2 := by
    intro X
    have hsubset : TwoBiteBasePairs X ⊆ X.product X := by
      intro q hq
      have hq' :
          (q.1 ∈ X ∧ q.2 ∈ X) ∧ (q.1 : Fin m).val < q.2.val := by
        simpa [TwoBiteBasePairs, TwoBitePairsInSet] using hq
      simpa using hq'.1
    calc
      (TwoBiteBasePairs X).card ≤ (X.product X).card :=
        Finset.card_le_card hsubset
      _ = X.card ^ 2 := by
        simp [pow_two, Finset.card_product]
  have hBasePairs_card_lt_sq :
      ∀ X : Finset (Fin m), X.Nonempty → (TwoBiteBasePairs X).card < X.card ^ 2 := by
    intro X hX
    have hsubset : TwoBiteBasePairs X ⊆ X.product X := by
      intro q hq
      have hq' :
          (q.1 ∈ X ∧ q.2 ∈ X) ∧ (q.1 : Fin m).val < q.2.val := by
        simpa [TwoBiteBasePairs, TwoBitePairsInSet] using hq
      simpa using hq'.1
    rcases hX with ⟨x, hx⟩
    have hdiag_product : (x, x) ∈ X.product X := by
      simp [hx]
    have hdiag_not_base : (x, x) ∉ TwoBiteBasePairs X := by
      simp [TwoBiteBasePairs, TwoBitePairsInSet, hx]
    have hproper : TwoBiteBasePairs X ⊂ X.product X := by
      refine ⟨hsubset, ?_⟩
      intro hreverse
      exact hdiag_not_base (hreverse hdiag_product)
    calc
      (TwoBiteBasePairs X).card < (X.product X).card :=
        Finset.card_lt_card hproper
      _ = X.card ^ 2 := by
        simp [pow_two, Finset.card_product]
  have redCount_le_base :
      ∀ ω : Ω,
        redCount ω ≤
          (TwoBiteBasePairs (I.image (TwoBiteRedProjection ω))).card := by
    intro ω
    let redSet : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
      (TwoBiteStagedOpenPairs ω ε I).filter
        (fun e =>
          TwoBiteEdgeCoordinateValue ω e ∧
            match e with
            | Sum.inl _ => True
            | Sum.inr _ => False)
    have hsubset :
        redSet ⊆
          (TwoBiteBasePairs (I.image (TwoBiteRedProjection ω))).image Sum.inl := by
      intro e he
      cases e with
      | inl q =>
          have heS : Sum.inl q ∈ TwoBiteStagedOpenPairs ω ε I :=
            (Finset.mem_filter.mp he).1
          have hproj : Sum.inl q ∈ TwoBiteProjectionPairSet ω I := by
            have heS' := heS
            simp [TwoBiteStagedOpenPairs] at heS'
            exact heS'.1
          have hq : q ∈ TwoBiteBasePairs (I.image (TwoBiteRedProjection ω)) := by
            simpa [TwoBiteProjectionPairSet] using hproj
          exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
      | inr q =>
          exact False.elim (Finset.mem_filter.mp he).2.2
    calc
      redCount ω = redSet.card := by
        rfl
      _ ≤ ((TwoBiteBasePairs (I.image (TwoBiteRedProjection ω))).image
            Sum.inl).card :=
        Finset.card_le_card hsubset
      _ ≤ (TwoBiteBasePairs (I.image (TwoBiteRedProjection ω))).card :=
        Finset.card_image_le
  have blueCount_le_base :
      ∀ ω : Ω,
        blueCount ω ≤
          (TwoBiteBasePairs (I.image (TwoBiteBlueProjection ω))).card := by
    intro ω
    let blueSet : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
      (TwoBiteStagedOpenPairs ω ε I).filter
        (fun e =>
          TwoBiteEdgeCoordinateValue ω e ∧
            match e with
            | Sum.inl _ => False
            | Sum.inr _ => True)
    have hsubset :
        blueSet ⊆
          (TwoBiteBasePairs (I.image (TwoBiteBlueProjection ω))).image Sum.inr := by
      intro e he
      cases e with
      | inl q =>
          exact False.elim (Finset.mem_filter.mp he).2.2
      | inr q =>
          have heS : Sum.inr q ∈ TwoBiteStagedOpenPairs ω ε I :=
            (Finset.mem_filter.mp he).1
          have hproj : Sum.inr q ∈ TwoBiteProjectionPairSet ω I := by
            have heS' := heS
            simp [TwoBiteStagedOpenPairs] at heS'
            exact heS'.1
          have hq : q ∈ TwoBiteBasePairs (I.image (TwoBiteBlueProjection ω)) := by
            simpa [TwoBiteProjectionPairSet] using hproj
          exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    calc
      blueCount ω = blueSet.card := by
        rfl
      _ ≤ ((TwoBiteBasePairs (I.image (TwoBiteBlueProjection ω))).image
            Sum.inr).card :=
        Finset.card_le_card hsubset
      _ ≤ (TwoBiteBasePairs (I.image (TwoBiteBlueProjection ω))).card :=
        Finset.card_image_le
  have redCount_le_k_sq : ∀ ω : Ω, redCount ω ≤ k ^ 2 := by
    intro ω
    let X : Finset (Fin m) := I.image (TwoBiteRedProjection ω)
    have hX_le_k : X.card ≤ k := by
      dsimp [X]
      rw [← hI]
      exact Finset.card_image_le
    have hX_sq_le_k_sq : X.card ^ 2 ≤ k ^ 2 :=
      Nat.pow_le_pow_left hX_le_k 2
    exact le_trans (redCount_le_base ω)
      (le_trans (hBasePairs_card_le_sq X) hX_sq_le_k_sq)
  have blueCount_le_k_sq : ∀ ω : Ω, blueCount ω ≤ k ^ 2 := by
    intro ω
    let X : Finset (Fin m) := I.image (TwoBiteBlueProjection ω)
    have hX_le_k : X.card ≤ k := by
      dsimp [X]
      rw [← hI]
      exact Finset.card_image_le
    have hX_sq_le_k_sq : X.card ^ 2 ≤ k ^ 2 :=
      Nat.pow_le_pow_left hX_le_k 2
    exact le_trans (blueCount_le_base ω)
      (le_trans (hBasePairs_card_le_sq X) hX_sq_le_k_sq)
  have redCount_lt_k_sq_of_pos :
      ∀ ω : Ω, k ≠ 0 → redCount ω < k ^ 2 := by
    intro ω hk
    let X : Finset (Fin m) := I.image (TwoBiteRedProjection ω)
    have hI_nonempty : I.Nonempty := by
      exact Finset.card_pos.mp (by
        rw [hI]
        exact Nat.pos_of_ne_zero hk)
    have hX_nonempty : X.Nonempty := by
      rcases hI_nonempty with ⟨x, hx⟩
      exact ⟨TwoBiteRedProjection ω x,
        Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
    have hX_le_k : X.card ≤ k := by
      dsimp [X]
      rw [← hI]
      exact Finset.card_image_le
    have hX_sq_le_k_sq : X.card ^ 2 ≤ k ^ 2 :=
      Nat.pow_le_pow_left hX_le_k 2
    exact lt_of_lt_of_le
      (lt_of_le_of_lt (redCount_le_base ω)
        (hBasePairs_card_lt_sq X hX_nonempty))
      hX_sq_le_k_sq
  have blueCount_lt_k_sq_of_pos :
      ∀ ω : Ω, k ≠ 0 → blueCount ω < k ^ 2 := by
    intro ω hk
    let X : Finset (Fin m) := I.image (TwoBiteBlueProjection ω)
    have hI_nonempty : I.Nonempty := by
      exact Finset.card_pos.mp (by
        rw [hI]
        exact Nat.pos_of_ne_zero hk)
    have hX_nonempty : X.Nonempty := by
      rcases hI_nonempty with ⟨x, hx⟩
      exact ⟨TwoBiteBlueProjection ω x,
        Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
    have hX_le_k : X.card ≤ k := by
      dsimp [X]
      rw [← hI]
      exact Finset.card_image_le
    have hX_sq_le_k_sq : X.card ^ 2 ≤ k ^ 2 :=
      Nat.pow_le_pow_left hX_le_k 2
    exact lt_of_lt_of_le
      (lt_of_le_of_lt (blueCount_le_base ω)
        (hBasePairs_card_lt_sq X hX_nonempty))
      hX_sq_le_k_sq
  have redCount_lt_N : ∀ ω : Ω, redCount ω < N := by
    intro ω
    by_cases hk : k = 0
    · have hzero : redCount ω = 0 := by
        exact Nat.eq_zero_of_le_zero (by
          simpa [hk] using redCount_le_k_sq ω)
      simp [N, hk, hzero]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hN : N = k ^ 2 := by
        have h1le : 1 ≤ k ^ 2 :=
          Nat.succ_le_of_lt (pow_pos hkpos 2)
        exact max_eq_right h1le
      simpa [N, hN] using redCount_lt_k_sq_of_pos ω hk
  have blueCount_lt_N : ∀ ω : Ω, blueCount ω < N := by
    intro ω
    by_cases hk : k = 0
    · have hzero : blueCount ω = 0 := by
        exact Nat.eq_zero_of_le_zero (by
          simpa [hk] using blueCount_le_k_sq ω)
      simp [N, hk, hzero]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hN : N = k ^ 2 := by
        have h1le : 1 ≤ k ^ 2 :=
          Nat.succ_le_of_lt (pow_pos hkpos 2)
        exact max_eq_right h1le
      simpa [N, hN] using blueCount_lt_k_sq_of_pos ω hk
  have hidx_card_bound :
      (idx.card : ℝ) ≤ max (1 : ℝ) ((k : ℝ) ^ 4) := by
    have hidx_card_nat : idx.card = N * N := by
      simp [idx]
    by_cases hk : k = 0
    · have hN : N = 1 := by
        simp [N, hk]
      have hidx : idx.card = 1 := by
        simp [hidx_card_nat, hN]
      norm_num [hidx, hk]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hN : N = k ^ 2 := by
        have h1le : 1 ≤ k ^ 2 :=
          Nat.succ_le_of_lt (pow_pos hkpos 2)
        exact max_eq_right h1le
      have hidx : idx.card = k ^ 4 := by
        rw [hidx_card_nat, hN]
        ring
      have hk_one_real : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt hkpos)
      have hpow_ge_one : (1 : ℝ) ≤ (k : ℝ) ^ 4 := by
        simpa using
          (pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hk_one_real 4)
      have hidx_real : (idx.card : ℝ) = (k : ℝ) ^ 4 := by
        norm_num [hidx]
      simp [hidx_real, max_eq_right hpow_ge_one]
  have hfactor_nonneg :
      0 ≤ max (1 : ℝ) ((k : ℝ) ^ 4) :=
    le_trans zero_le_one (le_max_left _ _)
  by_cases hden : prob hist = 0
  · have hcond_zero :
        TwoBiteConditionalProbability n m p target hist = 0 := by
      simp [TwoBiteConditionalProbability, prob, hden]
    have hrhs_nonneg :
        0 ≤ max (1 : ℝ) ((k : ℝ) ^ 4) * C :=
      mul_nonneg hfactor_nonneg hC
    simpa [hcond_zero] using hrhs_nonneg
  · have hden_pos : 0 < prob hist :=
      lt_of_le_of_ne (prob_nonneg hist) (Ne.symm hden)
    have htarget_subset :
        ∀ ω : Ω, target ω ∧ hist ω →
          ∃ ij ∈ idx, cellWithHist ij ω := by
      intro ω hω
      let ij : ℕ × ℕ := (redCount ω, blueCount ω)
      have hij : ij ∈ idx := by
        simp [idx, ij, redCount_lt_N ω, blueCount_lt_N ω]
      refine ⟨ij, hij, ?_⟩
      simp [cellWithHist, cellEvent, ij, hω]
    have hnum_union :
        prob (fun ω : Ω => target ω ∧ hist ω) ≤
          prob (fun ω : Ω => ∃ ij ∈ idx, cellWithHist ij ω) :=
      prob_mono htarget_subset
    have hunion_sum :
        prob (fun ω : Ω => ∃ ij ∈ idx, cellWithHist ij ω) ≤
          idx.sum (fun ij => prob (cellWithHist ij)) :=
      prob_union_bound idx cellWithHist
    have hcell_num_bound :
        ∀ ij ∈ idx, prob (cellWithHist ij) ≤ C * prob hist := by
      intro ij hij
      have hcond := hcell ij.1 ij.2
      have hdiv :
          prob (cellWithHist ij) / prob hist ≤ C := by
        simpa [cellWithHist, cellEvent, redCount, blueCount, prob,
          TwoBiteConditionalProbability, hden, and_assoc, and_left_comm,
          and_comm] using hcond
      have hmul := (div_le_iff₀ hden_pos).mp hdiv
      simpa [mul_comm] using hmul
    have hsum_bound :
        idx.sum (fun ij => prob (cellWithHist ij)) ≤
          idx.sum (fun _ij => C * prob hist) :=
      Finset.sum_le_sum (by
        intro ij hij
        exact hcell_num_bound ij hij)
    have hsum_const :
        idx.sum (fun _ij => C * prob hist) =
          (idx.card : ℝ) * (C * prob hist) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hnum_bound :
        prob (fun ω : Ω => target ω ∧ hist ω) ≤
          (idx.card : ℝ) * (C * prob hist) := by
      linarith
    have htarget_cond_le_idx :
        TwoBiteConditionalProbability n m p target hist ≤ (idx.card : ℝ) * C := by
      have hnum_bound' :
          prob (fun ω : Ω => target ω ∧ hist ω) ≤
            ((idx.card : ℝ) * C) * prob hist := by
        convert hnum_bound using 1
        ring
      have hdiv :
          prob (fun ω : Ω => target ω ∧ hist ω) / prob hist ≤
            (idx.card : ℝ) * C :=
        (div_le_iff₀ hden_pos).mpr hnum_bound'
      simpa [TwoBiteConditionalProbability, prob, hden] using hdiv
    have hidx_mul :
        (idx.card : ℝ) * C ≤ max (1 : ℝ) ((k : ℝ) ^ 4) * C :=
      mul_le_mul_of_nonneg_right hidx_card_bound hC
    exact le_trans htarget_cond_le_idx hidx_mul
