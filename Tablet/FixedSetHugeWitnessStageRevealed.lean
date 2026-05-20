import Tablet.FiberAndDegreeEvent
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteHugeClass
import Tablet.TwoBiteStageRevealedVertex

-- [TABLET NODE: FixedSetHugeWitnessStageRevealed]

theorem FixedSetHugeWitnessStageRevealed :
    ∀ {n m : ℕ} {p ε ε1 ε2 : ℝ} {n0 : ℕ}
      (ω : TwoBiteSample n m p) (I : Finset (Fin n))
      (x : TwoBiteBaseVertex m),
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      m = TwoBiteNaturalReducedVertexCount n →
      p = (1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) →
      I.card = TwoBiteNaturalIndependenceScale (1 + ε) n →
      FiberAndDegreeEvent ω ε2 →
      TwoBiteHugeClass ω I x →
      TwoBiteStageRevealedVertex ω ε I x := by
-- BODY
  intro n m p ε ε1 ε2 n0 ω I x hComparisons hn hm hp hI hFiber hHuge
  classical
  unfold TwoBiteHugeClass at hHuge
  rcases hHuge with ⟨hHugeLower, hHugeUpper⟩
  unfold TwoBiteStageRevealedVertex
  by_cases hProj : TwoBiteProjectionContains ω I x
  · right
    by_cases hF1 : TwoBiteStageF1 ω I x
    · exact Or.inl hF1
    · right
      by_contra hnotF2
      have hNeighborWeak :
          (((Finset.univ : Finset (TwoBiteBaseVertex m)).filter
            (fun y => TwoBiteStageF1 ω I y ∧
              TwoBiteBaseAdj ω x y)).card : ℝ) ≤
            TwoBiteLargeCutoff ε n / Real.log (n : ℝ) := by
        have hnotLt :
            ¬ TwoBiteLargeCutoff ε n / Real.log (n : ℝ) <
              (((Finset.univ : Finset (TwoBiteBaseVertex m)).filter
                (fun y => TwoBiteStageF1 ω I y ∧
                  TwoBiteBaseAdj ω x y)).card : ℝ) := by
          intro hlt
          exact hnotF2 (by
            unfold TwoBiteStageF2
            exact ⟨hProj, hlt⟩)
        exact le_of_not_gt hnotLt
      have hCompn := hComparisons n hn
      cases x with
      | inl r =>
          dsimp [ParameterHierarchyEventualComparisons] at hCompn
          rcases hCompn with
            ⟨hm_pos, _hp_nonneg, _hp_le, hpm_ge_one, _hkReal_le, _hk_lt,
              _hm_le, _hmReal_lt, _h9, _h10, _h11, _h12, _h13, _h14, _h15,
              _h16, _h17, _h18, _h19, _h20, _heps2_small,
              heps2_nonneg, _heps2_le, _h24, _h25, _h26, _h27, _h28,
              _hLargeHuge, hStageUpper, _h31, _h32, _h33, _h34, _h35,
              _h36⟩
          have hL_pos : 0 < Real.log (n : ℝ) := by
            have hn_pos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le n0) hn
            have hn_real_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
            have hsqrt_nonneg :
                0 ≤ Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) :=
              Real.sqrt_nonneg _
            have hsqrt_pos :
                0 < Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) := by
              by_contra hnot
              have hsqrt_zero :
                  Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) = 0 :=
                le_antisymm (le_of_not_gt hnot) hsqrt_nonneg
              nlinarith only [hpm_ge_one, hm_pos, hsqrt_zero]
            have hratio_pos :
                0 < Real.log (n : ℝ) / (n : ℝ) :=
              Real.sqrt_pos.mp hsqrt_pos
            have hmul_pos :
                0 < (Real.log (n : ℝ) / (n : ℝ)) * (n : ℝ) :=
              mul_pos hratio_pos hn_real_pos
            rwa [div_mul_cancel₀ _ (ne_of_gt hn_real_pos)] at hmul_pos
          have hL_nonneg : 0 ≤ Real.log (n : ℝ) := le_of_lt hL_pos
          dsimp [FiberAndDegreeEvent] at hFiber
          rcases hFiber with
            ⟨hredFiber, _hblueFiber, hredDegree, _hblueDegree,
              _hredPair, _hbluePair, _hliftedDegree, _hredOverlap,
              _hblueOverlap, _hmixedOverlap, _hredOpposite, _hblueOpposite⟩
          let L : ℝ := Real.log (n : ℝ)
          let M : ℝ := (1 + ε2) * L ^ 2
          have hM_nonneg : 0 ≤ M := by
            have hsq : 0 ≤ L ^ 2 := sq_nonneg L
            nlinarith only [heps2_nonneg, hsq]
          have hredFiberUpper (s : Fin m) :
              ((RedFiber ω s).card : ℝ) ≤ M := by
            have hf := hredFiber s
            unfold WithinRelativeError at hf
            have hdiff :
                ((RedFiber ω s).card : ℝ) - L ^ 2 ≤ ε2 * L ^ 2 := by
              simpa [L] using le_trans (le_abs_self _) hf
            nlinarith only [hdiff]
          have hredDegreeUpper :
              (GraphDegreeCount (TwoBiteRedGraph ω) r : ℝ) ≤
                (1 + ε2) * (p * (m : ℝ)) := by
            have hd := hredDegree r
            unfold WithinRelativeError at hd
            have hdiff :
                (GraphDegreeCount (TwoBiteRedGraph ω) r : ℝ) -
                    p * (m : ℝ) ≤ ε2 * (p * (m : ℝ)) := by
              simpa [L, hp, hm] using le_trans (le_abs_self _) hd
            nlinarith only [hdiff]
          let X : Finset (Fin n) := TwoBiteX ω I (Sum.inl r)
          let A : Finset (Fin n) :=
            X.filter
              (fun v => TwoBiteStageF1 ω I (Sum.inl (TwoBiteRedProjection ω v)))
          let B : Finset (Fin n) :=
            X.filter
              (fun v => ¬
                TwoBiteStageF1 ω I (Sum.inl (TwoBiteRedProjection ω v)))
          let Nbase : Finset (TwoBiteBaseVertex m) :=
            (Finset.univ : Finset (TwoBiteBaseVertex m)).filter
              (fun y => TwoBiteStageF1 ω I y ∧
                TwoBiteBaseAdj ω (Sum.inl r) y)
          let redFiberFor : TwoBiteBaseVertex m → Finset (Fin n) :=
            fun y =>
              match y with
              | Sum.inl s => RedFiber ω s
              | Sum.inr _ => ∅
          have hNbaseWeak :
              (Nbase.card : ℝ) ≤ TwoBiteLargeCutoff ε n / L := by
            simpa [Nbase, L] using hNeighborWeak
          have hA_to_sigma :
              A.card ≤ (Nbase.sigma redFiberFor).card := by
            refine Finset.card_le_card_of_injOn
              (fun v : Fin n =>
                (⟨Sum.inl (TwoBiteRedProjection ω v), v⟩ :
                  Sigma fun _ : TwoBiteBaseVertex m => Fin n)) ?_ ?_
            · intro v hv
              have hv' : v ∈ X ∧
                  TwoBiteStageF1 ω I (Sum.inl (TwoBiteRedProjection ω v)) := by
                simpa [A] using hv
              have hvX : v ∈ I ∧
                  (TwoBiteRedGraph ω).Adj r (TwoBiteRedProjection ω v) := by
                simpa [X, TwoBiteX, TwoBiteLiftedNeighborhood] using hv'.1
              exact Finset.mem_sigma.mpr
                ⟨by simp [Nbase, TwoBiteBaseAdj, hv'.2, hvX.2],
                  by simp [redFiberFor, RedFiber]⟩
            · intro v hv w hw hEq
              exact congrArg Sigma.snd hEq
          have hA_le_sum :
              (A.card : ℝ) ≤
                Nbase.sum (fun y => ((redFiberFor y).card : ℝ)) := by
            have hnat :
                A.card ≤ Nbase.sum (fun y => (redFiberFor y).card) := by
              simpa [Finset.card_sigma] using hA_to_sigma
            exact_mod_cast hnat
          have hA_sum_le :
              Nbase.sum (fun y => ((redFiberFor y).card : ℝ)) ≤
                (Nbase.card : ℝ) * M := by
            calc
              Nbase.sum (fun y => ((redFiberFor y).card : ℝ))
                  ≤ Nbase.sum (fun _y => M) := by
                    refine Finset.sum_le_sum ?_
                    intro y hy
                    cases y with
                    | inl s =>
                        simpa [redFiberFor] using hredFiberUpper s
                    | inr b =>
                        simp [Nbase, TwoBiteBaseAdj] at hy
              _ = (Nbase.card : ℝ) * M := by
                    simp [nsmul_eq_mul]
          have hA_bound :
              (A.card : ℝ) ≤ M * (TwoBiteLargeCutoff ε n / L) := by
            have hmul :
                (Nbase.card : ℝ) * M ≤
                  (TwoBiteLargeCutoff ε n / L) * M :=
              mul_le_mul_of_nonneg_right hNbaseWeak hM_nonneg
            nlinarith only [hA_le_sum, hA_sum_le, hmul]
          let Bproj : Finset (Fin m) := B.image (TwoBiteRedProjection ω)
          let redFiberInI : Fin m → Finset (Fin n) :=
            fun s => RedFiber ω s ∩ I
          have hB_to_sigma :
              B.card ≤ (Bproj.sigma redFiberInI).card := by
            refine Finset.card_le_card_of_injOn
              (fun v : Fin n =>
                (⟨TwoBiteRedProjection ω v, v⟩ :
                  Sigma fun _ : Fin m => Fin n)) ?_ ?_
            · intro v hv
              have hv' : v ∈ X ∧
                  ¬ TwoBiteStageF1 ω I
                    (Sum.inl (TwoBiteRedProjection ω v)) := by
                simpa [B] using hv
              have hvX : v ∈ I ∧
                  (TwoBiteRedGraph ω).Adj r (TwoBiteRedProjection ω v) := by
                simpa [X, TwoBiteX, TwoBiteLiftedNeighborhood] using hv'.1
              exact Finset.mem_sigma.mpr
                ⟨Finset.mem_image.mpr ⟨v, hv, rfl⟩,
                  Finset.mem_inter.mpr
                    ⟨by simp [RedFiber], hvX.1⟩⟩
            · intro v hv w hw hEq
              exact congrArg Sigma.snd hEq
          have hB_le_sum :
              (B.card : ℝ) ≤
                Bproj.sum (fun s => ((redFiberInI s).card : ℝ)) := by
            have hnat :
                B.card ≤ Bproj.sum (fun s => (redFiberInI s).card) := by
              simpa [Finset.card_sigma] using hB_to_sigma
            exact_mod_cast hnat
          have hB_fiber_le (s : Fin m) (hs : s ∈ Bproj) :
              ((redFiberInI s).card : ℝ) ≤ L := by
            rcases Finset.mem_image.mp hs with ⟨v, hvB, rfl⟩
            have hv' : v ∈ X ∧
                ¬ TwoBiteStageF1 ω I
                  (Sum.inl (TwoBiteRedProjection ω v)) := by
              simpa [B] using hvB
            have hvX : v ∈ I ∧
                (TwoBiteRedGraph ω).Adj r (TwoBiteRedProjection ω v) := by
              simpa [X, TwoBiteX, TwoBiteLiftedNeighborhood] using hv'.1
            have hProjV :
                TwoBiteProjectionContains ω I
                  (Sum.inl (TwoBiteRedProjection ω v)) := by
              unfold TwoBiteProjectionContains
              exact Finset.mem_image.mpr ⟨v, hvX.1, rfl⟩
            have hnotLt :
                ¬ L <
                  (((TwoBiteBaseFiber ω
                    (Sum.inl (TwoBiteRedProjection ω v))) ∩ I).card : ℝ) := by
              intro hlt
              exact hv'.2 (by
                unfold TwoBiteStageF1
                exact ⟨hProjV, by simpa [L] using hlt⟩)
            have hle :
                (((TwoBiteBaseFiber ω
                    (Sum.inl (TwoBiteRedProjection ω v))) ∩ I).card : ℝ) ≤ L :=
              le_of_not_gt hnotLt
            simpa [redFiberInI, TwoBiteBaseFiber] using hle
          have hB_sum_le :
              Bproj.sum (fun s => ((redFiberInI s).card : ℝ)) ≤
                (Bproj.card : ℝ) * L := by
            calc
              Bproj.sum (fun s => ((redFiberInI s).card : ℝ))
                  ≤ Bproj.sum (fun _s => L) := by
                    exact Finset.sum_le_sum hB_fiber_le
              _ = (Bproj.card : ℝ) * L := by
                    simp [nsmul_eq_mul]
          let G : Finset (Fin m) :=
            (Finset.univ : Finset (Fin m)).filter
              (fun s => (TwoBiteRedGraph ω).Adj r s)
          have hBproj_subset_G : Bproj ⊆ G := by
            intro s hs
            rcases Finset.mem_image.mp hs with ⟨v, hvB, rfl⟩
            have hv' : v ∈ X ∧
                ¬ TwoBiteStageF1 ω I
                  (Sum.inl (TwoBiteRedProjection ω v)) := by
              simpa [B] using hvB
            have hvX : v ∈ I ∧
                (TwoBiteRedGraph ω).Adj r (TwoBiteRedProjection ω v) := by
              simpa [X, TwoBiteX, TwoBiteLiftedNeighborhood] using hv'.1
            simpa [G] using hvX.2
          have hBproj_card_le_G :
              (Bproj.card : ℝ) ≤ (G.card : ℝ) := by
            exact_mod_cast Finset.card_le_card hBproj_subset_G
          have hG_card :
              (G.card : ℝ) =
                (GraphDegreeCount (TwoBiteRedGraph ω) r : ℝ) := by
            simp [G, GraphDegreeCount]
          have hB_bound :
              (B.card : ℝ) ≤
                L * ((1 + ε2) * (p * (m : ℝ))) := by
            have h1 :
                (B.card : ℝ) ≤ (Bproj.card : ℝ) * L :=
              le_trans hB_le_sum hB_sum_le
            have h2 :
                (Bproj.card : ℝ) * L ≤ (G.card : ℝ) * L :=
              mul_le_mul_of_nonneg_right hBproj_card_le_G hL_nonneg
            have h3 :
                (G.card : ℝ) * L ≤
                  ((1 + ε2) * (p * (m : ℝ))) * L := by
              rw [hG_card]
              exact mul_le_mul_of_nonneg_right hredDegreeUpper hL_nonneg
            nlinarith only [h1, h2, h3]
          have hsplit_nat : A.card + B.card = X.card := by
            simpa [A, B] using
              (Finset.card_filter_add_card_filter_not
                (s := X)
                (p := fun v =>
                  TwoBiteStageF1 ω I
                    (Sum.inl (TwoBiteRedProjection ω v))))
          have hsplit :
              (X.card : ℝ) = (A.card : ℝ) + (B.card : ℝ) := by
            exact_mod_cast hsplit_nat.symm
          have hX_upper :
              (X.card : ℝ) ≤
                M * (TwoBiteLargeCutoff ε n / L) +
                  L * ((1 + ε2) * (p * (m : ℝ))) := by
            nlinarith only [hA_bound, hB_bound, hsplit]
          have hStageUpper' :
              M * (TwoBiteLargeCutoff ε n / L) +
                  L * ((1 + ε2) * (p * (m : ℝ))) <
                TwoBiteHugeCutoff n := by
            simpa [M, L, TwoBiteLargeCutoff, hp, hm, mul_assoc, mul_left_comm,
              mul_comm] using hStageUpper
          have hX_lt :
              ((TwoBiteX ω I (Sum.inl r)).card : ℝ) <
                TwoBiteHugeCutoff n := by
            simpa [X] using lt_of_le_of_lt hX_upper hStageUpper'
          exact (lt_irrefl _ (lt_trans hHugeLower hX_lt)).elim
      | inr b =>
          dsimp [ParameterHierarchyEventualComparisons] at hCompn
          rcases hCompn with
            ⟨hm_pos, _hp_nonneg, _hp_le, hpm_ge_one, _hkReal_le, _hk_lt,
              _hm_le, _hmReal_lt, _h9, _h10, _h11, _h12, _h13, _h14, _h15,
              _h16, _h17, _h18, _h19, _h20, _heps2_small,
              heps2_nonneg, _heps2_le, _h24, _h25, _h26, _h27, _h28,
              _hLargeHuge, hStageUpper, _h31, _h32, _h33, _h34, _h35,
              _h36⟩
          have hL_pos : 0 < Real.log (n : ℝ) := by
            have hn_pos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le n0) hn
            have hn_real_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
            have hsqrt_nonneg :
                0 ≤ Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) :=
              Real.sqrt_nonneg _
            have hsqrt_pos :
                0 < Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) := by
              by_contra hnot
              have hsqrt_zero :
                  Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) = 0 :=
                le_antisymm (le_of_not_gt hnot) hsqrt_nonneg
              nlinarith only [hpm_ge_one, hm_pos, hsqrt_zero]
            have hratio_pos :
                0 < Real.log (n : ℝ) / (n : ℝ) :=
              Real.sqrt_pos.mp hsqrt_pos
            have hmul_pos :
                0 < (Real.log (n : ℝ) / (n : ℝ)) * (n : ℝ) :=
              mul_pos hratio_pos hn_real_pos
            rwa [div_mul_cancel₀ _ (ne_of_gt hn_real_pos)] at hmul_pos
          have hL_nonneg : 0 ≤ Real.log (n : ℝ) := le_of_lt hL_pos
          dsimp [FiberAndDegreeEvent] at hFiber
          rcases hFiber with
            ⟨_hredFiber, hblueFiber, _hredDegree, hblueDegree,
              _hredPair, _hbluePair, _hliftedDegree, _hredOverlap,
              _hblueOverlap, _hmixedOverlap, _hredOpposite, _hblueOpposite⟩
          let L : ℝ := Real.log (n : ℝ)
          let M : ℝ := (1 + ε2) * L ^ 2
          have hM_nonneg : 0 ≤ M := by
            have hsq : 0 ≤ L ^ 2 := sq_nonneg L
            nlinarith only [heps2_nonneg, hsq]
          have hblueFiberUpper (c : Fin m) :
              ((BlueFiber ω c).card : ℝ) ≤ M := by
            have hf := hblueFiber c
            unfold WithinRelativeError at hf
            have hdiff :
                ((BlueFiber ω c).card : ℝ) - L ^ 2 ≤ ε2 * L ^ 2 := by
              simpa [L] using le_trans (le_abs_self _) hf
            nlinarith only [hdiff]
          have hblueDegreeUpper :
              (GraphDegreeCount (TwoBiteBlueGraph ω) b : ℝ) ≤
                (1 + ε2) * (p * (m : ℝ)) := by
            have hd := hblueDegree b
            unfold WithinRelativeError at hd
            have hdiff :
                (GraphDegreeCount (TwoBiteBlueGraph ω) b : ℝ) -
                    p * (m : ℝ) ≤ ε2 * (p * (m : ℝ)) := by
              simpa [L, hp, hm] using le_trans (le_abs_self _) hd
            nlinarith only [hdiff]
          let X : Finset (Fin n) := TwoBiteX ω I (Sum.inr b)
          let A : Finset (Fin n) :=
            X.filter
              (fun v => TwoBiteStageF1 ω I (Sum.inr (TwoBiteBlueProjection ω v)))
          let B : Finset (Fin n) :=
            X.filter
              (fun v => ¬
                TwoBiteStageF1 ω I (Sum.inr (TwoBiteBlueProjection ω v)))
          let Nbase : Finset (TwoBiteBaseVertex m) :=
            (Finset.univ : Finset (TwoBiteBaseVertex m)).filter
              (fun y => TwoBiteStageF1 ω I y ∧
                TwoBiteBaseAdj ω (Sum.inr b) y)
          let blueFiberFor : TwoBiteBaseVertex m → Finset (Fin n) :=
            fun y =>
              match y with
              | Sum.inl _ => ∅
              | Sum.inr c => BlueFiber ω c
          have hNbaseWeak :
              (Nbase.card : ℝ) ≤ TwoBiteLargeCutoff ε n / L := by
            simpa [Nbase, L] using hNeighborWeak
          have hA_to_sigma :
              A.card ≤ (Nbase.sigma blueFiberFor).card := by
            refine Finset.card_le_card_of_injOn
              (fun v : Fin n =>
                (⟨Sum.inr (TwoBiteBlueProjection ω v), v⟩ :
                  Sigma fun _ : TwoBiteBaseVertex m => Fin n)) ?_ ?_
            · intro v hv
              have hv' : v ∈ X ∧
                  TwoBiteStageF1 ω I (Sum.inr (TwoBiteBlueProjection ω v)) := by
                simpa [A] using hv
              have hvX : v ∈ I ∧
                  (TwoBiteBlueGraph ω).Adj b (TwoBiteBlueProjection ω v) := by
                simpa [X, TwoBiteX, TwoBiteLiftedNeighborhood] using hv'.1
              exact Finset.mem_sigma.mpr
                ⟨by simp [Nbase, TwoBiteBaseAdj, hv'.2, hvX.2],
                  by simp [blueFiberFor, BlueFiber]⟩
            · intro v hv w hw hEq
              exact congrArg Sigma.snd hEq
          have hA_le_sum :
              (A.card : ℝ) ≤
                Nbase.sum (fun y => ((blueFiberFor y).card : ℝ)) := by
            have hnat :
                A.card ≤ Nbase.sum (fun y => (blueFiberFor y).card) := by
              simpa [Finset.card_sigma] using hA_to_sigma
            exact_mod_cast hnat
          have hA_sum_le :
              Nbase.sum (fun y => ((blueFiberFor y).card : ℝ)) ≤
                (Nbase.card : ℝ) * M := by
            calc
              Nbase.sum (fun y => ((blueFiberFor y).card : ℝ))
                  ≤ Nbase.sum (fun _y => M) := by
                    refine Finset.sum_le_sum ?_
                    intro y hy
                    cases y with
                    | inl r =>
                        simp [Nbase, TwoBiteBaseAdj] at hy
                    | inr c =>
                        simpa [blueFiberFor] using hblueFiberUpper c
              _ = (Nbase.card : ℝ) * M := by
                    simp [nsmul_eq_mul]
          have hA_bound :
              (A.card : ℝ) ≤ M * (TwoBiteLargeCutoff ε n / L) := by
            have hmul :
                (Nbase.card : ℝ) * M ≤
                  (TwoBiteLargeCutoff ε n / L) * M :=
              mul_le_mul_of_nonneg_right hNbaseWeak hM_nonneg
            nlinarith only [hA_le_sum, hA_sum_le, hmul]
          let Bproj : Finset (Fin m) := B.image (TwoBiteBlueProjection ω)
          let blueFiberInI : Fin m → Finset (Fin n) :=
            fun c => BlueFiber ω c ∩ I
          have hB_to_sigma :
              B.card ≤ (Bproj.sigma blueFiberInI).card := by
            refine Finset.card_le_card_of_injOn
              (fun v : Fin n =>
                (⟨TwoBiteBlueProjection ω v, v⟩ :
                  Sigma fun _ : Fin m => Fin n)) ?_ ?_
            · intro v hv
              have hv' : v ∈ X ∧
                  ¬ TwoBiteStageF1 ω I
                    (Sum.inr (TwoBiteBlueProjection ω v)) := by
                simpa [B] using hv
              have hvX : v ∈ I ∧
                  (TwoBiteBlueGraph ω).Adj b (TwoBiteBlueProjection ω v) := by
                simpa [X, TwoBiteX, TwoBiteLiftedNeighborhood] using hv'.1
              exact Finset.mem_sigma.mpr
                ⟨Finset.mem_image.mpr ⟨v, hv, rfl⟩,
                  Finset.mem_inter.mpr
                    ⟨by simp [BlueFiber], hvX.1⟩⟩
            · intro v hv w hw hEq
              exact congrArg Sigma.snd hEq
          have hB_le_sum :
              (B.card : ℝ) ≤
                Bproj.sum (fun c => ((blueFiberInI c).card : ℝ)) := by
            have hnat :
                B.card ≤ Bproj.sum (fun c => (blueFiberInI c).card) := by
              simpa [Finset.card_sigma] using hB_to_sigma
            exact_mod_cast hnat
          have hB_fiber_le (c : Fin m) (hc : c ∈ Bproj) :
              ((blueFiberInI c).card : ℝ) ≤ L := by
            rcases Finset.mem_image.mp hc with ⟨v, hvB, rfl⟩
            have hv' : v ∈ X ∧
                ¬ TwoBiteStageF1 ω I
                  (Sum.inr (TwoBiteBlueProjection ω v)) := by
              simpa [B] using hvB
            have hvX : v ∈ I ∧
                (TwoBiteBlueGraph ω).Adj b (TwoBiteBlueProjection ω v) := by
              simpa [X, TwoBiteX, TwoBiteLiftedNeighborhood] using hv'.1
            have hProjV :
                TwoBiteProjectionContains ω I
                  (Sum.inr (TwoBiteBlueProjection ω v)) := by
              unfold TwoBiteProjectionContains
              exact Finset.mem_image.mpr ⟨v, hvX.1, rfl⟩
            have hnotLt :
                ¬ L <
                  (((TwoBiteBaseFiber ω
                    (Sum.inr (TwoBiteBlueProjection ω v))) ∩ I).card : ℝ) := by
              intro hlt
              exact hv'.2 (by
                unfold TwoBiteStageF1
                exact ⟨hProjV, by simpa [L] using hlt⟩)
            have hle :
                (((TwoBiteBaseFiber ω
                    (Sum.inr (TwoBiteBlueProjection ω v))) ∩ I).card : ℝ) ≤ L :=
              le_of_not_gt hnotLt
            simpa [blueFiberInI, TwoBiteBaseFiber] using hle
          have hB_sum_le :
              Bproj.sum (fun c => ((blueFiberInI c).card : ℝ)) ≤
                (Bproj.card : ℝ) * L := by
            calc
              Bproj.sum (fun c => ((blueFiberInI c).card : ℝ))
                  ≤ Bproj.sum (fun _c => L) := by
                    exact Finset.sum_le_sum hB_fiber_le
              _ = (Bproj.card : ℝ) * L := by
                    simp [nsmul_eq_mul]
          let G : Finset (Fin m) :=
            (Finset.univ : Finset (Fin m)).filter
              (fun c => (TwoBiteBlueGraph ω).Adj b c)
          have hBproj_subset_G : Bproj ⊆ G := by
            intro c hc
            rcases Finset.mem_image.mp hc with ⟨v, hvB, rfl⟩
            have hv' : v ∈ X ∧
                ¬ TwoBiteStageF1 ω I
                  (Sum.inr (TwoBiteBlueProjection ω v)) := by
              simpa [B] using hvB
            have hvX : v ∈ I ∧
                (TwoBiteBlueGraph ω).Adj b (TwoBiteBlueProjection ω v) := by
              simpa [X, TwoBiteX, TwoBiteLiftedNeighborhood] using hv'.1
            simpa [G] using hvX.2
          have hBproj_card_le_G :
              (Bproj.card : ℝ) ≤ (G.card : ℝ) := by
            exact_mod_cast Finset.card_le_card hBproj_subset_G
          have hG_card :
              (G.card : ℝ) =
                (GraphDegreeCount (TwoBiteBlueGraph ω) b : ℝ) := by
            simp [G, GraphDegreeCount]
          have hB_bound :
              (B.card : ℝ) ≤
                L * ((1 + ε2) * (p * (m : ℝ))) := by
            have h1 :
                (B.card : ℝ) ≤ (Bproj.card : ℝ) * L :=
              le_trans hB_le_sum hB_sum_le
            have h2 :
                (Bproj.card : ℝ) * L ≤ (G.card : ℝ) * L :=
              mul_le_mul_of_nonneg_right hBproj_card_le_G hL_nonneg
            have h3 :
                (G.card : ℝ) * L ≤
                  ((1 + ε2) * (p * (m : ℝ))) * L := by
              rw [hG_card]
              exact mul_le_mul_of_nonneg_right hblueDegreeUpper hL_nonneg
            nlinarith only [h1, h2, h3]
          have hsplit_nat : A.card + B.card = X.card := by
            simpa [A, B] using
              (Finset.card_filter_add_card_filter_not
                (s := X)
                (p := fun v =>
                  TwoBiteStageF1 ω I
                    (Sum.inr (TwoBiteBlueProjection ω v))))
          have hsplit :
              (X.card : ℝ) = (A.card : ℝ) + (B.card : ℝ) := by
            exact_mod_cast hsplit_nat.symm
          have hX_upper :
              (X.card : ℝ) ≤
                M * (TwoBiteLargeCutoff ε n / L) +
                  L * ((1 + ε2) * (p * (m : ℝ))) := by
            nlinarith only [hA_bound, hB_bound, hsplit]
          have hStageUpper' :
              M * (TwoBiteLargeCutoff ε n / L) +
                  L * ((1 + ε2) * (p * (m : ℝ))) <
                TwoBiteHugeCutoff n := by
            simpa [M, L, TwoBiteLargeCutoff, hp, hm, mul_assoc, mul_left_comm,
              mul_comm] using hStageUpper
          have hX_lt :
              ((TwoBiteX ω I (Sum.inr b)).card : ℝ) <
                TwoBiteHugeCutoff n := by
            simpa [X] using lt_of_le_of_lt hX_upper hStageUpper'
          exact (lt_irrefl _ (lt_trans hHugeLower hX_lt)).elim
  · exact Or.inl hProj
