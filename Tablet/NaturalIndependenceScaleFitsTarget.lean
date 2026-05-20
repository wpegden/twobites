import Tablet.NaturalScaleGapEventually
import Tablet.NaturalParameterApproximation
import Tablet.TwoBiteIndependenceScale
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteReducedVertexCount

-- [TABLET NODE: NaturalIndependenceScaleFitsTarget]

theorem NaturalIndependenceScaleFitsTarget :
    ∀ ε η : ℝ, 0 < η → η < ε →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        (TwoBiteNaturalIndependenceScale (1 + η) n : ℝ) <
          TwoBiteIndependenceScale (1 + ε) n := by
-- BODY
  intro ε η hη hηε
  have hδ : 0 < ε - η := sub_pos.mpr hηε
  obtain ⟨nGap, hnGap⟩ := NaturalScaleGapEventually (ε - η) hδ
  refine ⟨max 2 nGap, ?_⟩
  intro n hn
  have htwo : 2 ≤ n := le_trans (Nat.le_max_left 2 nGap) hn
  have hgap_ge : nGap ≤ n := le_trans (Nat.le_max_right 2 nGap) hn
  have hgap := hnGap n hgap_ge
  have hn_gt_one_nat : 1 < n := Nat.lt_of_lt_of_le (by decide) htwo
  have hn_gt_one_real : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn_gt_one_nat
  have hn_pos_real : 0 < (n : ℝ) := lt_trans zero_lt_one hn_gt_one_real
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_gt_one_real
  have hstretch_pos : 0 < TwoBiteStretch n := by
    unfold TwoBiteStretch
    exact pow_pos hlog_pos 2
  have hm_nonneg : 0 ≤ TwoBiteReducedVertexCount n := by
    unfold TwoBiteReducedVertexCount
    exact div_nonneg hn_pos_real.le hstretch_pos.le
  have hk_nonneg : 0 ≤ TwoBiteIndependenceScale (1 + η) n := by
    unfold TwoBiteIndependenceScale
    exact mul_nonneg (by linarith [hη]) (Real.sqrt_nonneg _)
  have hround := NaturalParameterApproximation (1 + η) n hm_nonneg hk_nonneg
  have hceil_lt :
      (TwoBiteNaturalIndependenceScale (1 + η) n : ℝ) <
        TwoBiteIndependenceScale (1 + η) n + 1 := hround.2.2.2
  have hscale_gap :
      TwoBiteIndependenceScale (1 + η) n + 1 <
        TwoBiteIndependenceScale (1 + ε) n := by
    unfold TwoBiteIndependenceScale
    calc
      (1 + η) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) + 1
          < (1 + η) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) +
              (ε - η) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_lt_add_left hgap
            ((1 + η) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
      _ = (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by ring
  exact lt_trans hceil_lt hscale_gap
