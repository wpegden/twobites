import Mathlib.Tactic
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalIndependenceScale

-- [TABLET NODE: MediumClosedPairsNaturalTailHypotheses]

theorem MediumClosedPairsNaturalTailHypotheses
    {α : Type} [DecidableEq α]
    (ε : ℝ) (n : ℕ) (BR BB : Finset α) :
    let K := TwoBiteNaturalIndependenceScale (1 + ε) n
    let p := TwoBiteEdgeProbability (1 / 2 : ℝ) n
    let A := (K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) /
      (6 * (Real.log (n : ℝ)) ^ 2)
    0 < (n : ℝ) →
    0 < Real.log (n : ℝ) →
    0 < ε →
    ε < 1 →
    ((BR.card + BB.card : ℝ) ≤
      (3 / 2 : ℝ) * (K : ℝ) *
        Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε)) →
    ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (K : ℝ)) →
    p * (K : ℝ) ≤ (1 + ε) * Real.log (n : ℝ) →
    36 * Real.exp 1 * (1 + ε) * (Real.log (n : ℝ)) ^ 3 ≤
      Real.rpow (n : ℝ) (2 * ε) →
    24 * (Real.log (n : ℝ)) ^ 2 ≤
      (1 + ε) * Real.sqrt (Real.log (n : ℝ)) * Real.rpow (n : ℝ) ε →
    0 < A ∧
      0 ≤ p ∧
      p * (((BR.card + BB.card) * K : ℕ) : ℝ) ≤ A / (4 * Real.exp 1) ∧
      Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε) ≤ A / 4 := by
-- BODY
  intro K p A hn_pos hL_pos hε_pos hε_lt_one hsize hK_lower hpK hmean_absorb
    htail_absorb
  have hK_nonneg : 0 ≤ (K : ℝ) := by exact_mod_cast (Nat.zero_le K)
  have hK_pos : 0 < (K : ℝ) := by
    have hcoef_pos : 0 < 1 + ε := by linarith
    have hprod_pos : 0 < (n : ℝ) * Real.log (n : ℝ) := mul_pos hn_pos hL_pos
    have hsqrt_pos : 0 < Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
      Real.sqrt_pos.2 hprod_pos
    exact lt_of_lt_of_le (mul_pos hcoef_pos hsqrt_pos) hK_lower
  have hp0 : 0 ≤ p := by
    dsimp [p, TwoBiteEdgeProbability]
    positivity
  have hr1_pos : 0 < Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) :=
    Real.rpow_pos_of_pos hn_pos _
  have hden_pos : 0 < 6 * (Real.log (n : ℝ)) ^ 2 := by positivity
  have hApos : 0 < A := by
    dsimp [A]
    exact div_pos (mul_pos hK_pos hr1_pos) hden_pos
  have hmean :
      p * (((BR.card + BB.card) * K : ℕ) : ℝ) ≤ A / (4 * Real.exp 1) := by
    let L := Real.log (n : ℝ)
    let x := (n : ℝ)
    let rsmall := Real.rpow x ((1 / 4 : ℝ) - 3 * ε)
    let rmain := Real.rpow x ((1 / 4 : ℝ) - ε)
    let epow := Real.rpow x (2 * ε)
    have hLpos' : 0 < L := by simpa [L] using hL_pos
    have hrsmall_nonneg : 0 ≤ rsmall := by
      dsimp [rsmall, x]
      exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hden_mean_pos : 0 < 24 * Real.exp 1 * L ^ 2 := by
      positivity
    have hprod_cast :
        (((BR.card + BB.card) * K : ℕ) : ℝ) =
          (BR.card + BB.card : ℝ) * (K : ℝ) := by
      norm_num
    have hsizeK :
        (BR.card + BB.card : ℝ) * (K : ℝ) ≤
          ((3 / 2 : ℝ) * (K : ℝ) * rsmall) * (K : ℝ) := by
      exact mul_le_mul_of_nonneg_right (by simpa [rsmall, x] using hsize) hK_nonneg
    have hmean_size :
        p * (((BR.card + BB.card) * K : ℕ) : ℝ) ≤
          p * (((3 / 2 : ℝ) * (K : ℝ) * rsmall) * (K : ℝ)) := by
      rw [hprod_cast]
      exact mul_le_mul_of_nonneg_left hsizeK hp0
    have hrmain_eq : rmain = rsmall * epow := by
      dsimp [rmain, rsmall, epow, x]
      calc
        Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) =
            Real.rpow (n : ℝ) (((1 / 4 : ℝ) - 3 * ε) + 2 * ε) := by
          congr 1
          ring
        _ = Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) *
            Real.rpow (n : ℝ) (2 * ε) := by
          exact Real.rpow_add hn_pos ((1 / 4 : ℝ) - 3 * ε) (2 * ε)
    have hbound_num :
        24 * Real.exp 1 * L ^ 2 *
            (p * (((3 / 2 : ℝ) * (K : ℝ) * rsmall) * (K : ℝ))) ≤
          (K : ℝ) * rmain := by
      have hmul1 :
          p * (((3 / 2 : ℝ) * (K : ℝ) * rsmall) * (K : ℝ)) =
            ((3 / 2 : ℝ) * rsmall * (K : ℝ)) * (p * (K : ℝ)) := by
        ring
      rw [hmul1]
      have hright_nonneg : 0 ≤ (3 / 2 : ℝ) * rsmall * (K : ℝ) := by positivity
      have hpk_scaled :
          ((3 / 2 : ℝ) * rsmall * (K : ℝ)) * (p * (K : ℝ)) ≤
            ((3 / 2 : ℝ) * rsmall * (K : ℝ)) *
              ((1 + ε) * L) := by
        exact mul_le_mul_of_nonneg_left (by simpa [L] using hpK) hright_nonneg
      have hscale_nonneg : 0 ≤ 24 * Real.exp 1 * L ^ 2 := by positivity
      calc
        24 * Real.exp 1 * L ^ 2 *
            (((3 / 2 : ℝ) * rsmall * (K : ℝ)) * (p * (K : ℝ)))
            ≤ 24 * Real.exp 1 * L ^ 2 *
              (((3 / 2 : ℝ) * rsmall * (K : ℝ)) * ((1 + ε) * L)) := by
              exact mul_le_mul_of_nonneg_left hpk_scaled hscale_nonneg
        _ = (K : ℝ) * rsmall *
              (36 * Real.exp 1 * (1 + ε) * L ^ 3) := by ring
        _ ≤ (K : ℝ) * rsmall * epow := by
              have habs : 36 * Real.exp 1 * (1 + ε) * L ^ 3 ≤ epow := by
                simpa [L, epow, x] using hmean_absorb
              exact mul_le_mul_of_nonneg_left habs
                (mul_nonneg hK_nonneg hrsmall_nonneg)
        _ = (K : ℝ) * rmain := by rw [hrmain_eq]; ring
    have htarget_big :
        p * (((3 / 2 : ℝ) * (K : ℝ) * rsmall) * (K : ℝ)) ≤
          ((K : ℝ) * rmain) / (24 * Real.exp 1 * L ^ 2) := by
      rw [le_div_iff₀ hden_mean_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hbound_num
    have hA_div :
        A / (4 * Real.exp 1) =
          ((K : ℝ) * rmain) / (24 * Real.exp 1 * L ^ 2) := by
      dsimp [A, rmain, L, x]
      field_simp [ne_of_gt (Real.exp_pos 1), ne_of_gt hLpos']
      ring
    exact le_trans hmean_size (by simpa [hA_div] using htarget_big)
  have htail : Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε) ≤ A / 4 := by
    let L := Real.log (n : ℝ)
    let x := (n : ℝ)
    let rtail := Real.rpow x ((3 / 4 : ℝ) - 2 * ε)
    let rmain := Real.rpow x ((1 / 4 : ℝ) - ε)
    let epow := Real.rpow x ε
    have hLpos' : 0 < L := by simpa [L] using hL_pos
    have hrtail_nonneg : 0 ≤ rtail := by
      dsimp [rtail, x]
      exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hden_tail_pos : 0 < 24 * L ^ 2 := by positivity
    have hsqrt_mul :
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) =
          Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ)) := by
      exact Real.sqrt_mul (le_of_lt hn_pos) (Real.log (n : ℝ))
    have hsqrt_rmain_eq : Real.sqrt x * rmain = epow * rtail := by
      dsimp [rmain, rtail, epow, x]
      have hsqrt_eq : Real.sqrt (n : ℝ) = Real.rpow (n : ℝ) (1 / 2 : ℝ) := by
        simpa using Real.sqrt_eq_rpow (n : ℝ)
      calc
        Real.sqrt (n : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) =
            Real.rpow (n : ℝ) (1 / 2 : ℝ) *
              Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) := by
          rw [hsqrt_eq]
        _ = Real.rpow (n : ℝ) ((1 / 2 : ℝ) + ((1 / 4 : ℝ) - ε)) := by
          exact (Real.rpow_add hn_pos (1 / 2 : ℝ) ((1 / 4 : ℝ) - ε)).symm
        _ = Real.rpow (n : ℝ) (ε + ((3 / 4 : ℝ) - 2 * ε)) := by
          congr 1
          ring
        _ = Real.rpow (n : ℝ) ε *
            Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε) := by
          exact Real.rpow_add hn_pos ε ((3 / 4 : ℝ) - 2 * ε)
    have htail_num :
        24 * L ^ 2 * rtail ≤ (K : ℝ) * rmain := by
      have habs :
          24 * L ^ 2 ≤ (1 + ε) * Real.sqrt L * epow := by
        simpa [L, epow, x] using htail_absorb
      have hscaled :
          24 * L ^ 2 * rtail ≤ ((1 + ε) * Real.sqrt L * epow) * rtail :=
        mul_le_mul_of_nonneg_right habs hrtail_nonneg
      have hbridge :
          ((1 + ε) * Real.sqrt L * epow) * rtail ≤ (K : ℝ) * rmain := by
        have hleft_eq :
            ((1 + ε) * Real.sqrt L * epow) * rtail =
              ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) *
                rmain := by
          dsimp [L, epow, rtail, rmain, x]
          rw [hsqrt_mul]
          have hpow := hsqrt_rmain_eq
          dsimp [x, rmain, epow, rtail] at hpow
          calc
            (1 + ε) * √(Real.log ↑n) * ↑n ^ ε * ↑n ^ (3 / 4 - 2 * ε) =
                (1 + ε) * √(Real.log ↑n) *
                  (↑n ^ ε * ↑n ^ (3 / 4 - 2 * ε)) := by ring
            _ = (1 + ε) * √(Real.log ↑n) *
                  (√↑n * ↑n ^ (1 / 4 - ε)) := by rw [← hpow]
            _ = (1 + ε) * (√↑n * √(Real.log ↑n)) * ↑n ^ (1 / 4 - ε) := by
              ring
        rw [hleft_eq]
        exact mul_le_mul_of_nonneg_right hK_lower (le_of_lt hr1_pos)
      exact le_trans hscaled hbridge
    have htarget :
        rtail ≤ ((K : ℝ) * rmain) / (24 * L ^ 2) := by
      rw [le_div_iff₀ hden_tail_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using htail_num
    have hA_four :
        A / 4 = ((K : ℝ) * rmain) / (24 * L ^ 2) := by
      dsimp [A, rmain, L, x]
      field_simp [ne_of_gt hLpos']
      ring
    simpa [rtail, x, hA_four] using htarget
  exact ⟨hApos, hp0, hmean, htail⟩
