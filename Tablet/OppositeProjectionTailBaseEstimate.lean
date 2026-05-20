import Tablet.Preamble
import Mathlib.Tactic

-- [TABLET NODE: OppositeProjectionTailBaseEstimate]

theorem OppositeProjectionTailBaseEstimate (L N M T V q : ℝ)
    (hL : 0 < L) (hN : 0 < N)
    (hM : N / (2 * L ^ 2) ≤ M)
    (hT : 100 * L ^ 3 ≤ T)
    (hVq : V * q ≤ L * N) :
    Real.exp 1 * V * q / (T * M) ≤ Real.exp 1 / 50 := by
-- BODY
  have hLsq_pos : 0 < L ^ 2 := sq_pos_of_pos hL
  have hLN_pos : 0 < L * N := mul_pos hL hN
  have hM_pos : 0 < M := by
    have hlower_pos : 0 < N / (2 * L ^ 2) := by positivity
    exact lt_of_lt_of_le hlower_pos hM
  have hT_pos : 0 < T := by
    have hlower_pos : 0 < 100 * L ^ 3 := by positivity
    exact lt_of_lt_of_le hlower_pos hT
  have hden_lower : 50 * (L * N) ≤ T * M := by
    have hprod :=
      mul_le_mul hT hM (by positivity : 0 ≤ N / (2 * L ^ 2)) hT_pos.le
    have hrewrite : (100 * L ^ 3) * (N / (2 * L ^ 2)) = 50 * (L * N) := by
      field_simp [ne_of_gt hL, ne_of_gt hLsq_pos]
      ring
    simpa [hrewrite] using hprod
  have hden_pos : 0 < T * M := mul_pos hT_pos hM_pos
  have hsmall_den_pos : 0 < 50 * (L * N) := by positivity
  have hnum_le : Real.exp 1 * (V * q) ≤ Real.exp 1 * (L * N) :=
    mul_le_mul_of_nonneg_left hVq (Real.exp_pos 1).le
  calc
    Real.exp 1 * V * q / (T * M)
        = Real.exp 1 * (V * q) / (T * M) := by ring
    _ ≤ Real.exp 1 * (L * N) / (T * M) :=
        div_le_div_of_nonneg_right hnum_le hden_pos.le
    _ ≤ Real.exp 1 * (L * N) / (50 * (L * N)) :=
        div_le_div_of_nonneg_left (by positivity) hsmall_den_pos hden_lower
    _ = Real.exp 1 / 50 := by
        field_simp [ne_of_gt hLN_pos]

