import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyConstantBounds]

theorem ParameterHierarchyConstantBounds :
    ∀ ε : ℝ, 0 < ε →
      let eps := min (ε / 2) (1 / 32 : ℝ)
      let eps1 := (1 / 2 : ℝ) *
        min eps (min (((eps ^ 3) / 32) ^ 2) (eps ^ 3 / 40))
      let eps2 := (1 / 2 : ℝ) * min eps1 (min (eps1 / 30) (1 : ℝ))
      0 < eps ∧ eps < ε ∧ eps ≤ ε ∧
        0 < eps2 ∧ eps2 < eps1 ∧ eps1 < eps ∧ eps < 1 ∧
          eps < (1 / 16 : ℝ) ∧
        3 * eps2 ≤ eps1 / 10 ∧
        8 * Real.sqrt eps1 + 10 * eps1 ≤ eps ^ 3 / 2 := by
-- BODY
  intro ε hε
  let eps : ℝ := min (ε / 2) (1 / 32 : ℝ)
  let eps1 : ℝ := (1 / 2 : ℝ) *
    min eps (min (((eps ^ 3) / 32) ^ 2) (eps ^ 3 / 40))
  let eps2 : ℝ := (1 / 2 : ℝ) * min eps1 (min (eps1 / 30) (1 : ℝ))
  have heps_pos : 0 < eps := by
    dsimp [eps]
    exact lt_min (by positivity) (by norm_num)
  have heps_le_half : eps ≤ ε / 2 := by
    dsimp [eps]
    exact min_le_left _ _
  have heps_le_const : eps ≤ (1 / 32 : ℝ) := by
    dsimp [eps]
    exact min_le_right _ _
  have heps_lt_eps : eps < ε := by
    nlinarith [heps_le_half, hε]
  have heps_le_eps : eps ≤ ε := le_of_lt heps_lt_eps
  have heps_lt_one : eps < 1 := by
    nlinarith [heps_le_const]
  have heps_lt_sixteen : eps < (1 / 16 : ℝ) := by
    nlinarith [heps_le_const]
  have hsquare_entry_pos : 0 < ((eps ^ 3) / 32) ^ 2 := by
    exact pow_pos (by positivity) 2
  have hthird_entry_pos : 0 < eps ^ 3 / 40 := by
    positivity
  have hmin1_pos :
      0 < min eps (min (((eps ^ 3) / 32) ^ 2) (eps ^ 3 / 40)) := by
    exact lt_min heps_pos (lt_min hsquare_entry_pos hthird_entry_pos)
  have heps1_pos : 0 < eps1 := by
    dsimp [eps1]
    exact mul_pos (by norm_num) hmin1_pos
  have hmin1_le_eps :
      min eps (min (((eps ^ 3) / 32) ^ 2) (eps ^ 3 / 40)) ≤ eps :=
    min_le_left _ _
  have hmin1_le_square :
      min eps (min (((eps ^ 3) / 32) ^ 2) (eps ^ 3 / 40)) ≤
        ((eps ^ 3) / 32) ^ 2 := by
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hmin1_le_third :
      min eps (min (((eps ^ 3) / 32) ^ 2) (eps ^ 3 / 40)) ≤
        eps ^ 3 / 40 := by
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have heps1_le_half_eps : eps1 ≤ (1 / 2 : ℝ) * eps := by
    dsimp [eps1]
    exact mul_le_mul_of_nonneg_left hmin1_le_eps (by norm_num)
  have heps1_lt_eps : eps1 < eps := by
    nlinarith [heps1_le_half_eps, heps_pos]
  have heps1_le_min1 :
      eps1 ≤ min eps (min (((eps ^ 3) / 32) ^ 2) (eps ^ 3 / 40)) := by
    dsimp [eps1]
    nlinarith [hmin1_pos]
  have heps1_le_square : eps1 ≤ ((eps ^ 3) / 32) ^ 2 :=
    le_trans heps1_le_min1 hmin1_le_square
  have heps1_le_third : eps1 ≤ eps ^ 3 / 40 :=
    le_trans heps1_le_min1 hmin1_le_third
  have hmin2_pos : 0 < min eps1 (min (eps1 / 30) (1 : ℝ)) := by
    exact lt_min heps1_pos (lt_min (by positivity) (by norm_num))
  have heps2_pos : 0 < eps2 := by
    dsimp [eps2]
    exact mul_pos (by norm_num) hmin2_pos
  have hmin2_le_eps1 : min eps1 (min (eps1 / 30) (1 : ℝ)) ≤ eps1 :=
    min_le_left _ _
  have hmin2_le_eps1_div30 : min eps1 (min (eps1 / 30) (1 : ℝ)) ≤ eps1 / 30 := by
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have heps2_le_half_eps1 : eps2 ≤ (1 / 2 : ℝ) * eps1 := by
    dsimp [eps2]
    exact mul_le_mul_of_nonneg_left hmin2_le_eps1 (by norm_num)
  have heps2_lt_eps1 : eps2 < eps1 := by
    nlinarith [heps2_le_half_eps1, heps1_pos]
  have heps2_le_eps1_div60 : eps2 ≤ eps1 / 60 := by
    dsimp [eps2]
    have h := mul_le_mul_of_nonneg_left hmin2_le_eps1_div30
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith [h]
  have hthree_eps2 : 3 * eps2 ≤ eps1 / 10 := by
    nlinarith [heps2_le_eps1_div60, heps1_pos]
  have hsqrt_le : Real.sqrt eps1 ≤ eps ^ 3 / 32 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · exact heps1_le_square
  have height_sqrt : 8 * Real.sqrt eps1 ≤ eps ^ 3 / 4 := by
    nlinarith [hsqrt_le]
  have hten_eps1 : 10 * eps1 ≤ eps ^ 3 / 4 := by
    nlinarith [heps1_le_third]
  have hfinal : 8 * Real.sqrt eps1 + 10 * eps1 ≤ eps ^ 3 / 2 := by
    nlinarith [height_sqrt, hten_eps1]
  exact ⟨heps_pos, heps_lt_eps, heps_le_eps, heps2_pos, heps2_lt_eps1,
    heps1_lt_eps, heps_lt_one, heps_lt_sixteen, hthree_eps2, hfinal⟩
