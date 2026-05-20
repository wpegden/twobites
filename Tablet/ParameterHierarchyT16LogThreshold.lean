import Tablet.ParameterHierarchyT9LogThreshold
import Tablet.ParameterHierarchyT16Algebra

-- [TABLET NODE: ParameterHierarchyT16LogThreshold]

theorem ParameterHierarchyT16LogThreshold :
    ∀ ε2 : ℝ, 0 < ε2 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
        let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
        let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
        0 < (n : ℝ) →
        0 < L →
        0 < Real.log L →
        2 * p * m ≤ Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ) →
        2 * p * m ≤ (ε2 / 100) * t1 := by
-- BODY
  intro ε2 hε2
  have hε2_div_five_pos : 0 < ε2 / 5 := by positivity
  obtain ⟨n0, hT9⟩ := ParameterHierarchyT9LogThreshold (ε2 / 5) hε2_div_five_pos
  refine ⟨n0, ?_⟩
  intro n hn
  dsimp
  let L := Real.log (n : ℝ)
  let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
  let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
  let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
  have hraw :
      2 * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 2 ≤
        (ε2 / 5) / 10 := by
    simpa using hT9 n hn
  have hthreshold : Real.log L / L ^ 2 ≤ ε2 / 100 := by
    dsimp [L]
    have hraw' :
        2 * (Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 2) ≤ ε2 / 50 := by
      calc
        2 * (Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 2) =
            2 * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 2 := by
          ring
        _ ≤ (ε2 / 5) / 10 := hraw
        _ = ε2 / 50 := by ring
    calc
      Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 2 =
          (2 * (Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ 2)) / 2 := by
        ring
      _ ≤ (ε2 / 50) / 2 :=
        div_le_div_of_nonneg_right hraw' (by norm_num : (0 : ℝ) ≤ 2)
      _ = ε2 / 100 := by ring
  intro hn_pos hL_pos hlogL_pos hmass
  simpa only [L, m, p, t1] using
    ParameterHierarchyT16Algebra ε2 n hn_pos hL_pos hlogL_pos hmass hthreshold
