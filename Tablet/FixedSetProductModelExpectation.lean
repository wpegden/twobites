import Tablet.FixedSetProductModelMassFn
import Tablet.FixedSetProductModelMass
import Tablet.FixedSetProductModelVar
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.RealChooseTwo
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.FixedSetProductModelWeightSum
import Tablet.FixedSetProductModelCoordinateMarginal
import Tablet.FixedSetProductModelPairUnionBound
import Tablet.FixedSetProductModelLinearity

-- [TABLET NODE: FixedSetProductModelExpectation]

open scoped Classical

theorem FixedSetProductModelExpectation {n : ℕ} (I : Finset (Fin n)) (ε ε1 ε2 : ℝ) {n0 : ℕ}
    (h_hier : ParameterHierarchyEventualComparisons ε ε1 ε2 n0)
    (hn0 : n0 < n)
    (hI : I.card = TwoBiteNaturalIndependenceScale (1 + ε) n)
    {m_sub : ℕ} (p_sub : ℝ) (π : Fin n ↪ (Fin m_sub × Fin m_sub))
    (hm : m_sub = TwoBiteNaturalReducedVertexCount n)
    (hp : p_sub = TwoBiteEdgeProbability (1 / 2 : ℝ) n)
    (C L : ℝ) (hC : C = RealChooseTwo (TwoBiteNaturalIndependenceScale (1 + ε) n)) (hL : L = Real.log (n : ℝ)) :
    let r_prod := 2 * m_sub
    let P_R := I.image (fun u => (π u).1)
    let P_B := I.image (fun u => (π u).2)
    let q := FixedSetProductModelMassFn p_sub P_R P_B
    let Z_prod := FixedSetProductModelVar I ε p_sub π
    Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) =>
      (Finset.univ.prod (fun i => q (v i))) * Z_prod v) ≤ C / (2 * L) := by
-- BODY
  have h_comp := h_hier n hn0
  have hp0 : 0 ≤ p_sub := by
    rw [hp]
    exact h_comp.2.1
  have hp1 : p_sub ≤ 1 := by
    rw [hp]
    have h_half : TwoBiteEdgeProbability (1 / 2 : ℝ) n ≤ (1 / 2 : ℝ) := h_comp.2.2.1
    linarith
  have h_bound : 2 * (m_sub : ℝ) * p_sub ^ 2 ≤ 1 / (2 * L) := by
    have hm_ineq : (m_sub : ℝ) ≤ (n : ℝ) / (L ^ 2) := by
      rw [hm, hL]
      exact h_comp.2.2.2.2.2.2.1
    have hp_val : p_sub = (1 / 2 : ℝ) * Real.sqrt (L / n) := by
      rw [hp, hL]
      rfl
    have h_m_pos : 0 < (m_sub : ℝ) := by
      rw [hm]
      exact h_comp.1
    have hn_ge_1 : 1 ≤ n := by omega
    have hn_not_1 : n ≠ 1 := by
      intro hn_eq_1
      have hL_zero : L = 0 := by
        rw [hL, hn_eq_1]
        norm_num
      have hm_le_0 : (m_sub : ℝ) ≤ 0 := by
        calc (m_sub : ℝ) ≤ (n : ℝ) / L ^ 2 := hm_ineq
        _ = (1 : ℝ) / 0 ^ 2 := by rw [hn_eq_1, hL_zero]; norm_num
        _ = 0 := by norm_num
      linarith
    have hn_gt_1 : 1 < n := by omega
    have hn_pos_real : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hn_gt_1_real : (1 : ℝ) < n := by exact_mod_cast hn_gt_1
    have hL_pos : (0 : ℝ) < L := by
      rw [hL]
      exact Real.log_pos hn_gt_1_real
    have h_sq : p_sub ^ 2 = (1 / 4 : ℝ) * (L / n) := by
      rw [hp_val, mul_pow, Real.sq_sqrt]
      · ring
      · exact div_nonneg (le_of_lt hL_pos) (le_of_lt hn_pos_real)
    calc
      2 * (m_sub : ℝ) * p_sub ^ 2
      _ ≤ 2 * ((n : ℝ) / L ^ 2) * p_sub ^ 2 := by
        have h_p2_nonneg : 0 ≤ p_sub ^ 2 := sq_nonneg p_sub
        gcongr
      _ = 2 * ((n : ℝ) / L ^ 2) * (1 / 4 * (L / n)) := by rw [h_sq]
      _ = 1 / (2 * L) := by
        have h_eq : 2 * ((n : ℝ) / L ^ 2) * (1 / 4 * (L / n)) = (2 * (1 / 4)) * ((n : ℝ) / n) * (L / L ^ 2) := by ring
        rw [h_eq]
        rw [div_self (ne_of_gt hn_pos_real)]
        have h_L2 : L ^ 2 = L * L := by ring
        rw [h_L2]
        have h_L_div : L / (L * L) = 1 / L := by
          rw [div_mul_eq_div_div, div_self (ne_of_gt hL_pos)]
        rw [h_L_div]
        calc
          2 * (1 / 4 : ℝ) * 1 * (1 / L)
          _ = (1 / 2 : ℝ) * (1 / L) := by ring
          _ = 1 / (2 * L) := by rw [one_div_mul_one_div]
  have hC' : C = RealChooseTwo I.card := by
    rw [hI, hC]
  have hB_nonneg : 0 ≤ (1 / (2 * L) : ℝ) := by
    have hleft_nonneg : 0 ≤ 2 * (m_sub : ℝ) * p_sub ^ 2 := by
      exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg m_sub)) (sq_nonneg p_sub)
    linarith
  have h_lin := FixedSetProductModelLinearity I ε p_sub π hp0 hp1 C hC' (1 / (2 * L)) hB_nonneg
  have h_lin_app := h_lin (by
    intro u w hu hw hd1 hd2
    have h_pair := FixedSetProductModelPairUnionBound I p_sub π hp0 hp1 u w hu hw ⟨hd1, hd2⟩
    linarith)
  have h_div : C * (1 / (2 * L)) = C / (2 * L) := by ring
  exact h_div ▸ h_lin_app
