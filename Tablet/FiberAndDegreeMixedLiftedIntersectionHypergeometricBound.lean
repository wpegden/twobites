import Tablet.HypergeometricMgfComparison

open Real Filter

-- [TABLET NODE: FiberAndDegreeMixedLiftedIntersectionHypergeometricBound]

theorem FiberAndDegreeMixedLiftedIntersectionHypergeometricBound :
    ∀ (N n m_marked : ℕ) (K_set : Finset (Fin N)) (T L_param : ℝ),
      0 < n → n ≤ N → m_marked ≤ N → K_set.card = m_marked → 0 < T → 0 ≤ L_param →
      (Nat.choose N n : ℝ)⁻¹ * (Finset.powersetCard n (Finset.univ : Finset (Fin N))).sum
        (fun S => (if ((S ∩ K_set).card : ℝ) ≥ T then (1 : ℝ) else (0 : ℝ)))
      ≤ exp (n * (m_marked / N) * (exp L_param - 1) - L_param * T) := by
-- BODY
  intro N n m_marked K_set T L_param hn hnN hmN hK hT hL
  let q := (m_marked : ℝ) / (N : ℝ)
  let μ := (n : ℝ) * q
  have h_bound : ∀ S, (if ((S ∩ K_set).card : ℝ) ≥ T then (1 : ℝ) else (0 : ℝ)) ≤ exp (L_param * (S ∩ K_set).card - L_param * T) := by
    intro S
    let x := ((S ∩ K_set).card : ℝ)
    split_ifs with h
    · have h_pos : 0 ≤ L_param * (x - T) := mul_nonneg hL (sub_nonneg.mpr h)
      have h_exp : 1 ≤ exp (L_param * (x - T)) := one_le_exp h_pos
      have : L_param * (x - T) = L_param * x - L_param * T := by ring
      rwa [this] at h_exp
    · positivity
  have h_sum := (Finset.powersetCard n (Finset.univ : Finset (Fin N))).sum_le_sum (fun S _ => h_bound S)
  have h_const : (Finset.powersetCard n (Finset.univ : Finset (Fin N))).sum (fun S => exp (L_param * (S ∩ K_set).card - L_param * T)) =
                 ((Finset.powersetCard n (Finset.univ : Finset (Fin N))).sum (fun S => exp (L_param * (S ∩ K_set).card))) * exp (- (L_param * T)) := by
    rw [Finset.sum_congr rfl (by intro S _; rw [sub_eq_add_neg, exp_add])]
    rw [Finset.sum_mul]
  have h_mgf := HypergeometricMgfComparison N n m_marked hnN hmN K_set hK L_param
  have h_mgf_bound := h_mgf.1.trans h_mgf.2
  rw [mul_assoc]
  apply le_trans (mul_le_mul_of_nonneg_left h_sum (by positivity))
  rw [h_const]
  rw [← mul_assoc]
  apply le_trans (mul_le_mul_of_nonneg_right h_mgf_bound (by positivity))
  rw [← exp_add]
  ring_nf
  exact le_refl _
