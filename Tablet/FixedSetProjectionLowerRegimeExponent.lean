import Tablet.ProjectionOpenPairFunction

-- [TABLET NODE: FixedSetProjectionLowerRegimeExponent]

theorem FixedSetProjectionLowerRegimeExponent :
    ∀ {ε η p : ℝ} {K n ℓR ℓB : ℕ},
      0 < ε →
      0 < K →
      0 ≤ (K : ℝ) * Real.log (n : ℝ) →
      η ≤ ε / 80 →
      let xR : ℝ := (ℓR : ℝ) / (K : ℝ)
      let xB : ℝ := (ℓB : ℝ) / (K : ℝ)
      ℓR ≤ K →
      ℓB ≤ K →
      xR + xB ≤ 1 - ε / 2 →
        (η + ((1 / 2 : ℝ) + η) - (2 - xR - xB) / 2) *
            (K : ℝ) * Real.log (n : ℝ) +
            min (0 : ℝ)
              (-(p *
                (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ) (K : ℝ) p
                  (n : ℝ) -
                  ε ^ 3 * (K : ℝ) ^ 2)))
          ≤
          -4 * η * (K : ℝ) * Real.log (n : ℝ) := by
-- BODY
  intro ε η p K n ℓR ℓB hε _hK hT hη
  dsimp
  intro _hℓR _hℓB hsum
  have hcoeff :
      η + ((1 / 2 : ℝ) + η) -
          (2 - (ℓR : ℝ) / (K : ℝ) - (ℓB : ℝ) / (K : ℝ)) / 2 ≤
        -4 * η := by
    linarith
  have hscaled :
      (η + ((1 / 2 : ℝ) + η) -
          (2 - (ℓR : ℝ) / (K : ℝ) - (ℓB : ℝ) / (K : ℝ)) / 2) *
          ((K : ℝ) * Real.log (n : ℝ)) ≤
        (-4 * η) * ((K : ℝ) * Real.log (n : ℝ)) := by
    exact mul_le_mul_of_nonneg_right hcoeff hT
  have hmin_nonpos :
      min (0 : ℝ)
        (-(p *
          (ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ) (K : ℝ) p
            (n : ℝ) -
            ε ^ 3 * (K : ℝ) ^ 2))) ≤ 0 := by
    exact min_le_left _ _
  nlinarith [hscaled, hmin_nonpos]
