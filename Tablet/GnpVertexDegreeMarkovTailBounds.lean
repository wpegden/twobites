import Tablet.GnpGraphWeight
import Tablet.GraphDegreeCount
import Mathlib.Tactic

open Classical

-- [TABLET NODE: GnpVertexDegreeMarkovTailBounds]

theorem GnpVertexDegreeMarkovTailBounds (m : ℕ) (p t A : ℝ) (r : Fin m)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : 0 ≤ t) :
    (∑ G : SimpleGraph (Fin m),
      if A ≤ (GraphDegreeCount G r : ℝ) then GnpGraphWeight p G else 0) ≤
      Real.exp (-(t * A)) *
        ∑ G : SimpleGraph (Fin m),
          Real.exp (t * (GraphDegreeCount G r : ℝ)) * GnpGraphWeight p G
    ∧
    (∑ G : SimpleGraph (Fin m),
      if (GraphDegreeCount G r : ℝ) ≤ A then GnpGraphWeight p G else 0) ≤
      Real.exp (t * A) *
        ∑ G : SimpleGraph (Fin m),
          Real.exp (-(t * (GraphDegreeCount G r : ℝ))) * GnpGraphWeight p G := by
-- BODY
  have hW : ∀ G : SimpleGraph (Fin m), 0 ≤ GnpGraphWeight p G := by
    intro G
    unfold GnpGraphWeight
    apply Finset.prod_nonneg
    intro e _
    split_ifs
    · exact hp0
    · linarith
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro G _
    by_cases htail : A ≤ (GraphDegreeCount G r : ℝ)
    · simp [htail]
      let X : ℝ := (GraphDegreeCount G r : ℝ)
      have harg_nonneg : 0 ≤ -(t * A) + t * X := by
        have hdiff : 0 ≤ X - A := by
          dsimp [X]
          exact sub_nonneg.mpr htail
        nlinarith [mul_nonneg ht hdiff]
      have hfactor : 1 ≤ Real.exp (-(t * A)) * Real.exp (t * X) := by
        calc
          (1 : ℝ) ≤ Real.exp (-(t * A) + t * X) :=
            Real.one_le_exp harg_nonneg
          _ = Real.exp (-(t * A)) * Real.exp (t * X) := by
            rw [Real.exp_add]
      have hnonneg := hW G
      calc
        GnpGraphWeight p G = 1 * GnpGraphWeight p G := by ring
        _ ≤ (Real.exp (-(t * A)) * Real.exp (t * X)) *
              GnpGraphWeight p G :=
            mul_le_mul_of_nonneg_right hfactor hnonneg
        _ = Real.exp (-(t * A)) *
              (Real.exp (t * (GraphDegreeCount G r : ℝ)) *
                GnpGraphWeight p G) := by
            dsimp [X]
            ring
    · simp [htail]
      exact mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (Real.exp_pos _).le (hW G))
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro G _
    by_cases htail : (GraphDegreeCount G r : ℝ) ≤ A
    · simp [htail]
      let X : ℝ := (GraphDegreeCount G r : ℝ)
      have harg_nonneg : 0 ≤ t * A + (-(t * X)) := by
        have hdiff : 0 ≤ A - X := by
          dsimp [X]
          exact sub_nonneg.mpr htail
        nlinarith [mul_nonneg ht hdiff]
      have hfactor : 1 ≤ Real.exp (t * A) * Real.exp (-(t * X)) := by
        calc
          (1 : ℝ) ≤ Real.exp (t * A + (-(t * X))) :=
            Real.one_le_exp harg_nonneg
          _ = Real.exp (t * A) * Real.exp (-(t * X)) := by
            rw [Real.exp_add]
      have hnonneg := hW G
      calc
        GnpGraphWeight p G = 1 * GnpGraphWeight p G := by ring
        _ ≤ (Real.exp (t * A) * Real.exp (-(t * X))) *
              GnpGraphWeight p G :=
            mul_le_mul_of_nonneg_right hfactor hnonneg
        _ = Real.exp (t * A) *
              (Real.exp (-(t * (GraphDegreeCount G r : ℝ))) *
                GnpGraphWeight p G) := by
            dsimp [X]
            ring
    · simp [htail]
      exact mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (Real.exp_pos _).le (hW G))
