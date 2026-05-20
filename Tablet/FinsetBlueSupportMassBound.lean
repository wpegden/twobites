import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Tablet.FinsetPowersetCylinderMass
import Tablet.Preamble

-- [TABLET NODE: FinsetBlueSupportMassBound]

theorem FinsetBlueSupportMassBound
    {α : Type} [DecidableEq α]
    (blueTerminal B : Finset α) (traces : Finset (Finset α)) (p : ℝ) (uB : ℕ)
    (hp_nonneg : 0 ≤ p)
    (hp_le_one : p ≤ 1)
    (hBblue : B ⊆ blueTerminal)
    (hBcard : B.card = uB)
    (htraces :
      traces ⊆ blueTerminal.powerset.filter (fun S => B ⊆ S)) :
    traces.sum
        (fun S => p ^ S.card *
          ((1 : ℝ) - p) ^ (blueTerminal.card - S.card))
      ≤
      p ^ uB := by
-- BODY
  classical
  have hq_nonneg : 0 ≤ (1 : ℝ) - p := by
    linarith
  have hnonneg :
      ∀ S ∈ blueTerminal.powerset.filter (fun S => B ⊆ S),
        S ∉ traces →
          0 ≤
            p ^ S.card *
              ((1 : ℝ) - p) ^ (blueTerminal.card - S.card) := by
    intro S hS hSnot
    exact mul_nonneg (pow_nonneg hp_nonneg _) (pow_nonneg hq_nonneg _)
  have hsum_le :
      traces.sum
          (fun S => p ^ S.card *
            ((1 : ℝ) - p) ^ (blueTerminal.card - S.card))
        ≤
        (blueTerminal.powerset.filter (fun S => B ⊆ S)).sum
          (fun S => p ^ S.card *
            ((1 : ℝ) - p) ^ (blueTerminal.card - S.card)) :=
    Finset.sum_le_sum_of_subset_of_nonneg htraces hnonneg
  have hfilter_eq :
      blueTerminal.powerset.filter (fun S => B ⊆ S)
        =
      blueTerminal.powerset.filter (fun S => B ⊆ S ∧ Disjoint ∅ S) := by
    ext S
    simp
  have hfull :
      (blueTerminal.powerset.filter (fun S => B ⊆ S)).sum
          (fun S => p ^ S.card *
            ((1 : ℝ) - p) ^ (blueTerminal.card - S.card))
        =
        p ^ uB := by
    calc
      (blueTerminal.powerset.filter (fun S => B ⊆ S)).sum
          (fun S => p ^ S.card *
            ((1 : ℝ) - p) ^ (blueTerminal.card - S.card))
          =
        (blueTerminal.powerset.filter (fun S => B ⊆ S ∧ Disjoint ∅ S)).sum
          (fun S => p ^ S.card *
            ((1 : ℝ) - p) ^ (blueTerminal.card - S.card)) := by
          rw [hfilter_eq]
      _ =
        p ^ B.card * ((1 : ℝ) - p) ^ (∅ : Finset α).card := by
          exact
            FinsetPowersetCylinderMass blueTerminal B ∅ p
              hBblue (by simp) (by simp)
      _ = p ^ uB := by
          simp [hBcard]
  exact le_trans hsum_le (le_of_eq hfull)
