import Tablet.RealChooseTwo
import Tablet.TwoBiteNaturalIndependenceScale

-- [TABLET NODE: FixedSetProductModelConstants]

theorem FixedSetProductModelConstants {n : ℕ} (ε : ℝ) (hn : 0 < n) :
    let c_prod := (1 / 2 : ℝ) * ((n : ℝ) ^ (4 * ε))
    let K := (TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ)
    let C := RealChooseTwo K
    let L := Real.log (n : ℝ)
    let t := C / Real.sqrt L
    0 < c_prod ∧ 0 ≤ t := by
-- BODY
  dsimp only
  constructor
  · have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
    have hpow_pos : 0 < ((n : ℝ) ^ (4 * ε)) :=
      Real.rpow_pos_of_pos hn_real _
    nlinarith
  · let a := TwoBiteNaturalIndependenceScale (1 + ε) n
    have hchoose_nonneg : 0 ≤ RealChooseTwo (a : ℝ) := by
      by_cases ha0 : a = 0
      · simp [ha0, RealChooseTwo]
      · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha0
        have ha_one : (1 : ℝ) ≤ (a : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt ha_pos)
        have ha_nonneg : 0 ≤ (a : ℝ) := by exact_mod_cast Nat.zero_le a
        unfold RealChooseTwo
        nlinarith
    exact div_nonneg (by simpa [a] using hchoose_nonneg) (Real.sqrt_nonneg _)
