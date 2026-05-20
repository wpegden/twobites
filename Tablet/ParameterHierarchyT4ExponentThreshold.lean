import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.TwoBiteNaturalIndependenceScale

-- [TABLET NODE: ParameterHierarchyT4ExponentThreshold]

open Filter
open scoped Topology

theorem ParameterHierarchyT4ExponentThreshold :
    ∀ η : ℝ, 0 < η → η < (1 / 16 : ℝ) →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
        let K := TwoBiteNaturalIndependenceScale (1 + η) n
        let k := (K : ℝ)
        let mReal := (n : ℝ) / L ^ 2
        (2 * k * L + L) *
            (16 * L * mReal * Real.rpow (n : ℝ) (8 * η)) ≤ kReal ^ 4 := by
-- BODY
  intro η hη hη_lt
  let α : ℝ := (1 / 2 : ℝ) - 8 * η
  have hα_pos : 0 < α := by dsimp [α]; linarith
  have hκ_pos : 0 < 1 + η := by linarith
  have hκ_ge_one : (1 : ℝ) ≤ 1 + η := by linarith
  have hκ3_pos : 0 < (1 + η) ^ 3 := by positivity
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have hpow_atTop :
      Tendsto (fun n : ℕ => (n : ℝ) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα_pos).comp hn_atTop
  have hκpow_atTop :
      Tendsto (fun n : ℕ => (1 + η) ^ 3 * (n : ℝ) ^ α) atTop atTop :=
    Tendsto.const_mul_atTop hκ3_pos hpow_atTop
  have hgrowth_eventually :
      ∀ᶠ n : ℕ in atTop,
        80 ≤ (1 + η) ^ 3 * (n : ℝ) ^ α *
          (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) := by
    filter_upwards [hκpow_atTop.eventually_ge_atTop (80 : ℝ),
      hlog_atTop.eventually_ge_atTop (1 : ℝ)] with n hlarge hL_ge_one
    have hLpow_ge_one :
        (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) := by
      calc
        (1 : ℝ) = (1 : ℝ) ^ (3 / 2 : ℝ) := by rw [Real.one_rpow]
        _ ≤ (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hL_ge_one
            (by norm_num : (0 : ℝ) ≤ 3 / 2)
    have hA_nonneg : 0 ≤ (1 + η) ^ 3 * (n : ℝ) ^ α :=
      le_trans (by norm_num : (0 : ℝ) ≤ 80) hlarge
    calc
      (80 : ℝ) ≤ (1 + η) ^ 3 * (n : ℝ) ^ α := hlarge
      _ = (1 + η) ^ 3 * (n : ℝ) ^ α * 1 := by ring
      _ ≤ (1 + η) ^ 3 * (n : ℝ) ^ α *
          (Real.log (n : ℝ)) ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hLpow_ge_one hA_nonneg
  have hmain_eventually :
      ∀ᶠ n : ℕ in atTop,
        let L := Real.log (n : ℝ)
        let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
        let K := TwoBiteNaturalIndependenceScale (1 + η) n
        let k := (K : ℝ)
        let mReal := (n : ℝ) / L ^ 2
        (2 * k * L + L) *
            (16 * L * mReal * Real.rpow (n : ℝ) (8 * η)) ≤ kReal ^ 4 := by
    filter_upwards [hgrowth_eventually, hlog_atTop.eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (1 : ℕ)] with n hgrowth hL_ge_one hn_ge_one
    let L := Real.log (n : ℝ)
    let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
    let K := TwoBiteNaturalIndependenceScale (1 + η) n
    let k := (K : ℝ)
    let mReal := (n : ℝ) / L ^ 2
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_ge_one)
    have hL_pos : 0 < L := by dsimp [L]; linarith
    have hkReal_nonneg : 0 ≤ kReal := by
      dsimp [kReal]
      exact mul_nonneg (le_of_lt hκ_pos) (Real.sqrt_nonneg _)
    have hkReal_ge_one : (1 : ℝ) ≤ kReal := by
      dsimp [kReal]
      have hnL_ge_one : (1 : ℝ) ≤ (n : ℝ) * L := by
        nlinarith [show (1 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn_ge_one,
          show (1 : ℝ) ≤ L by simpa [L] using hL_ge_one]
      have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) * L) := by
        simpa using Real.sqrt_le_sqrt hnL_ge_one
      nlinarith
    have hk_lt : k < kReal + 1 := by
      dsimp [k, K, kReal, TwoBiteNaturalIndependenceScale, TwoBiteIndependenceScale]
      exact Nat.ceil_lt_add_one hkReal_nonneg
    have hk_le_two : k ≤ 2 * kReal := by
      have hk_le_add : k ≤ kReal + 1 := le_of_lt hk_lt
      nlinarith
    have hA_le : 2 * k * L + L ≤ 5 * kReal * L := by
      have htwo : 2 * k * L ≤ 4 * kReal * L := by nlinarith
      have hone : L ≤ kReal * L := by nlinarith
      nlinarith
    have hden_nonneg : 0 ≤ 16 * L * mReal * Real.rpow (n : ℝ) (8 * η) := by
      dsimp [mReal]
      positivity
    have hfirst :
        (2 * k * L + L) *
            (16 * L * mReal * Real.rpow (n : ℝ) (8 * η)) ≤
          (5 * kReal * L) *
            (16 * L * mReal * Real.rpow (n : ℝ) (8 * η)) :=
      mul_le_mul_of_nonneg_right hA_le hden_nonneg
    have hm_expand :
        (5 * kReal * L) *
            (16 * L * mReal * Real.rpow (n : ℝ) (8 * η)) =
          80 * kReal * (n : ℝ) * Real.rpow (n : ℝ) (8 * η) := by
      dsimp [mReal]
      field_simp [hL_pos.ne']
      ring
    have hscale :
        80 * kReal * (n : ℝ) * Real.rpow (n : ℝ) (8 * η) ≤
          kReal ^ 4 := by
      have hpower_identity :
          ∀ κ x L η : ℝ, 0 < x → 0 < L →
            (κ ^ 3 * x ^ ((1 / 2 : ℝ) - 8 * η) * L ^ (3 / 2 : ℝ)) *
                ((κ * Real.sqrt (x * L)) * x * x ^ (8 * η)) =
              (κ * Real.sqrt (x * L)) ^ 4 := by
        intro κ x L η hx hL
        have hxprod :
            x ^ ((1 / 2 : ℝ) - η * 8) * x ^ (1 / 2 : ℝ) *
                x ^ (1 : ℝ) * x ^ (η * 8) = x ^ (2 : ℝ) := by
          calc
            x ^ ((1 / 2 : ℝ) - η * 8) * x ^ (1 / 2 : ℝ) *
                x ^ (1 : ℝ) * x ^ (η * 8)
                = (x ^ ((1 / 2 : ℝ) - η * 8) * x ^ (η * 8)) *
                    (x ^ (1 / 2 : ℝ) * x ^ (1 : ℝ)) := by ring
            _ = x ^ (((1 / 2 : ℝ) - η * 8) + η * 8) *
                  x ^ ((1 / 2 : ℝ) + 1) := by
                rw [← Real.rpow_add hx, ← Real.rpow_add hx]
            _ = x ^ ((((1 / 2 : ℝ) - η * 8) + η * 8) + ((1 / 2 : ℝ) + 1)) := by
                rw [← Real.rpow_add hx]
            _ = x ^ (2 : ℝ) := by
                congr 1
                ring
        have hLprod : L ^ (3 / 2 : ℝ) * L ^ (1 / 2 : ℝ) = L ^ (2 : ℝ) := by
          calc
            L ^ (3 / 2 : ℝ) * L ^ (1 / 2 : ℝ)
                = L ^ ((3 / 2 : ℝ) + (1 / 2 : ℝ)) := by
                  rw [← Real.rpow_add hL]
            _ = L ^ (2 : ℝ) := by norm_num
        rw [Real.sqrt_eq_rpow]
        rw [Real.mul_rpow (le_of_lt hx) (le_of_lt hL)]
        rw [mul_pow, mul_pow]
        rw [← Real.rpow_natCast (x ^ (1 / 2 : ℝ)) 4]
        rw [← Real.rpow_natCast (L ^ (1 / 2 : ℝ)) 4]
        norm_num only [Nat.cast_ofNat] at *
        rw [← Real.rpow_mul (le_of_lt hx) (1 / 2 : ℝ) (4 : ℝ)]
        rw [← Real.rpow_mul (le_of_lt hL) (1 / 2 : ℝ) (4 : ℝ)]
        norm_num only at *
        conv_lhs =>
          rw [show x = x ^ (1 : ℝ) by rw [Real.rpow_one]]
        repeat rw [← Real.rpow_mul (le_of_lt hx)]
        ring_nf
        calc
          κ ^ 4 * x ^ ((1 / 2 : ℝ) - η * 8) * L ^ (3 / 2 : ℝ) *
                x ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) * x ^ (1 : ℝ) * x ^ (η * 8)
              = κ ^ 4 *
                  (x ^ ((1 / 2 : ℝ) - η * 8) * x ^ (1 / 2 : ℝ) *
                    x ^ (1 : ℝ) * x ^ (η * 8)) *
                    (L ^ (3 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) := by ring_nf
          _ = κ ^ 4 * x ^ (2 : ℝ) * L ^ (2 : ℝ) := by rw [hxprod, hLprod]
      have hfactor_nonneg :
          0 ≤ kReal * (n : ℝ) * Real.rpow (n : ℝ) (8 * η) := by
        exact mul_nonneg (mul_nonneg hkReal_nonneg (le_of_lt hn_pos))
          (Real.rpow_pos_of_pos hn_pos (8 * η)).le
      have heq :
          ((1 + η) ^ 3 * (n : ℝ) ^ α * L ^ (3 / 2 : ℝ)) *
              (kReal * (n : ℝ) * Real.rpow (n : ℝ) (8 * η)) =
            kReal ^ 4 := by
        dsimp [kReal]
        simpa [α, mul_comm, mul_left_comm, mul_assoc] using
          hpower_identity (1 + η) (n : ℝ) L η hn_pos hL_pos
      have hgrowthL :
          80 ≤ (1 + η) ^ 3 * (n : ℝ) ^ α * L ^ (3 / 2 : ℝ) := by
        simpa [L] using hgrowth
      calc
        80 * kReal * (n : ℝ) * Real.rpow (n : ℝ) (8 * η)
            = 80 * (kReal * (n : ℝ) * Real.rpow (n : ℝ) (8 * η)) := by ring
        _ ≤ ((1 + η) ^ 3 * (n : ℝ) ^ α * L ^ (3 / 2 : ℝ)) *
              (kReal * (n : ℝ) * Real.rpow (n : ℝ) (8 * η)) := by
            exact mul_le_mul_of_nonneg_right hgrowthL hfactor_nonneg
        _ = kReal ^ 4 := heq
    calc
      (2 * k * L + L) *
          (16 * L * mReal * Real.rpow (n : ℝ) (8 * η))
          ≤ (5 * kReal * L) *
            (16 * L * mReal * Real.rpow (n : ℝ) (8 * η)) := hfirst
      _ = 80 * kReal * (n : ℝ) * Real.rpow (n : ℝ) (8 * η) := hm_expand
      _ ≤ kReal ^ 4 := hscale
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp hmain_eventually
  exact ⟨n0, fun n hn => hn0 n (le_of_lt hn)⟩
