import Tablet.Preamble

-- [TABLET NODE: FixedSetHistoryCellBinomialExponentialEstimate]

set_option maxHeartbeats 1000000 in
theorem FixedSetHistoryCellBinomialExponentialEstimate :
    ∀ {k uR uB NR NB : ℕ} {p ε1 a : ℝ},
      0 ≤ ε1 →
      ε1 ≤ 1 →
      0 ≤ p →
      p ≤ (1 / 2 : ℝ) →
      uB ≤ uR →
      (NR : ℝ) ≤ 3 * ε1 * (k : ℝ) ^ 2 →
      (NB : ℝ) ≤ (k : ℝ) ^ 2 →
      ((Nat.choose NR uR : ℝ) * p ^ uR *
          (Nat.choose NB uB : ℝ) * p ^ uB *
        Real.rpow ((1 : ℝ) - p)
          (max 0 (a - (uR : ℝ) - (uB : ℝ))))
        ≤
        Real.exp
          (8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 - p * a) := by
-- BODY
  intro k uR uB NR NB p ε1 a hε_nonneg hε_le_one hp_nonneg hp_le_half
    huB_le_uR hNR hNB
  classical
  by_cases hp_zero : p = 0
  · subst p
    by_cases huR_zero : uR = 0
    · subst uR
      have huB_zero : uB = 0 := Nat.eq_zero_of_le_zero huB_le_uR
      subst uB
      simp
    · simp [huR_zero]
  have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg (Ne.symm hp_zero)
  have absence_le_exp_of (x : ℝ) :
      Real.rpow (1 - p) (max 0 x) ≤ Real.exp (-(p * x)) := by
    by_cases hx : 0 ≤ x
    · have hbase_nonneg : 0 ≤ 1 - p := by linarith
      have hbase_le : 1 - p ≤ Real.exp (-p) := Real.one_sub_le_exp_neg p
      have hrpow :
          Real.rpow (1 - p) x ≤ Real.rpow (Real.exp (-p)) x :=
        Real.rpow_le_rpow hbase_nonneg hbase_le hx
      have hexp_rpow :
          Real.rpow (Real.exp (-p)) x = Real.exp (-(p * x)) := by
        calc
          Real.rpow (Real.exp (-p)) x = Real.exp ((-p) * x) :=
            (Real.exp_mul (-p) x).symm
          _ = Real.exp (-(p * x)) := by ring_nf
      rw [max_eq_right hx]
      exact le_trans hrpow (le_of_eq hexp_rpow)
    · have hx_le : x ≤ 0 := le_of_not_ge hx
      have hmax : max 0 x = 0 := max_eq_left hx_le
      have hnonneg : 0 ≤ -(p * x) := by nlinarith [hp_nonneg, hx_le]
      have hone : (1 : ℝ) ≤ Real.exp (-(p * x)) :=
        Real.one_le_exp_iff.mpr (by simpa using hnonneg)
      simpa [hmax] using hone
  have absence_le_exp :
      Real.rpow (1 - p) (max 0 a) ≤ Real.exp (-(p * a)) :=
    absence_le_exp_of a
  by_cases hε_zero : ε1 = 0
  · subst ε1
    have hNR_zero : NR = 0 := by
      have hNR_nonneg : (0 : ℝ) ≤ (NR : ℝ) := by exact_mod_cast Nat.zero_le NR
      have hNR_le_zero : (NR : ℝ) ≤ 0 := by simpa using hNR
      exact_mod_cast le_antisymm hNR_le_zero hNR_nonneg
    subst NR
    by_cases huR_zero : uR = 0
    · subst uR
      have huB_zero : uB = 0 := Nat.eq_zero_of_le_zero huB_le_uR
      subst uB
      simpa using absence_le_exp
    · have hchooseR : Nat.choose 0 uR = 0 :=
        Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero huR_zero)
      simpa [hchooseR] using (Real.exp_pos (-(p * a))).le
  have hε_pos : 0 < ε1 := lt_of_le_of_ne hε_nonneg (Ne.symm hε_zero)
  by_cases hk_zero : k = 0
  · subst k
    have hNR_zero : NR = 0 := by
      have hNR_nonneg : (0 : ℝ) ≤ (NR : ℝ) := by exact_mod_cast Nat.zero_le NR
      have hNR_le_zero : (NR : ℝ) ≤ 0 := by simpa using hNR
      exact_mod_cast le_antisymm hNR_le_zero hNR_nonneg
    have hNB_zero : NB = 0 := by
      have hNB_nonneg : (0 : ℝ) ≤ (NB : ℝ) := by exact_mod_cast Nat.zero_le NB
      have hNB_le_zero : (NB : ℝ) ≤ 0 := by simpa using hNB
      exact_mod_cast le_antisymm hNB_le_zero hNB_nonneg
    subst NR
    subst NB
    by_cases huR_zero : uR = 0
    · subst uR
      have huB_zero : uB = 0 := Nat.eq_zero_of_le_zero huB_le_uR
      subst uB
      simpa using absence_le_exp
    · have hchooseR : Nat.choose 0 uR = 0 :=
        Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero huR_zero)
      simpa [hchooseR] using (Real.exp_pos (-(p * a))).le
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_zero
  by_cases huR_zero : uR = 0
  · subst uR
    have huB_zero : uB = 0 := Nat.eq_zero_of_le_zero huB_le_uR
    subst uB
    have hshift_nonneg : 0 ≤ 8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 := by positivity
    have h_exp_mono :
        Real.exp (-(p * a)) ≤
          Real.exp (8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 - p * a) := by
      rw [Real.exp_le_exp]
      linarith
    simpa using le_trans absence_le_exp h_exp_mono
  have huR_pos : 0 < uR := Nat.pos_of_ne_zero huR_zero
  let q : ℝ := 2 * p
  let lam : ℝ := Real.sqrt ε1
  let K : ℝ := (k : ℝ) ^ 2
  have hlam_pos : 0 < lam := by
    dsimp [lam]
    exact Real.sqrt_pos_of_pos hε_pos
  have hlam_nonneg : 0 ≤ lam := hlam_pos.le
  have hlam_le_one : lam ≤ 1 := by
    dsimp [lam]
    exact Real.sqrt_le_one.mpr hε_le_one
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    nlinarith
  have hq_pos : 0 < q := by
    dsimp [q]
    nlinarith
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hNR_nonneg : 0 ≤ (NR : ℝ) := by exact_mod_cast Nat.zero_le NR
  have hNB_nonneg : 0 ≤ (NB : ℝ) := by exact_mod_cast Nat.zero_le NB
  have hscale_nonneg : 0 ≤ q / lam := div_nonneg hq_nonneg hlam_nonneg
  have hred_scaled :
      (Nat.choose NR uR : ℝ) * (q / lam) ^ uR ≤
        Real.exp ((q / lam) * (NR : ℝ)) := by
    have hchoose :
        (Nat.choose NR uR : ℝ) ≤ (NR : ℝ) ^ uR / (uR.factorial : ℝ) :=
      Nat.choose_le_pow_div (α := ℝ) uR NR
    calc
      (Nat.choose NR uR : ℝ) * (q / lam) ^ uR
          ≤ ((NR : ℝ) ^ uR / (uR.factorial : ℝ)) * (q / lam) ^ uR :=
            mul_le_mul_of_nonneg_right hchoose (pow_nonneg hscale_nonneg uR)
      _ = (((q / lam) * (NR : ℝ)) ^ uR) / (uR.factorial : ℝ) := by
            rw [mul_pow]
            ring
      _ ≤ Real.exp ((q / lam) * (NR : ℝ)) :=
            Real.pow_div_factorial_le_exp ((q / lam) * (NR : ℝ))
              (mul_nonneg hscale_nonneg hNR_nonneg) uR
  have hblue_scaled :
      (Nat.choose NB uB : ℝ) * (lam * q) ^ uB ≤
        Real.exp ((lam * q) * (NB : ℝ)) := by
    have hchoose :
        (Nat.choose NB uB : ℝ) ≤ (NB : ℝ) ^ uB / (uB.factorial : ℝ) :=
      Nat.choose_le_pow_div (α := ℝ) uB NB
    have hlamq_nonneg : 0 ≤ lam * q := mul_nonneg hlam_nonneg hq_nonneg
    calc
      (Nat.choose NB uB : ℝ) * (lam * q) ^ uB
          ≤ ((NB : ℝ) ^ uB / (uB.factorial : ℝ)) * (lam * q) ^ uB :=
            mul_le_mul_of_nonneg_right hchoose (pow_nonneg hlamq_nonneg uB)
      _ = (((lam * q) * (NB : ℝ)) ^ uB) / (uB.factorial : ℝ) := by
            rw [mul_pow]
            ring
      _ ≤ Real.exp ((lam * q) * (NB : ℝ)) :=
            Real.pow_div_factorial_le_exp ((lam * q) * (NB : ℝ))
              (mul_nonneg hlamq_nonneg hNB_nonneg) uB
  let redQ : ℝ := (Nat.choose NR uR : ℝ) * q ^ uR
  let blueQ : ℝ := (Nat.choose NB uB : ℝ) * q ^ uB
  have hredQ_bound :
      redQ ≤ Real.exp ((q / lam) * (NR : ℝ)) * lam ^ uR := by
    have hmul :=
      mul_le_mul_of_nonneg_right hred_scaled (pow_nonneg hlam_nonneg uR)
    calc
      redQ = ((Nat.choose NR uR : ℝ) * (q / lam) ^ uR) * lam ^ uR := by
        dsimp [redQ]
        rw [div_pow]
        field_simp [pow_ne_zero uR hlam_pos.ne']
      _ ≤ Real.exp ((q / lam) * (NR : ℝ)) * lam ^ uR := hmul
  have hblueQ_bound_uB :
      blueQ ≤ Real.exp ((lam * q) * (NB : ℝ)) / lam ^ uB := by
    rw [le_div_iff₀' (pow_pos hlam_pos uB)]
    calc
      lam ^ uB * blueQ =
          (Nat.choose NB uB : ℝ) * (lam * q) ^ uB := by
            dsimp [blueQ]
            rw [mul_pow]
            ring
      _ ≤ Real.exp ((lam * q) * (NB : ℝ)) := hblue_scaled
  have hlam_pow_mono : lam ^ uR ≤ lam ^ uB :=
    pow_le_pow_of_le_one hlam_nonneg hlam_le_one huB_le_uR
  have hblueQ_bound :
      blueQ ≤ Real.exp ((lam * q) * (NB : ℝ)) / lam ^ uR := by
    exact le_trans hblueQ_bound_uB
      (div_le_div_of_nonneg_left (Real.exp_pos ((lam * q) * (NB : ℝ))).le
        (pow_pos hlam_pos uR) hlam_pow_mono)
  have hsupport_raw :
      redQ * blueQ ≤
        Real.exp ((q / lam) * (NR : ℝ)) *
          Real.exp ((lam * q) * (NB : ℝ)) := by
    have hprod :=
      mul_le_mul hredQ_bound hblueQ_bound (by dsimp [blueQ]; positivity)
        (mul_nonneg (Real.exp_pos ((q / lam) * (NR : ℝ))).le
          (pow_nonneg hlam_nonneg uR))
    calc
      redQ * blueQ
          ≤ (Real.exp ((q / lam) * (NR : ℝ)) * lam ^ uR) *
              (Real.exp ((lam * q) * (NB : ℝ)) / lam ^ uR) := hprod
      _ = Real.exp ((q / lam) * (NR : ℝ)) *
            Real.exp ((lam * q) * (NB : ℝ)) := by
            field_simp [pow_ne_zero uR hlam_pos.ne']
  have hred_exp_le :
      (q / lam) * (NR : ℝ) ≤ 3 * lam * q * K := by
    have hmul := mul_le_mul_of_nonneg_left hNR hscale_nonneg
    have hε_eq : ε1 = lam ^ 2 := by
      dsimp [lam]
      rw [Real.sq_sqrt hε_nonneg]
    calc
      (q / lam) * (NR : ℝ) ≤ (q / lam) * (3 * ε1 * K) := by
        simpa [K, mul_assoc] using hmul
      _ = 3 * lam * q * K := by
        rw [hε_eq]
        field_simp [hlam_pos.ne']
  have hblue_exp_le :
      (lam * q) * (NB : ℝ) ≤ lam * q * K := by
    have hlamq_nonneg : 0 ≤ lam * q := mul_nonneg hlam_nonneg hq_nonneg
    have hmul := mul_le_mul_of_nonneg_left hNB hlamq_nonneg
    simpa [K, mul_assoc] using hmul
  have hsupportQ :
      redQ * blueQ ≤ Real.exp (8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2) := by
    have hsum :
        (q / lam) * (NR : ℝ) + (lam * q) * (NB : ℝ) ≤
          4 * lam * q * K := by
      nlinarith [hred_exp_le, hblue_exp_le]
    calc
      redQ * blueQ
          ≤ Real.exp ((q / lam) * (NR : ℝ)) *
              Real.exp ((lam * q) * (NB : ℝ)) := hsupport_raw
      _ = Real.exp (((q / lam) * (NR : ℝ)) + ((lam * q) * (NB : ℝ))) := by
            rw [Real.exp_add]
      _ ≤ Real.exp (4 * lam * q * K) := Real.exp_le_exp.mpr hsum
      _ = Real.exp (8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2) := by
            dsimp [q, lam, K]
            ring_nf
  let U : ℕ := uR + uB
  have hexp_p_le_two : Real.exp p ≤ 2 := by
    have hp_lt_one : p < 1 := by linarith
    have h₁ : Real.exp p ≤ 1 / (1 - p) :=
      Real.exp_bound_div_one_sub_of_interval hp_nonneg hp_lt_one
    have h₂ : 1 / (1 - p) ≤ (2 : ℝ) := by
      have hden_pos : 0 < 1 - p := by linarith
      rw [div_le_iff₀ hden_pos]
      nlinarith
    exact le_trans h₁ h₂
  have hexp_pU_le_twoU :
      Real.exp (p * (U : ℝ)) ≤ (2 : ℝ) ^ U := by
    calc
      Real.exp (p * (U : ℝ)) = Real.exp p ^ U := by
        rw [mul_comm, Real.exp_nat_mul]
      _ ≤ (2 : ℝ) ^ U :=
        pow_le_pow_left₀ (Real.exp_pos p).le hexp_p_le_two U
  have hpowers_exp_le_q :
      p ^ uR * p ^ uB * Real.exp (p * (U : ℝ)) ≤ q ^ uR * q ^ uB := by
    calc
      p ^ uR * p ^ uB * Real.exp (p * (U : ℝ))
          ≤ p ^ uR * p ^ uB * (2 : ℝ) ^ U :=
            mul_le_mul_of_nonneg_left hexp_pU_le_twoU (by positivity)
      _ = q ^ uR * q ^ uB := by
            dsimp [q, U]
            rw [pow_add, mul_pow, mul_pow]
            ring
  have hpower_absence :
      p ^ uR * p ^ uB *
          Real.rpow (1 - p) (max 0 (a - (uR : ℝ) - (uB : ℝ))) ≤
        q ^ uR * q ^ uB * Real.exp (-(p * a)) := by
    let c : ℝ := a - (uR : ℝ) - (uB : ℝ)
    by_cases hc : 0 ≤ c
    · have habs := absence_le_exp_of c
      have hcore :
          p ^ uR * p ^ uB * Real.exp (-(p * c)) ≤
            q ^ uR * q ^ uB * Real.exp (-(p * a)) := by
        have hcexp :
            Real.exp (-(p * c)) =
              Real.exp (p * (U : ℝ)) * Real.exp (-(p * a)) := by
          rw [← Real.exp_add]
          congr 1
          dsimp [c, U]
          norm_num
          ring
        calc
          p ^ uR * p ^ uB * Real.exp (-(p * c))
              = (p ^ uR * p ^ uB * Real.exp (p * (U : ℝ))) *
                  Real.exp (-(p * a)) := by
                    rw [hcexp]
                    ring
          _ ≤ (q ^ uR * q ^ uB) * Real.exp (-(p * a)) :=
                mul_le_mul_of_nonneg_right hpowers_exp_le_q
                  (Real.exp_pos (-(p * a))).le
      calc
        p ^ uR * p ^ uB *
            Real.rpow (1 - p) (max 0 (a - (uR : ℝ) - (uB : ℝ)))
            ≤ p ^ uR * p ^ uB * Real.exp (-(p * c)) := by
              have hpow_nonneg : 0 ≤ p ^ uR * p ^ uB := by positivity
              exact mul_le_mul_of_nonneg_left (by simpa [c] using habs) hpow_nonneg
        _ ≤ q ^ uR * q ^ uB * Real.exp (-(p * a)) := hcore
    · have hc_lt : c < 0 := lt_of_not_ge hc
      have hc_le : c ≤ 0 := le_of_lt hc_lt
      have hmax : max 0 c = 0 := max_eq_left hc_le
      have ha_lt_U : a < (U : ℝ) := by
        have hU_cast : (U : ℝ) = (uR : ℝ) + (uB : ℝ) := by
          norm_num [U]
        dsimp [c] at hc_lt
        rw [hU_cast]
        linarith
      have hdecomp :
          p ^ uR * p ^ uB =
            (p ^ uR * p ^ uB * Real.exp (p * (U : ℝ))) *
              Real.exp (-(p * (U : ℝ))) := by
        rw [Real.exp_neg]
        have hne : Real.exp (p * (U : ℝ)) ≠ 0 := (Real.exp_pos _).ne'
        field_simp [hne]
      have hneg_exp_mono :
          Real.exp (-(p * (U : ℝ))) ≤ Real.exp (-(p * a)) := by
        rw [Real.exp_le_exp]
        nlinarith [hp_nonneg, ha_lt_U.le]
      have hpow_le :
          p ^ uR * p ^ uB ≤ q ^ uR * q ^ uB * Real.exp (-(p * a)) := by
        calc
          p ^ uR * p ^ uB
              = (p ^ uR * p ^ uB * Real.exp (p * (U : ℝ))) *
                  Real.exp (-(p * (U : ℝ))) := hdecomp
          _ ≤ (q ^ uR * q ^ uB) * Real.exp (-(p * (U : ℝ))) :=
                mul_le_mul_of_nonneg_right hpowers_exp_le_q
                  (Real.exp_pos (-(p * (U : ℝ)))).le
          _ ≤ q ^ uR * q ^ uB * Real.exp (-(p * a)) :=
                mul_le_mul_of_nonneg_left hneg_exp_mono
                  (mul_nonneg (pow_nonneg hq_nonneg uR) (pow_nonneg hq_nonneg uB))
      simpa [c, hmax] using hpow_le
  have hbin_power_absence :
      ((Nat.choose NR uR : ℝ) * (Nat.choose NB uB : ℝ)) *
          (p ^ uR * p ^ uB *
            Real.rpow (1 - p) (max 0 (a - (uR : ℝ) - (uB : ℝ)))) ≤
        ((Nat.choose NR uR : ℝ) * (Nat.choose NB uB : ℝ)) *
          (q ^ uR * q ^ uB * Real.exp (-(p * a))) :=
    mul_le_mul_of_nonneg_left hpower_absence (by positivity)
  calc
    ((Nat.choose NR uR : ℝ) * p ^ uR *
          (Nat.choose NB uB : ℝ) * p ^ uB *
        Real.rpow ((1 : ℝ) - p)
          (max 0 (a - (uR : ℝ) - (uB : ℝ))))
        ≤ redQ * blueQ * Real.exp (-(p * a)) := by
          calc
            ((Nat.choose NR uR : ℝ) * p ^ uR *
                  (Nat.choose NB uB : ℝ) * p ^ uB *
                Real.rpow ((1 : ℝ) - p)
                  (max 0 (a - (uR : ℝ) - (uB : ℝ))))
                =
              ((Nat.choose NR uR : ℝ) * (Nat.choose NB uB : ℝ)) *
                (p ^ uR * p ^ uB *
                  Real.rpow (1 - p) (max 0 (a - (uR : ℝ) - (uB : ℝ)))) := by
                  ring
            _ ≤ ((Nat.choose NR uR : ℝ) * (Nat.choose NB uB : ℝ)) *
                (q ^ uR * q ^ uB * Real.exp (-(p * a))) :=
                  hbin_power_absence
            _ = redQ * blueQ * Real.exp (-(p * a)) := by
                  dsimp [redQ, blueQ]
                  ring
    _ ≤ Real.exp (8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2) *
        Real.exp (-(p * a)) :=
          mul_le_mul_of_nonneg_right hsupportQ (Real.exp_pos (-(p * a))).le
    _ = Real.exp (8 * Real.sqrt ε1 * p * (k : ℝ) ^ 2 - p * a) := by
          rw [← Real.exp_add]
          congr 1
