import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Tablet.ProductHoeffdingMgFStep
import Tablet.ProductWeightSumOne

open scoped BigOperators

-- [TABLET NODE: ProductMgfBound]

theorem ProductMgfBound :
    ∀ {α : Type} [Fintype α] [DecidableEq α]
      (r : ℕ) (q : α → ℝ) (c : ℝ) (Z : (Fin r → α) → ℝ),
      (∀ a : α, 0 ≤ q a) →
      Finset.univ.sum (fun a : α => q a) = 1 →
      0 < c →
      (∀ (i : Fin r) (ω ω' : Fin r → α),
        (∀ j : Fin r, j ≠ i → ω j = ω' j) →
          |Z ω - Z ω'| ≤ c) →
      ∀ lam : ℝ, 0 ≤ lam →
      let weight : (Fin r → α) → ℝ :=
        fun ω => Finset.univ.prod (fun i : Fin r => q (ω i))
      let expectation : ℝ :=
        Finset.univ.sum (fun ω : Fin r → α => weight ω * Z ω)
      Finset.univ.sum
          (fun ω : Fin r → α =>
            weight ω * Real.exp (lam * (Z ω - expectation)))
        ≤ Real.exp ((r : ℝ) * lam ^ 2 * c ^ 2 / 8) := by
-- BODY
  intro α _ _ r
  induction r with
  | zero =>
      intro q c Z hq hq_sum hc hdiff lam hlam
      classical
      let weight : (Fin 0 → α) → ℝ := fun ω => Finset.univ.prod (fun i : Fin 0 => q (ω i))
      let expectation : ℝ := Finset.univ.sum (fun ω : Fin 0 → α => weight ω * Z ω)
      have hsub : Subsingleton (Fin 0 → α) := inferInstance
      have hweight (ω : Fin 0 → α) : weight ω = 1 := by simp [weight]
      have hexp (ω : Fin 0 → α) : Z ω - expectation = 0 := by
        have : expectation = Z ω := by
          have hZ : ∀ η : Fin 0 → α, Z η = Z ω := fun η => congrArg Z (Subsingleton.elim η ω)
          simp [expectation, weight, hZ]
        linarith
      simp [weight, expectation, hweight, hexp]
  | succ n ih =>
      intro q c Z hq hq_sum hc hdiff lam hlam
      classical
      haveI : Nonempty α := by
        by_contra hα
        haveI : IsEmpty α := not_nonempty_iff.mp hα
        simp at hq_sum
      have hsum_univ_cons :
          ∀ {β : Type} [AddCommMonoid β] (F : (Fin (n + 1) → α) → β),
            Finset.univ.sum F =
              Finset.univ.sum (fun x : α =>
                Finset.univ.sum (fun η : Fin n → α => F (Fin.cons x η))) := by
        intro β _ F
        rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => α)).sum_comp F]
        rw [← Finset.univ_product_univ, Finset.sum_product]
        rfl
      have hproduct_cons (x : α) (η : Fin n → α) :
          (Finset.univ.prod (fun i : Fin (n + 1) =>
            q ((@Fin.cons n (fun _ : Fin (n + 1) => α) x η) i)))
            = q x * Finset.univ.prod (fun i : Fin n => q (η i)) := by
        rw [Fin.prod_univ_succ]
        simp
      let weight : (Fin (n + 1) → α) → ℝ :=
        fun ω => Finset.univ.prod (fun i : Fin (n + 1) => q (ω i))
      let tailWeight : (Fin n → α) → ℝ :=
        fun η => Finset.univ.prod (fun i : Fin n => q (η i))
      let tailZ (x : α) : (Fin n → α) → ℝ := fun η => Z (Fin.cons x η)
      let tailMu (x : α) : ℝ :=
        Finset.univ.sum (fun η : Fin n → α => tailWeight η * tailZ x η)
      let expectation : ℝ :=
        Finset.univ.sum (fun ω : Fin (n + 1) → α => weight ω * Z ω)
      have hweight_cons (x : α) (η : Fin n → α) :
          weight (Fin.cons x η) = q x * tailWeight η := by
        simpa [weight, tailWeight] using hproduct_cons x η
      have hexpect_split :
          expectation = Finset.univ.sum (fun x : α => q x * tailMu x) := by
        dsimp [expectation, tailMu, tailZ]
        rw [hsum_univ_cons (fun ω : Fin (n + 1) → α =>
          (∏ i, q (ω i)) * Z ω)]
        simp_rw [hproduct_cons]
        simp_rw [mul_assoc]
        congr with x
        rw [← Finset.mul_sum]
      have htaildiff (x : α) :
          ∀ (i : Fin n) (ω ω' : Fin n → α),
            (∀ j : Fin n, j ≠ i → ω j = ω' j) →
              |tailZ x ω - tailZ x ω'| ≤ c := by
        intro i ω ω' hsame
        dsimp [tailZ]
        refine hdiff i.succ (Fin.cons x ω) (Fin.cons x ω') ?_
        intro j hj
        cases j using Fin.cases with
        | zero => simp
        | succ j =>
            simp
            exact hsame j (by intro h; apply hj; simpa [h])
      have htail_mgf (x : α) :
          Finset.univ.sum
              (fun η : Fin n → α =>
                tailWeight η * Real.exp (lam * (tailZ x η - tailMu x)))
            ≤ Real.exp ((n : ℝ) * lam ^ 2 * c ^ 2 / 8) := by
        simpa [tailWeight, tailZ, tailMu] using
          ih q c (tailZ x) hq hq_sum hc (htaildiff x) lam hlam
      have htailWeight_nonneg (η : Fin n → α) : 0 ≤ tailWeight η := by
        dsimp [tailWeight]
        exact Finset.prod_nonneg fun i hi => hq (η i)
      have htailWeight_sum : Finset.univ.sum tailWeight = 1 := by
        dsimp [tailWeight]
        exact ProductWeightSumOne n q hq hq_sum
      have hmu_osc :
          ∀ x y : α, |tailMu x - tailMu y| ≤ c := by
        intro x y
        have hpoint (η : Fin n → α) : |tailZ x η - tailZ y η| ≤ c := by
          dsimp [tailZ]
          refine hdiff 0 (Fin.cons x η) (Fin.cons y η) ?_
          intro j hj
          cases j using Fin.cases with
          | zero => contradiction
          | succ j => simp
        have hdiff_sum :
            |tailMu x - tailMu y|
              ≤ Finset.univ.sum (fun η : Fin n → α => tailWeight η * |tailZ x η - tailZ y η|) := by
          dsimp [tailMu]
          calc
            |Finset.univ.sum (fun η : Fin n → α => tailWeight η * tailZ x η) -
                Finset.univ.sum (fun η : Fin n → α => tailWeight η * tailZ y η)|
                = |Finset.univ.sum (fun η : Fin n → α =>
                    tailWeight η * (tailZ x η - tailZ y η))| := by
                  congr 1
                  rw [← Finset.sum_sub_distrib]
                  congr with η
                  ring
            _ ≤ Finset.univ.sum (fun η : Fin n → α =>
                    |tailWeight η * (tailZ x η - tailZ y η)|) := Finset.abs_sum_le_sum_abs _ _
            _ = Finset.univ.sum (fun η : Fin n → α =>
                    tailWeight η * |tailZ x η - tailZ y η|) := by
                  refine Finset.sum_congr rfl ?_
                  intro η hη
                  rw [abs_mul, abs_of_nonneg (htailWeight_nonneg η)]
        calc
          |tailMu x - tailMu y|
              ≤ Finset.univ.sum (fun η : Fin n → α => tailWeight η * |tailZ x η - tailZ y η|) := hdiff_sum
          _ ≤ Finset.univ.sum (fun η : Fin n → α => tailWeight η * c) := by
                refine Finset.sum_le_sum ?_
                intro η hη
                exact mul_le_mul_of_nonneg_left (hpoint η) (htailWeight_nonneg η)
          _ = c := by
                rw [← Finset.sum_mul, htailWeight_sum, one_mul]
      let centeredMu : α → ℝ := fun x => tailMu x - expectation
      have hcenter_mean : Finset.univ.sum (fun x : α => q x * centeredMu x) = 0 := by
        calc
          Finset.univ.sum (fun x : α => q x * centeredMu x)
              = Finset.univ.sum (fun x : α => (q x * tailMu x - q x * expectation)) := by
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    dsimp [centeredMu]
                    ring
          _ = Finset.univ.sum (fun x : α => q x * tailMu x) -
                  expectation * Finset.univ.sum (fun x : α => q x) := by
                    rw [Finset.sum_sub_distrib, Finset.mul_sum]
                    congr 1
                    congr with x
                    ring
          _ = 0 := by
                    rw [hq_sum, mul_one, ← hexpect_split]
                    ring
      let a0 : ℝ := (Finset.univ.image tailMu).min' (by
        classical
        exact Finset.image_nonempty.mpr Finset.univ_nonempty)
      let b0 : ℝ := (Finset.univ.image tailMu).max' (by
        classical
        exact Finset.image_nonempty.mpr Finset.univ_nonempty)
      have ha0_le_b0 : a0 - expectation ≤ b0 - expectation := by
        dsimp [a0, b0]
        gcongr
        exact Finset.min'_le_max' _ _
      have hcenter_bounds (x : α) : a0 - expectation ≤ centeredMu x ∧ centeredMu x ≤ b0 - expectation := by
        have hxmem : tailMu x ∈ Finset.univ.image tailMu := by simp
        constructor <;> dsimp [centeredMu, a0, b0]
        · exact sub_le_sub_right (Finset.min'_le _ _ hxmem) _
        · exact sub_le_sub_right (Finset.le_max' _ _ hxmem) _
      have hbmina : (b0 - expectation) - (a0 - expectation) ≤ c := by
        dsimp [a0, b0]
        have hmem_min : (Finset.univ.image tailMu).min' (Finset.image_nonempty.mpr Finset.univ_nonempty) ∈
            Finset.univ.image tailMu := Finset.min'_mem _ _
        have hmem_max : (Finset.univ.image tailMu).max' (Finset.image_nonempty.mpr Finset.univ_nonempty) ∈
            Finset.univ.image tailMu := Finset.max'_mem _ _
        rcases Finset.mem_image.mp hmem_min with ⟨xmin, _, hxmin⟩
        rcases Finset.mem_image.mp hmem_max with ⟨xmax, _, hxmax⟩
        have h := hmu_osc xmax xmin
        have h' : |b0 - a0| ≤ c := by
          dsimp [a0, b0]
          simpa [hxmax, hxmin] using h
        have hnonneg : 0 ≤ b0 - a0 := by
          dsimp [a0, b0]
          exact sub_nonneg.mpr (Finset.min'_le_max' _ _)
        have h'' : b0 - a0 ≤ c := by
          simpa [abs_of_nonneg hnonneg] using h'
        linarith
      have hcenter_mgf :
          Finset.univ.sum (fun x : α => q x * Real.exp (lam * centeredMu x))
            ≤ Real.exp (lam ^ 2 * ((b0 - expectation) - (a0 - expectation)) ^ 2 / 8) :=
        ProductHoeffdingMgFStep q centeredMu (a0 - expectation) (b0 - expectation) lam
          hq hq_sum ha0_le_b0 hcenter_bounds hcenter_mean hlam
      have hcenter_mgf_c :
          Finset.univ.sum (fun x : α => q x * Real.exp (lam * centeredMu x))
            ≤ Real.exp (lam ^ 2 * c ^ 2 / 8) := by
        refine hcenter_mgf.trans ?_
        apply Real.exp_le_exp.mpr
        have hwidth_nonneg : 0 ≤ (b0 - expectation) - (a0 - expectation) := sub_nonneg.mpr ha0_le_b0
        have hc_nonneg : 0 ≤ c := le_of_lt hc
        have hsq : ((b0 - expectation) - (a0 - expectation)) ^ 2 ≤ c ^ 2 := by
          nlinarith [sq_nonneg (c - ((b0 - expectation) - (a0 - expectation)))]
        nlinarith [hsq, sq_nonneg lam]
      calc
        Finset.univ.sum
            (fun ω : Fin (n + 1) → α =>
              weight ω * Real.exp (lam * (Z ω - expectation)))
            = Finset.univ.sum (fun x : α =>
                q x * (Finset.univ.sum (fun η : Fin n → α =>
                  tailWeight η * Real.exp (lam * (tailZ x η - tailMu x))) *
                  Real.exp (lam * centeredMu x))) := by
              dsimp [weight, expectation, tailWeight, tailZ, tailMu, centeredMu]
              rw [hsum_univ_cons (fun ω : Fin (n + 1) → α =>
                (∏ i, q (ω i)) * Real.exp
                  (lam * (Z ω - ∑ ω, (∏ i, q (ω i)) * Z ω)))]
              congr with x
              simp_rw [hproduct_cons]
              simp_rw [mul_assoc]
              rw [← Finset.mul_sum]
              congr 1
              calc
                Finset.univ.sum (fun η : Fin n → α =>
                    (∏ i, q (η i)) *
                      Real.exp (lam * (Z (Fin.cons x η) - ∑ ω, (∏ i, q (ω i)) * Z ω)))
                    =
                    Finset.univ.sum (fun η : Fin n → α =>
                      ((∏ i, q (η i)) *
                        Real.exp (lam * (Z (Fin.cons x η) -
                          ∑ η, (∏ i, q (η i)) * Z (Fin.cons x η)))) *
                        Real.exp (lam * (∑ η, (∏ i, q (η i)) * Z (Fin.cons x η) -
                          ∑ ω, (∏ i, q (ω i)) * Z ω))) := by
                      refine Finset.sum_congr rfl ?_
                      intro η hη
                      rw [mul_assoc]
                      rw [← Real.exp_add]
                      ring_nf
                _ =
                    (Finset.univ.sum (fun η : Fin n → α =>
                      (∏ i, q (η i)) *
                        Real.exp (lam * (Z (Fin.cons x η) -
                          ∑ η, (∏ i, q (η i)) * Z (Fin.cons x η))))) *
                        Real.exp (lam * (∑ η, (∏ i, q (η i)) * Z (Fin.cons x η) -
                          ∑ ω, (∏ i, q (ω i)) * Z ω)) := by
                      rw [← Finset.sum_mul]
        _ ≤ Finset.univ.sum (fun x : α =>
                q x * (Real.exp ((n : ℝ) * lam ^ 2 * c ^ 2 / 8) *
                  Real.exp (lam * centeredMu x))) := by
              refine Finset.sum_le_sum ?_
              intro x hx
              have hq_nonneg := hq x
              have hexp_nonneg : 0 ≤ Real.exp (lam * centeredMu x) := (Real.exp_pos _).le
              nlinarith [htail_mgf x, mul_nonneg hq_nonneg hexp_nonneg]
        _ = Real.exp ((n : ℝ) * lam ^ 2 * c ^ 2 / 8) *
              Finset.univ.sum (fun x : α => q x * Real.exp (lam * centeredMu x)) := by
              rw [Finset.mul_sum]
              congr with x
              ring
        _ ≤ Real.exp ((n : ℝ) * lam ^ 2 * c ^ 2 / 8) *
              Real.exp (lam ^ 2 * c ^ 2 / 8) := by
              exact mul_le_mul_of_nonneg_left hcenter_mgf_c (Real.exp_pos _).le
        _ = Real.exp (((n + 1 : ℕ) : ℝ) * lam ^ 2 * c ^ 2 / 8) := by
              rw [← Real.exp_add]
              congr 1
              norm_num
              ring
