import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteSampleWeight
import Tablet.GnpGraphWeight
import Tablet.UniformInjectionWeight
import Tablet.FixedSetCylinderProductMassFactor

-- [TABLET NODE: FixedSetCylinderProductLaw]

theorem FixedSetCylinderProductLaw :
    ∀ {n m : ℕ} {p : ℝ}
      (hist : TwoBiteSample n m p → Prop)
      (recorded product :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (ω0 : TwoBiteSample n m p),
      0 < p →
      p < 1 →
      hist ω0 →
      (∀ ω : TwoBiteSample n m p,
        hist ω ↔
          (∀ x : Fin n, ω.2.2 x = ω0.2.2 x) ∧
          (∀ e,
            e ∈ recorded →
              (TwoBiteEdgeCoordinateValue ω e ↔
                TwoBiteEdgeCoordinateValue ω0 e))) →
      (∀ e, e ∈ recorded →
        match e with
        | Sum.inl q => q.1.val < q.2.val
        | Sum.inr q => q.1.val < q.2.val) →
      (∀ e, e ∈ product → e ∉ recorded) →
      (∀ e, e ∈ product →
        match e with
        | Sum.inl q => q.1.val < q.2.val
        | Sum.inr q => q.1.val < q.2.val) →
      ∀ A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
        A ⊆ product →
          TwoBiteConditionalProbability n m p
            (fun ω =>
              ∀ e, e ∈ product →
                (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A))
            hist =
            p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card) := by
-- BODY
  intro n m p hist recorded product ω0 hp_pos hp_lt hhist0 hCylinder
    hRecordedOriented hProductUnrecorded hProductOriented A hAproduct
  classical
  let productEvent : TwoBiteSample n m p → Prop :=
    fun ω =>
      ∀ e, e ∈ product →
        (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A)
  have hConditionalUnfold :
      TwoBiteConditionalProbability n m p productEvent hist =
        if TwoBiteEventProbability n m p hist = 0 then
          0
        else
          TwoBiteEventProbability n m p
              (fun ω => productEvent ω ∧ hist ω) /
            TwoBiteEventProbability n m p hist := by
    rfl
  have hEventSplit :
      ∀ ω : TwoBiteSample n m p,
        productEvent ω ↔
          (∀ e, e ∈ A → TwoBiteEdgeCoordinateValue ω e) ∧
          (∀ e, e ∈ product \ A → ¬ TwoBiteEdgeCoordinateValue ω e) := by
    intro ω
    constructor
    · intro hω
      constructor
      · intro e heA
        exact (hω e (hAproduct heA)).2 heA
      · intro e heDiff hedge
        have heProduct : e ∈ product := (Finset.mem_sdiff.mp heDiff).1
        have heNotA : e ∉ A := (Finset.mem_sdiff.mp heDiff).2
        exact heNotA ((hω e heProduct).1 hedge)
    · intro hω e heProduct
      constructor
      · intro hedge
        by_contra heNotA
        exact (hω.2 e (Finset.mem_sdiff.mpr ⟨heProduct, heNotA⟩)) hedge
      · intro heA
        exact hω.1 e heA
  have hAcard_le_product : A.card ≤ product.card :=
    Finset.card_le_card hAproduct
  have hAInterProduct : A ∩ product = A := by
    apply Finset.ext
    intro e
    constructor
    · intro he
      exact (Finset.mem_inter.mp he).1
    · intro heA
      exact Finset.mem_inter.mpr ⟨heA, hAproduct heA⟩
  have hProductDiffCard :
      (product \ A).card = product.card - A.card := by
    rw [Finset.card_sdiff, hAInterProduct]
  have hProdDiffFactor :
      (product \ A).prod (fun e =>
        if e ∈ A then p else (1 : ℝ) - p) =
        ((1 : ℝ) - p) ^ (product \ A).card := by
    calc
      (product \ A).prod (fun e =>
          if e ∈ A then p else (1 : ℝ) - p)
          = (product \ A).prod (fun _ => (1 : ℝ) - p) := by
            apply Finset.prod_congr rfl
            intro e he
            simp [(Finset.mem_sdiff.mp he).2]
      _ = ((1 : ℝ) - p) ^ (product \ A).card := by
            simp
  have hProdAFactor :
      A.prod (fun e => if e ∈ A then p else (1 : ℝ) - p) =
        p ^ A.card := by
    calc
      A.prod (fun e => if e ∈ A then p else (1 : ℝ) - p)
          = A.prod (fun _ => p) := by
            apply Finset.prod_congr rfl
            intro e he
            simp [he]
      _ = p ^ A.card := by
            simp
  have hFactorProduct :
      product.prod (fun e =>
        if e ∈ A then p else (1 : ℝ) - p) =
        p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card) := by
    calc
      product.prod (fun e =>
          if e ∈ A then p else (1 : ℝ) - p)
          =
          (product \ A).prod (fun e =>
              if e ∈ A then p else (1 : ℝ) - p) *
            A.prod (fun e =>
              if e ∈ A then p else (1 : ℝ) - p) := by
            rw [← Finset.prod_sdiff hAproduct]
      _ = ((1 : ℝ) - p) ^ (product \ A).card * p ^ A.card := by
            rw [hProdDiffFactor, hProdAFactor]
      _ = p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card) := by
            rw [hProductDiffCard, mul_comm]
  have hAUnrecorded :
      ∀ e, e ∈ A → e ∉ recorded := by
    intro e heA
    exact hProductUnrecorded e (hAproduct heA)
  have hAOriented :
      ∀ e, e ∈ A →
        match e with
        | Sum.inl q => q.1.val < q.2.val
        | Sum.inr q => q.1.val < q.2.val := by
    intro e heA
    exact hProductOriented e (hAproduct heA)
  have hConditionCylinderAtRep :
      hist ω0 ↔
        (∀ x : Fin n, ω0.2.2 x = ω0.2.2 x) ∧
        (∀ e,
          e ∈ recorded →
            (TwoBiteEdgeCoordinateValue ω0 e ↔
              TwoBiteEdgeCoordinateValue ω0 e)) :=
    hCylinder ω0
  let injectionEvent : TwoBiteSample n m p → Prop :=
    fun ω => ∀ x : Fin n, ω.2.2 x = ω0.2.2 x
  let recordedEvent : TwoBiteSample n m p → Prop :=
    fun ω =>
      ∀ e,
        e ∈ recorded →
          (TwoBiteEdgeCoordinateValue ω e ↔
            TwoBiteEdgeCoordinateValue ω0 e)
  have hHistCylinder :
      ∀ ω : TwoBiteSample n m p,
        hist ω ↔ injectionEvent ω ∧ recordedEvent ω := by
    intro ω
    simpa [injectionEvent, recordedEvent] using hCylinder ω
  have hEventProbability_congr :
      ∀ E F : TwoBiteSample n m p → Prop,
        (∀ ω, E ω ↔ F ω) →
          TwoBiteEventProbability n m p E =
            TwoBiteEventProbability n m p F := by
    intro E F hiff
    unfold TwoBiteEventProbability
    have hfilter :
        (Finset.univ.filter (fun ω : TwoBiteSample n m p => E ω)) =
          (Finset.univ.filter (fun ω : TwoBiteSample n m p => F ω)) := by
      ext ω
      simp [hiff ω]
    rw [hfilter]
  have hDenominatorCylinder :
      TwoBiteEventProbability n m p hist =
        TwoBiteEventProbability n m p
          (fun ω => injectionEvent ω ∧ recordedEvent ω) := by
    exact hEventProbability_congr hist
      (fun ω => injectionEvent ω ∧ recordedEvent ω) hHistCylinder
  have hNumeratorCylinder :
      TwoBiteEventProbability n m p
          (fun ω => productEvent ω ∧ hist ω) =
        TwoBiteEventProbability n m p
          (fun ω =>
            productEvent ω ∧ injectionEvent ω ∧ recordedEvent ω) := by
    apply hEventProbability_congr
    intro ω
    rw [hHistCylinder ω]
  have hSampleWeightUnfold :
      ∀ ω : TwoBiteSample n m p,
        TwoBiteSampleWeight ω =
          GnpGraphWeight p ω.1 *
            GnpGraphWeight p ω.2.1 *
              UniformInjectionWeight n m := by
    intro ω
    rfl
  have hProductEventFactor :
      ∀ ω : TwoBiteSample n m p,
        productEvent ω →
          product.prod
              (fun e =>
                if TwoBiteEdgeCoordinateValue ω e then
                  p
                else
                  (1 : ℝ) - p) =
            p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card) := by
    intro ω hω
    calc
      product.prod
          (fun e =>
            if TwoBiteEdgeCoordinateValue ω e then
              p
            else
              (1 : ℝ) - p)
          =
          product.prod (fun e =>
            if e ∈ A then p else (1 : ℝ) - p) := by
            apply Finset.prod_congr rfl
            intro e heProduct
            by_cases hedge : TwoBiteEdgeCoordinateValue ω e
            · have heA : e ∈ A := (hω e heProduct).1 hedge
              simp [hedge, heA]
            · have heNotA : e ∉ A := by
                intro heA
                exact hedge ((hω e heProduct).2 heA)
              simp [hedge, heNotA]
      _ = p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card) :=
            hFactorProduct
  have hMass :=
    FixedSetCylinderProductMassFactor hist recorded product ω0 hp_pos hp_lt
      hhist0 hCylinder hRecordedOriented hProductUnrecorded hProductOriented
      A hAproduct
  have hDenominatorNonzero :
      TwoBiteEventProbability n m p hist ≠ 0 :=
    hMass.1
  have hNumeratorMass :
      TwoBiteEventProbability n m p
          (fun ω => productEvent ω ∧ hist ω) =
        (p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card)) *
          TwoBiteEventProbability n m p hist := by
    simpa [productEvent] using hMass.2
  rw [hConditionalUnfold]
  rw [if_neg hDenominatorNonzero]
  rw [hNumeratorMass]
  exact mul_div_cancel_right₀
    (p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card))
    hDenominatorNonzero
