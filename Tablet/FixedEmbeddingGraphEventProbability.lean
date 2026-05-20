import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEmbedding
import Tablet.GnpGraphWeight
import Tablet.UniformInjectionWeight

-- [TABLET NODE: FixedEmbeddingGraphEventProbability]

open scoped Classical BigOperators

theorem FixedEmbeddingGraphEventProbability {n m : ℕ} (p : ℝ)
    (π : Fin n ↪ (Fin m × Fin m))
    (K : SimpleGraph (Fin m) × SimpleGraph (Fin m) → Prop) :
    TwoBiteEventProbability n m p
      (fun ω => TwoBiteEmbedding ω = π ∧ K (ω.1, ω.2.1)) =
    UniformInjectionWeight n m *
      Finset.univ.sum (fun G : SimpleGraph (Fin m) × SimpleGraph (Fin m) =>
        if K G then GnpGraphWeight p G.1 * GnpGraphWeight p G.2 else 0) := by
-- BODY
  classical
  let A := SimpleGraph (Fin m)
  let C := Fin n ↪ (Fin m × Fin m)
  let sampleEvent : A × (A × C) → Prop := fun x => x.2.2 = π ∧ K (x.1, x.2.1)
  let pairEvent : A × A → Prop := fun G => K G
  let pairWeight : A × A → ℝ := fun G => GnpGraphWeight p G.1 * GnpGraphWeight p G.2
  have hCsum : ∀ (r : ℝ) (P : Prop),
      (∑ c : C, if c = π ∧ P then r else 0) = if P then r else 0 := by
    intro r P
    by_cases hP : P
    · simp [C, hP]
    · simp [hP]
  unfold TwoBiteEventProbability TwoBiteSampleWeight TwoBiteEmbedding
  rw [Finset.sum_filter]
  change
    (∑ x : A × (A × C),
      @ite ℝ (sampleEvent x) (Classical.propDecidable (sampleEvent x))
        (GnpGraphWeight p x.1 * GnpGraphWeight p x.2.1 * UniformInjectionWeight n m) 0) =
      UniformInjectionWeight n m * Finset.univ.sum (fun G : A × A =>
        if pairEvent G then pairWeight G else 0)
  have hnormalize :
      (∑ x : A × (A × C),
        @ite ℝ (sampleEvent x) (Classical.propDecidable (sampleEvent x))
          (GnpGraphWeight p x.1 * GnpGraphWeight p x.2.1 * UniformInjectionWeight n m) 0) =
      (∑ x : A × (A × C),
        if sampleEvent x then
          GnpGraphWeight p x.1 * GnpGraphWeight p x.2.1 * UniformInjectionWeight n m
        else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : sampleEvent x <;> simp [h]
  rw [hnormalize]
  calc
    (∑ x : A × (A × C),
        if sampleEvent x then
          GnpGraphWeight p x.1 * GnpGraphWeight p x.2.1 * UniformInjectionWeight n m
        else 0)
        = ∑ a : A, ∑ y : A × C,
            if sampleEvent (a, y) then
              GnpGraphWeight p a * GnpGraphWeight p y.1 * UniformInjectionWeight n m
            else 0 := by
          rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ a : A, ∑ b : A, ∑ c : C,
            if c = π ∧ pairEvent (a, b) then
              GnpGraphWeight p a * GnpGraphWeight p b * UniformInjectionWeight n m
            else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ a : A, ∑ b : A,
            if pairEvent (a, b) then
              GnpGraphWeight p a * GnpGraphWeight p b * UniformInjectionWeight n m
            else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          simpa using
            hCsum (GnpGraphWeight p a * GnpGraphWeight p b * UniformInjectionWeight n m)
              (pairEvent (a, b))
    _ = ∑ G : A × A,
            if pairEvent G then pairWeight G * UniformInjectionWeight n m else 0 := by
          rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = (∑ G : A × A, if pairEvent G then pairWeight G else 0) *
          UniformInjectionWeight n m := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro G hG
          by_cases hK : pairEvent G
          · simp [hK]
          · simp [hK]
    _ = UniformInjectionWeight n m *
          Finset.univ.sum (fun G : A × A => if pairEvent G then pairWeight G else 0) := by
          ring
