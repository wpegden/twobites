import Tablet.TwoBiteProjectionSizeEvent
import Tablet.TwoBiteEventProbabilityInjectionOnly
import Tablet.UniformInjectionWeight
import Tablet.UniformInjectionImage
import Tablet.ProjectionSubsetCountBound
import Mathlib.Tactic

open Finset

-- [TABLET NODE: InjectionOnlyEventProbabilityBound]

theorem InjectionOnlyEventProbabilityBound {n m k ℓR ℓB : ℕ} {p : ℝ}
    (I : Finset (Fin n)) (hI : I.card = k) :
    TwoBiteEventProbability n m p (fun ω => TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I)
    ≤ (Nat.choose m ℓR * Nat.choose m ℓB * Nat.choose (ℓR * ℓB) k : ℝ) / (Nat.choose (m * m) k : ℝ) := by
-- BODY
  let event : (Fin n ↪ Fin m × Fin m) → Prop :=
    fun pi => I.card = k ∧ (I.image (fun i => (pi i).1)).card = ℓR ∧ (I.image (fun i => (pi i).2)).card = ℓB
  have h_eq : (fun ω : TwoBiteSample n m p => TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I) =
      (fun ω => event ω.2.2) := by
    ext ω
    dsimp [TwoBiteProjectionSizeEvent, event, TwoBiteRedProjection, TwoBiteBlueProjection, TwoBiteEmbedding]
    rfl

  let P : Finset (Fin m × Fin m) → Prop :=
    fun S => (S.image Prod.fst).card = ℓR ∧ (S.image Prod.snd).card = ℓB
  
  have hevent : ∀ pi, event pi ↔ P (I.image pi) := by
    intro pi
    dsimp [event, P]
    rw [hI, image_image, image_image]
    simp only [true_and]
    rfl

  have h_eq2 : TwoBiteEventProbability n m p (fun ω => TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR) (ℓB := ℓB) ω I) =
      ((Finset.filter (fun (pi : Fin n ↪ Fin m × Fin m) => P (I.image pi)) Finset.univ).card : ℝ) * UniformInjectionWeight n m := by
    rw [h_eq, TwoBiteEventProbabilityInjectionOnly event]
    congr 2
    apply congrArg
    ext pi
    simp [hevent pi]

  rw [h_eq2]
  have h_img := UniformInjectionImage I hI P

  by_cases h_inj : Fintype.card (Fin n ↪ Fin m × Fin m) = 0
  · rw [UniformInjectionWeight, if_pos h_inj, mul_zero]
    apply div_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · exact Nat.cast_nonneg _
        · exact Nat.cast_nonneg _
      · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
  
  · rw [UniformInjectionWeight, if_neg h_inj]
    have h_pos_inj : 0 < Fintype.card (Fin n ↪ Fin m × Fin m) := Nat.pos_of_ne_zero h_inj
    have h_emb : Nonempty (Fin n ↪ Fin m × Fin m) := by
      rw [← Fintype.card_pos_iff]
      exact h_pos_inj
    have hn : n ≤ m * m := by
      have := Fintype.card_le_of_embedding h_emb.some
      simpa using this
    have hk : k ≤ m * m := by
      have h1 : I.card ≤ n := by
        calc I.card ≤ Fintype.card (Fin n) := Finset.card_le_univ I
          _ = n := Fintype.card_fin n
      calc k = I.card := hI.symm
        _ ≤ n := h1
        _ ≤ m * m := hn
    
    have h_denom_pos : (0 : ℝ) < Nat.choose (m * m) k := by
      exact Nat.cast_pos.mpr (Nat.choose_pos hk)
    
    let S_filter := Finset.filter (fun S : Finset (Fin m × Fin m) => S.card = k ∧ P S) Finset.univ
    have h_img_real : (((Finset.filter (fun (pi : Fin n ↪ Fin m × Fin m) => P (I.image pi)) Finset.univ).card : ℝ)) * (Nat.choose (m * m) k : ℝ) =
        ((S_filter.card : ℝ)) * (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) := by
      have h1 : (((Finset.filter (fun (pi : Fin n ↪ Fin m × Fin m) => P (I.image pi)) Finset.univ).card * Nat.choose (m * m) k : ℕ) : ℝ) =
          ((S_filter.card * Fintype.card (Fin n ↪ Fin m × Fin m) : ℕ) : ℝ) := congrArg (fun x : ℕ => (x : ℝ)) h_img
      push_cast at h1
      exact h1

    have h_sub_bound := @ProjectionSubsetCountBound m k ℓR ℓB
    have h_sub_bound_real : ((S_filter.card : ℝ)) ≤ (Nat.choose m ℓR * Nat.choose m ℓB * Nat.choose (ℓR * ℓB) k : ℝ) := by
      have h2 : S_filter.card = (Finset.filter (fun S : Finset (Fin m × Fin m) => S.card = k ∧ (S.image Prod.fst).card = ℓR ∧ (S.image Prod.snd).card = ℓB) Finset.univ).card := by rfl
      have h3 := h_sub_bound
      rw [← h2] at h3
      exact_mod_cast h3

    -- Re-arrange h_img_real to isolate `((Finset.filter ...).card : ℝ)`
    have h_iso : (((Finset.filter (fun (pi : Fin n ↪ Fin m × Fin m) => P (I.image pi)) Finset.univ).card : ℝ)) =
        ((S_filter.card : ℝ)) * (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) / (Nat.choose (m * m) k : ℝ) := by
      rw [← h_img_real, mul_div_cancel_right₀ _ h_denom_pos.ne']

    rw [h_iso]
    
    -- Now we need to prove `(S_filter.card * Y / C) * Y⁻¹ ≤ RHS / C`
    -- which is `S_filter.card / C ≤ RHS / C`
    -- Since `Y * Y⁻¹ = 1`
    have h_cancel : ((((S_filter.card : ℝ)) * (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) / (Nat.choose (m * m) k : ℝ)) * (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ)⁻¹) =
        ((S_filter.card : ℝ)) / (Nat.choose (m * m) k : ℝ) := by
      have h_Y_ne_zero : (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) ≠ 0 := by
        exact Nat.cast_ne_zero.mpr h_inj
      calc _ = (((S_filter.card : ℝ)) / (Nat.choose (m * m) k : ℝ)) * ((Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ) * (Fintype.card (Fin n ↪ Fin m × Fin m) : ℝ)⁻¹) := by ring
        _ = (((S_filter.card : ℝ)) / (Nat.choose (m * m) k : ℝ)) * 1 := by rw [mul_inv_cancel₀ h_Y_ne_zero]
        _ = (((S_filter.card : ℝ)) / (Nat.choose (m * m) k : ℝ)) := by rw [mul_one]
        
    rw [h_cancel]
    
    apply div_le_div_of_nonneg_right h_sub_bound_real (le_of_lt h_denom_pos)
