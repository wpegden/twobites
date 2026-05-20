import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyBaseDAlgebra]

theorem ParameterHierarchyBaseDAlgebra :
    ∀ κ S logL k : ℝ,
      1 ≤ κ →
      0 < S →
      0 < logL →
      1 ≤ logL →
      k < 2 * (κ * S) →
      2 * k / (S / logL) + 1 ≤ 5 * κ * logL := by
-- BODY
  intro κ S logL k hκ_ge_one hS hlog_pos hlog_ge_one hk
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ_ge_one
  have hden : 0 < S / logL := div_pos hS hlog_pos
  have hmain : 2 * k / (S / logL) < 4 * (κ * logL) := by
    rw [div_lt_iff₀ hden]
    calc
      2 * k < 2 * (2 * (κ * S)) :=
        mul_lt_mul_of_pos_left hk (by norm_num)
      _ = 4 * (κ * logL) * (S / logL) := by
        field_simp [hlog_pos.ne']
        ring
  have hone_le : 1 ≤ κ * logL := by
    have hmul := mul_le_mul hκ_ge_one hlog_ge_one (by norm_num : (0 : ℝ) ≤ 1) hκpos.le
    simpa using hmul
  calc
    2 * k / (S / logL) + 1 ≤ 4 * (κ * logL) + 1 :=
      add_le_add (le_of_lt hmain) le_rfl
    _ ≤ 4 * (κ * logL) + (κ * logL) :=
      add_le_add (le_refl (4 * (κ * logL))) hone_le
    _ = 5 * κ * logL := by ring
