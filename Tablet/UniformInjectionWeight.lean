import Tablet.Preamble

-- [TABLET NODE: UniformInjectionWeight]

noncomputable def UniformInjectionWeight (n m : ℕ) : ℝ :=
-- BODY
  if Fintype.card (Fin n ↪ (Fin m × Fin m)) = 0 then
    0
  else
    ((Fintype.card (Fin n ↪ (Fin m × Fin m)) : ℝ)⁻¹)
