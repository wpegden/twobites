import Tablet.FiberAndDegreeEvent

-- [TABLET NODE: FiberAndDegreeFiberToleranceTransfer]

theorem FiberAndDegreeFiberToleranceTransfer {n m : ℕ} {p ε η : ℝ}
    (ω : TwoBiteSample n m p) (hηε : η ≤ ε)
    (hRed :
      ∀ r : Fin m,
        WithinRelativeError η ((Real.log (n : ℝ)) ^ 2) ((RedFiber ω r).card : ℝ))
    (hBlue :
      ∀ b : Fin m,
        WithinRelativeError η ((Real.log (n : ℝ)) ^ 2) ((BlueFiber ω b).card : ℝ)) :
    (∀ r : Fin m,
      WithinRelativeError ε ((Real.log (n : ℝ)) ^ 2) ((RedFiber ω r).card : ℝ)) ∧
    (∀ b : Fin m,
      WithinRelativeError ε ((Real.log (n : ℝ)) ^ 2) ((BlueFiber ω b).card : ℝ)) := by
-- BODY
  have htarget_nonneg : 0 ≤ (Real.log (n : ℝ)) ^ 2 := sq_nonneg _
  constructor
  · intro r
    unfold WithinRelativeError at *
    have hr := hRed r
    nlinarith
  · intro b
    unfold WithinRelativeError at *
    have hb := hBlue b
    nlinarith
