import Tablet.RedFiber
import Tablet.BlueFiber
import Tablet.TwoBiteEventProbabilityInjectionOnly

open Classical

-- [TABLET NODE: FiberAndDegreeFiberSizeInjectionMarginal]

theorem FiberAndDegreeFiberSizeInjectionMarginal {n m : ℕ} {p : ℝ}
    (redSide : Bool) (x : Fin m) (E : ℕ → Prop) :
    TwoBiteEventProbability n m p
      (fun ω =>
        E ((if redSide then RedFiber ω x else BlueFiber ω x).card)) =
    (((Finset.univ.filter
      (fun π : Fin n ↪ (Fin m × Fin m) =>
        E ((Finset.univ.filter
          (fun v : Fin n => if redSide then (π v).1 = x else (π v).2 = x)).card))).card : ℝ) *
      UniformInjectionWeight n m) := by
-- BODY
  classical
  cases redSide
  · let event : (Fin n ↪ (Fin m × Fin m)) → Prop :=
      fun π => E ((Finset.univ.filter (fun v : Fin n => (π v).2 = x)).card)
    simpa [event, BlueFiber, TwoBiteBlueProjection, TwoBiteEmbedding] using
      (TwoBiteEventProbabilityInjectionOnly (n := n) (m := m) (p := p) event)
  · let event : (Fin n ↪ (Fin m × Fin m)) → Prop :=
      fun π => E ((Finset.univ.filter (fun v : Fin n => (π v).1 = x)).card)
    simpa [event, RedFiber, TwoBiteRedProjection, TwoBiteEmbedding] using
      (TwoBiteEventProbabilityInjectionOnly (n := n) (m := m) (p := p) event)
