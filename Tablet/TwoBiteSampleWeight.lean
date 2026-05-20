import Tablet.TwoBiteSample
import Tablet.GnpGraphWeight
import Tablet.UniformInjectionWeight

-- [TABLET NODE: TwoBiteSampleWeight]

noncomputable def TwoBiteSampleWeight {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) : ℝ :=
-- BODY
  GnpGraphWeight p ω.1 *
    GnpGraphWeight p ω.2.1 *
      UniformInjectionWeight n m
