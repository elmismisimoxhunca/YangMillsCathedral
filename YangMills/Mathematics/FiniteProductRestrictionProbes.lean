/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.FiniteProductRestriction

/-!
# Probes for finite-product restriction marginals
-/

namespace YangMills.Mathematics.FiniteProductRestriction.Probes

open MeasureTheory

noncomputable section

universe uG uI uJ

variable {I : Type uI} {J : Type uJ} {G : Type uG}
  [Fintype I] [Fintype J] [MeasurableSpace G]
  (μ : Measure G) [SigmaFinite μ] [IsProbabilityMeasure μ]
  (inclusion : J → I)

/-- An injective coordinate selection has the exact smaller product marginal. -/
theorem exact_injective_marginal (hinj : Function.Injective inclusion) :
    Measure.map (finiteProductRestriction (G := G) inclusion)
        (Measure.pi fun _ : I => μ) =
      Measure.pi fun _ : J => μ :=
  finiteProductRestriction.map_eq μ inclusion hinj

/-- An unrelated proposed marginal cannot replace the exact selected product. -/
theorem unrelated_marginal_blocked (hinj : Function.Injective inclusion)
    (wrong : Measure (J → G))
    (different : wrong ≠ Measure.pi fun _ : J => μ)
    (claimed : Measure.map (finiteProductRestriction (G := G) inclusion)
      (Measure.pi fun _ : I => μ) = wrong) : False := by
  apply different
  rw [← claimed]
  exact finiteProductRestriction.map_eq μ inclusion hinj

omit [Fintype I] [Fintype J] in
/-- Injectivity is load-bearing: a supplied collision directly contradicts the hypothesis needed by
the marginal theorem. -/
theorem colliding_selection_blocked
    {first second : J} (different : first ≠ second)
    (collision : inclusion first = inclusion second)
    (hinj : Function.Injective inclusion) : False :=
  different (hinj collision)

end

end YangMills.Mathematics.FiniteProductRestriction.Probes
