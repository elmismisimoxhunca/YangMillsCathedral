/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.AlternatingMapDegreeTwoBilinear

/-!
# Hostile probes for degree-two alternating-map bilinear packaging
-/

namespace YangMills.Mathematics.Probes

universe uR uE uV

noncomputable section

variable
    {R : Type uR} [CommSemiring R]
    {E : Type uE} [AddCommMonoid E] [Module R E]
    {V : Type uV} [AddCommMonoid V] [Module R V]

/-- The algebraic adapter cannot change a degree-two alternating-map value. -/
theorem alternatingMap_bilinearValue_replacement_blocked
    (form : E [⋀^Fin 2]→ₗ[R] V) (first second : E)
    (mismatch :
      alternatingMapFinTwoToBilinear form first second ≠ form ![first, second]) : False :=
  mismatch (alternatingMapFinTwoToBilinear_apply form first second)

/-- The packaged first argument cannot fail additivity. -/
theorem nonadditive_alternatingMapBilinear_blocked
    (form : E [⋀^Fin 2]→ₗ[R] V) (first second third : E)
    (mismatch :
      alternatingMapFinTwoToBilinear form (first + second) third ≠
        alternatingMapFinTwoToBilinear form first third +
          alternatingMapFinTwoToBilinear form second third) : False := by
  apply mismatch
  exact congrArg (fun linear => linear third)
    (map_add (alternatingMapFinTwoToBilinear form) first second)

variable [TopologicalSpace E] [TopologicalSpace V]

/-- Forgetting continuity cannot replace the value of a continuous alternating map. -/
theorem continuousAlternatingMap_bilinearValue_replacement_blocked
    (form : E [⋀^Fin 2]→L[R] V) (first second : E)
    (mismatch :
      continuousAlternatingMapFinTwoToBilinear form first second ≠
        form ![first, second]) : False :=
  mismatch (continuousAlternatingMapFinTwoToBilinear_apply form first second)

end

end YangMills.Mathematics.Probes
