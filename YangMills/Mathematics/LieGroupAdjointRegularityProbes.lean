/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupAdjointRegularity

/-!
# Probes for Lie-group adjoint regularity
-/

namespace YangMills.Mathematics.Probes

open scoped Manifold ContDiff

universe uE uH uG

noncomputable section

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]

omit [IsTopologicalGroup G] in
/-- The certificate cannot coexist with a discontinuous joint adjoint action. -/
theorem discontinuous_lieGroupAdjoint_action_blocked
    (data : ContinuousLieGroupAdjointData (I := I) (G := G))
    (discontinuous : ¬Continuous
      (fun z : G × GroupLieAlgebra I G => lieGroupAdjoint I z.1 z.2)) : False :=
  discontinuous data.action_continuous

/-- Inversion cannot disconnect the associated-bundle `Ad(g⁻¹)` action from the same certificate. -/
theorem discontinuous_lieGroupAdjoint_inverseAction_blocked
    (data : ContinuousLieGroupAdjointData (I := I) (G := G))
    (discontinuous : ¬Continuous
      (fun z : G × GroupLieAlgebra I G => lieGroupAdjoint I z.1⁻¹ z.2)) : False :=
  discontinuous data.inverseAction_continuous

omit [IsTopologicalGroup G] in
/-- The certificate specifically controls the derivative-defined adjoint map in model coordinates. -/
theorem disconnected_lieGroupAdjoint_coordinateMap_blocked
    (data : ContinuousLieGroupAdjointData (I := I) (G := G))
    (discontinuous : ¬Continuous
      (fun g : G => lieGroupAdjointCoordinates (I := I) g)) : False :=
  discontinuous data.map_continuous

end

end YangMills.Mathematics.Probes
