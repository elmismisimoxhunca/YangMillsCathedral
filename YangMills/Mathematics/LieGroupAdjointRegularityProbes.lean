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
/-- The coordinate adjoint equivalence cannot use a disconnected forward map. -/
theorem disconnected_lieGroupAdjoint_equiv_forward_blocked
    (g : G) (X : E)
    (mismatch : lieGroupAdjointCoordinatesEquiv (I := I) g X ≠
      lieGroupAdjointCoordinates (I := I) g X) : False :=
  mismatch (lieGroupAdjointCoordinatesEquiv_apply (I := I) g X)

omit [IsTopologicalGroup G] in
/-- Its inverse is forced to be the coordinate adjoint at the inverse group element. -/
theorem disconnected_lieGroupAdjoint_equiv_inverse_blocked
    (g : G) (X : E)
    (mismatch : (lieGroupAdjointCoordinatesEquiv (I := I) g).symm X ≠
      lieGroupAdjointCoordinates (I := I) g⁻¹ X) : False :=
  mismatch (lieGroupAdjointCoordinatesEquiv_symm_apply (I := I) g X)

omit [IsTopologicalGroup G] in
/-- The packaged inverse must actually undo the forward coordinate adjoint. -/
theorem broken_lieGroupAdjoint_coordinateEquiv_inverse_blocked
    (g : G) (X : E)
    (mismatch : (lieGroupAdjointCoordinatesEquiv (I := I) g).symm
      (lieGroupAdjointCoordinatesEquiv (I := I) g X) ≠ X) : False :=
  mismatch ((lieGroupAdjointCoordinatesEquiv (I := I) g).symm_apply_apply X)

omit [IsTopologicalGroup G] in
/-- The forward equivalence family cannot fail operator-valued smoothness. -/
theorem nonsmooth_lieGroupAdjoint_coordinateEquiv_blocked
    (nonsmooth : ¬ContMDiff I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun g : G => (lieGroupAdjointCoordinatesEquiv (I := I) g).toContinuousLinearMap)) : False :=
  nonsmooth (lieGroupAdjointCoordinatesEquiv_contMDiff (I := I) (G := G))

omit [IsTopologicalGroup G] in
/-- The inverse equivalence family cannot fail operator-valued smoothness. -/
theorem nonsmooth_lieGroupAdjoint_coordinateEquiv_inverse_blocked
    (nonsmooth : ¬ContMDiff I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun g : G =>
        (lieGroupAdjointCoordinatesEquiv (I := I) g).symm.toContinuousLinearMap)) : False :=
  nonsmooth (lieGroupAdjointCoordinatesEquiv_symm_contMDiff (I := I) (G := G))

omit [IsTopologicalGroup G] in
/-- General smooth adjoint regularity cannot be replaced by a nonsmooth operator-valued map. -/
theorem nonsmooth_lieGroupAdjoint_coordinateMap_blocked
    (nonsmooth : ¬ContMDiff I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun g : G => lieGroupAdjointCoordinates (I := I) g)) : False :=
  nonsmooth (lieGroupAdjointCoordinates_contMDiff (I := I) (G := G))

omit [IsTopologicalGroup G] in
/-- Joint model-coordinate evaluation inherits the proved smoothness. -/
theorem nonsmooth_lieGroupAdjoint_coordinateAction_blocked
    (nonsmooth : ¬ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun z : G × E => lieGroupAdjointCoordinates (I := I) z.1 z.2)) : False :=
  nonsmooth (lieGroupAdjointCoordinates_action_contMDiff (I := I) (G := G))

omit [IsTopologicalGroup G] in
/-- The canonical certificate rules out discontinuity without caller-supplied regularity data. -/
theorem discontinuous_canonical_lieGroupAdjoint_blocked
    (discontinuous : ¬Continuous
      (fun g : G => lieGroupAdjointCoordinates (I := I) g)) : False :=
  discontinuous (continuousLieGroupAdjointData (I := I) (G := G)).map_continuous

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
