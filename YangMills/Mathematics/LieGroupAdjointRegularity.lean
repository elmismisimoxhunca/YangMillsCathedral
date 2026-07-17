/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupAdjoint

/-!
# Regularity certificate for the Lie-group adjoint representation

The adjoint map was defined as the manifold derivative of conjugation and its algebraic laws were
proved previously. The pinned Mathlib API does not directly expose the parameter-dependent theorem
needed here in the project's intrinsic tangent coordinates. This file isolates that remaining general
manifold-calculus fact as an explicit continuity certificate for the map `g ↦ Ad(g)`.

No gauge group or certificate inhabitant is constructed. The interface is reusable and independent
of principal bundles and Yang--Mills theory.
-/

namespace YangMills.Mathematics

open scoped Manifold ContDiff

universe uE uH uG

noncomputable section

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]

/-- The adjoint map transported to the declared normed model coordinates. -/
def lieGroupAdjointCoordinates (g : G) : E →L[ℝ] E :=
  ((groupLieAlgebraModelEquiv (G := G) I :
      GroupLieAlgebra I G →L[ℝ] E).comp
    ((lieGroupAdjoint I g).comp
      (groupLieAlgebraModelEquiv (G := G) I).symm.toContinuousLinearMap))

/-- Explicit certificate that the derivative-defined adjoint representation varies continuously in
the group parameter. This should eventually be discharged by reusable parameter-dependent manifold
derivative infrastructure. -/
structure ContinuousLieGroupAdjointData : Prop where
  map_continuous : Continuous (fun g : G => lieGroupAdjointCoordinates (I := I) g)

namespace ContinuousLieGroupAdjointData

omit [IsTopologicalGroup G] in
/-- Joint continuity of `(g,X) ↦ Ad(g)X` follows from continuity into continuous linear maps. -/
theorem action_continuous (data : ContinuousLieGroupAdjointData (I := I) (G := G)) :
    Continuous (fun z : G × GroupLieAlgebra I G => lieGroupAdjoint I z.1 z.2) := by
  let coordinates := groupLieAlgebraModelEquiv (G := G) I
  have inputCoordinates : Continuous
      (fun z : G × GroupLieAlgebra I G => (z.1, coordinates z.2)) :=
    continuous_fst.prodMk (coordinates.continuous.comp continuous_snd)
  have evaluated : Continuous (fun z : G × E =>
      lieGroupAdjointCoordinates (I := I) z.1 z.2) :=
    (data.map_continuous.comp continuous_fst).clm_apply continuous_snd
  have transported := coordinates.symm.continuous.comp (evaluated.comp inputCoordinates)
  simpa [coordinates, lieGroupAdjointCoordinates, Function.comp_def] using transported

/-- Joint continuity also holds for the inverse-adjoint action used by associated bundles. -/
theorem inverseAction_continuous (data : ContinuousLieGroupAdjointData (I := I) (G := G)) :
    Continuous (fun z : G × GroupLieAlgebra I G => lieGroupAdjoint I z.1⁻¹ z.2) := by
  have input : Continuous (fun z : G × GroupLieAlgebra I G => (z.1⁻¹, z.2)) :=
    (continuous_inv.comp continuous_fst).prodMk continuous_snd
  simpa [Function.comp_def] using data.action_continuous.comp input

end ContinuousLieGroupAdjointData

end

end YangMills.Mathematics
