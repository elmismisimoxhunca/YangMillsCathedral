/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupInvariantFieldChartIdentity

namespace YangMills.Mathematics.LieGroupInvariantFieldChartIdentity.Probes

open Set ChartedSpace
open scoped Manifold ContDiff

universe uE uH uG

noncomputable section

variable {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type uG} [Group G] [TopologicalSpace G]
    [ChartedSpace H G] [LieGroup I ∞ G]

/-- Both exact product-range partial normalizations are retained. -/
theorem exact_partial_normalizations (X Y : E) :
    let c := extChartAt I (1 : G)
    let a := c (1 : G)
    let F := fun z : E × E => c (c.symm z.1 * c.symm z.2)
    fderivWithin ℝ F (range I ×ˢ range I) (a, a) (0, X) = X ∧
      fderivWithin ℝ F (range I ×ˢ range I) (a, a) (Y, 0) = Y :=
  ⟨centeredChartMul_second_normalization I X,
    centeredChartMul_first_normalization I Y⟩

/-- The normalized partial fields have zero bracket on the exact model range at the center. -/
theorem exact_partial_field_bracket
    (X Y : E) :
    let c := extChartAt I (1 : G)
    let a := c (1 : G)
    let F := fun z : E × E => c (c.symm z.1 * c.symm z.2)
    VectorField.lieBracketWithin ℝ
      (fun x => fderivWithin ℝ F (range I ×ˢ range I) (x, a) (0, X))
      (fun x => fderivWithin ℝ F (range I ×ˢ range I) (a, x) (Y, 0))
      (range I) a = 0 :=
  centeredChartMul_partialFields_lieBracketWithin_identity I X Y

/-- The left-invariant coordinate value is the exact second partial at the identity. -/
theorem exact_left_invariant_identity_coordinate (X : GroupLieAlgebra I G) :
    let c := extChartAt I (1 : G)
    let a := c (1 : G)
    let F := fun z : E × E => c (c.symm z.1 * c.symm z.2)
    extChartCoordinateField I (1 : G) (mulInvariantVectorField X) a =
      fderivWithin ℝ F (range I ×ˢ range I) (a, a)
        (0, groupLieAlgebraModelEquiv I X) :=
  extChartCoordinateField_mulInvariantVectorField_eq_secondPartial_identity I X

/-- The right-invariant coordinate value is the exact first partial at the identity. -/
theorem exact_right_invariant_identity_coordinate (Y : GroupLieAlgebra I G) :
    let c := extChartAt I (1 : G)
    let a := c (1 : G)
    let F := fun z : E × E => c (c.symm z.1 * c.symm z.2)
    extChartCoordinateField I (1 : G) (mulRightInvariantVectorField I Y) a =
      fderivWithin ℝ F (range I ×ˢ range I) (a, a)
        (groupLieAlgebraModelEquiv I Y, 0) :=
  extChartCoordinateField_mulRightInvariantVectorField_eq_firstPartial_identity I Y

/-- A nonzero normalized partial-field bracket contradicts Schwarz cancellation. -/
theorem nonzero_partial_field_bracket_blocked
    (X Y : E)
    (nonzero : (let c := extChartAt I (1 : G)
      let a := c (1 : G)
      let F := fun z : E × E => c (c.symm z.1 * c.symm z.2)
      VectorField.lieBracketWithin ℝ
        (fun x => fderivWithin ℝ F (range I ×ˢ range I) (x, a) (0, X))
        (fun x => fderivWithin ℝ F (range I ×ˢ range I) (a, x) (Y, 0))
        (range I) a ≠ 0)) : False :=
  nonzero (centeredChartMul_partialFields_lieBracketWithin_identity I X Y)

/-- A changed left-invariant center coordinate contradicts the exact identification. -/
theorem changed_left_identity_coordinate_blocked
    (X : GroupLieAlgebra I G)
    (changed : extChartCoordinateField I (1 : G) (mulInvariantVectorField X)
      ((extChartAt I (1 : G)) 1) ≠ groupLieAlgebraModelEquiv I X) : False :=
  changed (extChartCoordinateField_mulInvariantVectorField_identity I X)

/-- A changed right-invariant center coordinate contradicts the exact identification. -/
theorem changed_right_identity_coordinate_blocked
    (Y : GroupLieAlgebra I G)
    (changed : extChartCoordinateField I (1 : G) (mulRightInvariantVectorField I Y)
      ((extChartAt I (1 : G)) 1) ≠ groupLieAlgebraModelEquiv I Y) : False :=
  changed (extChartCoordinateField_mulRightInvariantVectorField_identity I Y)

end

end YangMills.Mathematics.LieGroupInvariantFieldChartIdentity.Probes
