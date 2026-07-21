/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.LieGroupLeftMaurerCartanCoordinateSmooth

/-!
# Probes for smooth left Maurer--Cartan coordinates

The probes pin the parameter-dependent inverse-left-translation derivative, its exact tangent
coordinate transport, and centerwise smoothness. They do not claim the nested metric Hom-bundle
section is already smooth.
-/

namespace YangMills.Geometry.LieGroupLeftMaurerCartanCoordinateSmooth.Probes

open scoped Manifold ContDiff

noncomputable section

universe uE uH uG

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]

omit [LieGroup I ∞ G] in
/-- The parameterized derivative is exactly the existing canonical Maurer--Cartan application. -/
theorem exact_canonical_application (x : G) (v : TangentSpace I x) :
    mfderiv I I (fun y : G => x⁻¹ * y) x v = leftMaurerCartanApply x v :=
  parameterizedLeftTranslationDerivative_apply x v

/-- The coordinate family retains the exact `x⁻¹ * y` derivative rather than an unrelated linear
map. -/
theorem exact_parameterized_derivative (center : G) :
    leftMaurerCartanInTangentCoordinates (I := I) center =
      inTangentCoordinates I I (fun x : G => x)
        (fun x : G => x⁻¹ * x)
        (fun x : G => mfderiv I I (fun y : G => x⁻¹ * y) x) center :=
  rfl

/-- Every exact center has the required local smooth coefficient family. -/
theorem exact_centerwise_smoothness (center : G) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (leftMaurerCartanInTangentCoordinates (I := I) center) center :=
  leftMaurerCartanInTangentCoordinates_smoothAt center

/-- An unrelated coordinate family cannot replace the exact derivative when distinguished at the
center. -/
theorem unrelated_coordinate_family_blocked
    (center : G) (wrong : G → (E →L[ℝ] E))
    (different : wrong center ≠ leftMaurerCartanInTangentCoordinates (I := I) center center)
    (claimed : wrong = leftMaurerCartanInTangentCoordinates (I := I) center) : False := by
  apply different
  rw [claimed]

end

end YangMills.Geometry.LieGroupLeftMaurerCartanCoordinateSmooth.Probes
