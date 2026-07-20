/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.UniversalMaurerCartanExteriorDerivative

/-!
# Hostile probes for the universal Maurer--Cartan certificate
-/

namespace YangMills.Geometry.UniversalMaurerCartanExteriorDerivative.Probes

open Set
open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uG

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [TopologicalSpace HG]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {IG : ModelWithCorners ℝ EG HG}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ENat.LEInfty (minSmoothness ℝ 3)]

omit [FiniteDimensional ℝ EG] [IsTopologicalGroup G] in
/-- The universal smooth package retains the exact left Maurer--Cartan carrier. -/
theorem exact_universal_smooth_carrier :
    (leftMaurerCartanSmoothForm (IG := IG) (G := G)).toForm =
      leftMaurerCartanForm :=
  leftMaurerCartanSmoothForm_toForm

/-- The universal derivative is a genuine all-fields Cartan certificate. -/
noncomputable def exact_universal_exterior_certificate :
    SmoothManifoldOneFormExteriorDerivativeCertificate
      (groupLieAlgebraModelEquiv IG)
      (leftMaurerCartanSmoothForm (IG := IG) (G := G)) :=
  leftMaurerCartanExteriorDerivativeCertificate

omit [IsTopologicalGroup G] in
/-- The certificate's derivative is the exact named universal derivative, not a second form. -/
theorem exact_certificate_derivative :
    (leftMaurerCartanExteriorDerivativeCertificate (IG := IG) (G := G)).derivative =
      leftMaurerCartanExteriorDerivative :=
  leftMaurerCartanExteriorDerivativeCertificate_derivative

omit [IsTopologicalGroup G] in
/-- The certificate exposes the all-fields Cartan formula with every local-set hypothesis. -/
theorem exact_certificate_cartan_formula
    (s : Set G) (x : G) (open_s : IsOpen s) (mem_s : x ∈ s)
    (unique_s : UniqueMDiffOn IG s)
    (first second : (y : G) → TangentSpace IG y)
    (first_smooth : ManifoldTangentField.IsSmoothOn IG s first)
    (second_smooth : ManifoldTangentField.IsSmoothOn IG s second) :
    (groupLieAlgebraModelEquiv IG)
        ((leftMaurerCartanExteriorDerivativeCertificate (IG := IG) (G := G)).derivative.toForm x
          (ManifoldDifferentialForm.twoVectorArguments first second x)) =
      (leftMaurerCartanSmoothForm (IG := IG) (G := G)).toForm.oneFormCartanExpressionCoordinates
        (groupLieAlgebraModelEquiv IG) s x first second :=
  (leftMaurerCartanExteriorDerivativeCertificate (IG := IG) (G := G)).cartan_formula
    s x open_s mem_s unique_s first second first_smooth second_smooth

omit [IsTopologicalGroup G] in
/-- Its derivative carrier is exactly the normalized negative self-wedge. -/
theorem exact_universal_derivative_carrier :
    (leftMaurerCartanExteriorDerivative (IG := IG) (G := G)).toForm =
      (-1 / 2 : ℝ) • ManifoldDifferentialForm.lieBracketWedgeOneMany
        (V := GroupLieAlgebra IG G) (I := IG) (M := G) 1
        leftMaurerCartanForm leftMaurerCartanForm :=
  leftMaurerCartanExteriorDerivative_toForm

omit [IsTopologicalGroup G] in
/-- The certified universal form satisfies the exact Maurer--Cartan equation. -/
theorem exact_universal_structure_equation :
    (leftMaurerCartanExteriorDerivative (IG := IG) (G := G)).toForm +
      (1 / 2 : ℝ) • ManifoldDifferentialForm.lieBracketWedgeOneMany
        (V := GroupLieAlgebra IG G) (I := IG) (M := G) 1
        leftMaurerCartanForm leftMaurerCartanForm = 0 :=
  leftMaurerCartan_structureEquation

omit [IsTopologicalGroup G] in
/-- A substituted derivative carrier contradicts the exact certificate construction. -/
theorem mismatched_universal_derivative_blocked
    (wrong :
      (leftMaurerCartanExteriorDerivative (IG := IG) (G := G)).toForm ≠
        (-1 / 2 : ℝ) • ManifoldDifferentialForm.lieBracketWedgeOneMany
          (V := GroupLieAlgebra IG G) (I := IG) (M := G) 1
          leftMaurerCartanForm leftMaurerCartanForm) : False :=
  wrong leftMaurerCartanExteriorDerivative_toForm

omit [IsTopologicalGroup G] in
/-- A nonzero universal structure combination is impossible. -/
theorem nonzero_universal_structure_equation_blocked
    (wrong :
      (leftMaurerCartanExteriorDerivative (IG := IG) (G := G)).toForm +
        (1 / 2 : ℝ) • ManifoldDifferentialForm.lieBracketWedgeOneMany
          (V := GroupLieAlgebra IG G) (I := IG) (M := G) 1
          leftMaurerCartanForm leftMaurerCartanForm ≠ 0) : False :=
  wrong leftMaurerCartan_structureEquation

end

end YangMills.Geometry.UniversalMaurerCartanExteriorDerivative.Probes
