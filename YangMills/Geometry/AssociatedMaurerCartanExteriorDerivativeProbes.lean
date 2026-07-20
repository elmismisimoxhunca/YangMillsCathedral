/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AssociatedMaurerCartanExteriorDerivative

/-!
# Hostile probes for the certified associated Maurer--Cartan equation
-/

namespace YangMills.Geometry.AssociatedMaurerCartanExteriorDerivative.Probes

open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
    [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- The associated candidate is now the derivative selected by a genuine Cartan certificate. -/
theorem exact_associated_exterior_certificate
    (gauge : SmoothGaugeTransformation smoothBundle) :
    (associatedMaurerCartanExteriorDerivativeCertificate gauge).derivative =
      associatedMaurerCartanDerivativeCandidate gauge :=
  associatedMaurerCartanExteriorDerivativeCertificate_derivative gauge

/-- The certified associated form satisfies the exact normalized equation. -/
theorem exact_associated_structure_equation
    (gauge : SmoothGaugeTransformation smoothBundle) :
    (associatedMaurerCartanExteriorDerivativeCertificate gauge).derivative.toForm +
      (1 / 2 : ℝ) • ManifoldDifferentialForm.lieBracketWedgeOneMany
        (V := GroupLieAlgebra IG G) (I := IP) (M := P) 1
        gauge.associatedMaurerCartanPullback gauge.associatedMaurerCartanPullback = 0 :=
  associatedMaurerCartan_structureEquation gauge

/-- A nonzero substituted left-hand side contradicts the certified equation. -/
theorem nonzero_associated_structure_equation_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (wrong :
      (associatedMaurerCartanExteriorDerivativeCertificate gauge).derivative.toForm +
        (1 / 2 : ℝ) • ManifoldDifferentialForm.lieBracketWedgeOneMany
          (V := GroupLieAlgebra IG G) (I := IP) (M := P) 1
          gauge.associatedMaurerCartanPullback gauge.associatedMaurerCartanPullback ≠ 0) : False :=
  wrong (associatedMaurerCartan_structureEquation gauge)

end

end YangMills.Geometry.AssociatedMaurerCartanExteriorDerivative.Probes
