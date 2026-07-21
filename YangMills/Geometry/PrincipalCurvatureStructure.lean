/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvature

/-!
# Structural semantics for principal curvature

Freed (1.14)--(1.15) says that principal curvature is right `Ad(g⁻¹)`-equivariant and horizontal.
This file states those properties using the derivatives of the actual bundle projection and right
action. `PrincipalCurvatureStructureCertificate` is indexed by the curvature derived from one exact
connection and exterior-derivative certificate; it cannot certify an unrelated two-form.

This file retains the explicit generic certificate surface for contexts without the later
finite-dimensional calculus. `PrincipalCurvatureStructureFiniteDimensional` derives the exact
certificate from the Cartan certificate and connection laws when all manifold models are finite
dimensional. Neither module constructs a connection, curvature, or Yang--Mills field.
-/

namespace YangMills.Geometry

open scoped Manifold ContDiff

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)

/-- A Lie-algebra-valued two-form on the principal-bundle total space is horizontal when it
vanishes whenever one argument is vertical, with verticality detected intrinsically by the
derivative of the bundle projection. -/
def PrincipalTwoForm.IsHorizontal
    (_smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2) : Prop :=
  ∀ (p : P) (v : Fin 2 → TangentSpace IP p),
    (∃ i, mfderiv IP IB torsor.projection p (v i) = 0) → form p v = 0

/-- A principal two-form obeys Freed's right-equivariance law when pullback along every actual right
translation equals `Ad(g⁻¹)` on its Lie-algebra value. -/
def PrincipalTwoForm.IsRightAdEquivariant
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2) : Prop :=
  ∀ (g : G) (p : P) (v : Fin 2 → TangentSpace IP p),
    form (torsor.rightAction p g)
        (fun i => principalRightTranslationDifferential smoothBundle p g (v i)) =
      YangMills.Mathematics.lieGroupAdjoint IG g⁻¹ (form p v)

/-- Explicit structural certificate for the exact curvature derived from one connection and its
certified exterior derivative. The generic carrier cannot accept a disconnected curvature witness;
the finite-dimensional specialization is derived automatically in a later module. -/
structure PrincipalCurvatureStructureCertificate
    [FiniteDimensional ℝ EG]
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) : Prop where
  /-- Freed (1.15): the derived curvature vanishes on vertical insertion. -/
  horizontal : PrincipalTwoForm.IsHorizontal smoothBundle
    (connection.curvatureForm exterior).toForm
  /-- Freed (1.14): the derived curvature transforms by `Ad(g⁻¹)` under right translation. -/
  right_ad_equivariant : PrincipalTwoForm.IsRightAdEquivariant smoothBundle
    (connection.curvatureForm exterior).toForm

end

end YangMills.Geometry
