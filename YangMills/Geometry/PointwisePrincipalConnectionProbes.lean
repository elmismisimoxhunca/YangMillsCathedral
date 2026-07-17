/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PointwisePrincipalConnection

/-!
# Hostile probes for pointwise principal connection forms

These probes independently enforce vertical normalization, infinitesimal freeness, and the
`Ad(g⁻¹)` right-equivariance convention. Smooth-section regularity remains outside this layer.
-/

namespace YangMills.Geometry.Probes

open scoped Manifold ContDiff

universe uEG uHG uEB uHB uEP uHP uG uB uP

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
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- Orbit maps used to define fundamental vectors are genuinely smooth. -/
theorem principal_orbitMap_is_smooth
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle) (p : P) :
    ContMDiff IG IP ∞ (principalOrbitMap torsor p) :=
  principalOrbitMap_smooth smoothBundle p

/-- Right translations used in equivariance are genuinely smooth. -/
theorem principal_rightTranslation_is_smooth
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle) (g : G) :
    ContMDiff IP IP ∞ (principalRightTranslation torsor g) :=
  principalRightTranslation_smooth smoothBundle g

/-- A connection form cannot fail to recover an infinitesimal vertical generator. -/
theorem broken_vertical_normalization_blocked
    (connection : PointwisePrincipalConnectionData smoothBundle)
    (p : P) (X : GroupLieAlgebra IG G)
    (mismatch : connection.form.evalOne p
      (principalFundamentalVector smoothBundle p X) ≠ X) : False :=
  mismatch (connection.vertical_normalization p X)

/-- A noninjective infinitesimal orbit map is incompatible with vertical normalization. -/
theorem noninjective_fundamentalVector_blocked
    (connection : PointwisePrincipalConnectionData smoothBundle)
    (p : P) (X Y : GroupLieAlgebra IG G) (distinct : X ≠ Y)
    (sameVector : principalFundamentalVector smoothBundle p X =
      principalFundamentalVector smoothBundle p Y) : False :=
  distinct (connection.fundamentalVector_injective p sameVector)

/-- The right-equivariance convention must use `Ad(g⁻¹)` on the form value. -/
theorem wrong_connection_equivariance_blocked
    (connection : PointwisePrincipalConnectionData smoothBundle)
    (p : P) (g : G) (v : TangentSpace IP p)
    (mismatch : connection.form.evalOne (torsor.rightAction p g)
        (principalRightTranslationDifferential smoothBundle p g v) ≠
      YangMills.Mathematics.lieGroupAdjoint IG g⁻¹ (connection.form.evalOne p v)) : False :=
  mismatch (connection.right_equivariant p g v)

end YangMills.Geometry.Probes
