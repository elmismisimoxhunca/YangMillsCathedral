/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalVerticalTangentGeneration

/-!
# Hostile probes for vertical tangent generation
-/

namespace YangMills.Geometry.PrincipalVerticalTangentGeneration.Probes

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
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- Every projection-vertical tangent is an actual infinitesimal orbit vector. -/
theorem exact_vertical_generation
    (p : P) (v : TangentSpace IP p)
    (vertical : mfderiv IP IB torsor.projection p v = 0) :
    ∃ X : GroupLieAlgebra IG G, v = principalFundamentalVector smoothBundle p X :=
  vertical_tangent_exists_fundamental p v vertical

/-- The exact connection-form value is the unique vertical generator. -/
theorem exact_connection_generator
    (connection : PointwisePrincipalConnectionData smoothBundle)
    (p : P) (v : TangentSpace IP p)
    (vertical : mfderiv IP IB torsor.projection p v = 0) :
    v = principalFundamentalVector smoothBundle p (connection.form.evalOne p v) :=
  vertical_tangent_eq_fundamental_connection connection p v vertical

/-- Generator uniqueness is derived rather than supplied. -/
theorem exact_unique_generator
    (connection : PointwisePrincipalConnectionData smoothBundle)
    (p : P) (v : TangentSpace IP p)
    (vertical : mfderiv IP IB torsor.projection p v = 0) :
    ∃! X : GroupLieAlgebra IG G, v = principalFundamentalVector smoothBundle p X :=
  vertical_tangent_existsUnique_fundamental connection p v vertical

/-- Replacing the recovered generator by a distinct one contradicts uniqueness. -/
theorem mismatched_vertical_generator_blocked
    (connection : PointwisePrincipalConnectionData smoothBundle)
    (p : P) (v : TangentSpace IP p)
    (X : GroupLieAlgebra IG G)
    (represents : v = principalFundamentalVector smoothBundle p X)
    (changed : X ≠ connection.form.evalOne p v) : False := by
  apply changed
  rw [represents, connection.vertical_normalization]

end

end YangMills.Geometry.PrincipalVerticalTangentGeneration.Probes
