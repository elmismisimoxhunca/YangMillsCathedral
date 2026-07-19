/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvature
import YangMills.Mathematics.ManifoldDifferentialFormNormedCoordinates

/-!
# Normed-coordinate carriers for derived principal curvature

This module applies the corner-aware within-set coordinate carrier to one exact principal connection,
its certified exterior derivative, and the curvature derived from both. It proves the coordinate
form of Freed's equation (1.13) using the same tangent transport and canonical group-Lie-algebra
bracket throughout.

The derivative term here is the coordinate pullback of the connection's supplied manifold exterior-
derivative certificate. It is not yet identified with normed-space `extDerivWithin`; that naturality
statement remains explicit debt. Consequently this module does not claim coordinate Bianchi.
-/

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff
open YangMills.Mathematics

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
    [FiniteDimensional ℝ EG]

namespace PrincipalConnectionData

/-- Within-set normed-coordinate carrier of the exact principal connection one-form. -/
noncomputable def connectionCoordinatePullbackWithin
    (connection : PrincipalConnectionData smoothBundle)
    (map : EP → P) (source : Set EP) : NormedSpaceDifferentialForm EP EG 1 :=
  connection.pointwise.form.normedCoordinatePullbackWithinAlong
    (groupLieAlgebraModelEquiv IG) 1 map source

/-- Within-set normed-coordinate carrier of the curvature derived from this exact connection and
exterior-derivative certificate. -/
noncomputable def curvatureCoordinatePullbackWithin
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (map : EP → P) (source : Set EP) : NormedSpaceDifferentialForm EP EG 2 :=
  (connection.curvatureForm exterior).toForm.normedCoordinatePullbackWithinAlong
    (groupLieAlgebraModelEquiv IG) 2 map source

/-- Inverse-chart coordinate carrier of the exact connection one-form. -/
noncomputable def connectionCoordinatesInExtChartAt
    (connection : PrincipalConnectionData smoothBundle) (p : P) :
    NormedSpaceDifferentialForm EP EG 1 :=
  connection.pointwise.form.inExtChartAt (groupLieAlgebraModelEquiv IG) 1 p

/-- Inverse-chart coordinate carrier of the exact derived curvature. -/
noncomputable def curvatureCoordinatesInExtChartAt
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) (p : P) :
    NormedSpaceDifferentialForm EP EG 2 :=
  (connection.curvatureForm exterior).toForm.inExtChartAt
    (groupLieAlgebraModelEquiv IG) 2 p

end PrincipalConnectionData

namespace PrincipalConnectionExteriorDerivativeData

/-- Within-set normed-coordinate carrier of the exact certified derivative `dΘ`. -/
noncomputable def coordinatePullbackWithin
    {connection : PrincipalConnectionData smoothBundle}
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (map : EP → P) (source : Set EP) : NormedSpaceDifferentialForm EP EG 2 :=
  exterior.certificate.derivative.toForm.normedCoordinatePullbackWithinAlong
    (groupLieAlgebraModelEquiv IG) 2 map source

/-- Inverse-chart coordinate carrier of the exact certified derivative `dΘ`. -/
noncomputable def coordinatesInExtChartAt
    {connection : PrincipalConnectionData smoothBundle}
    (exterior : PrincipalConnectionExteriorDerivativeData connection) (p : P) :
    NormedSpaceDifferentialForm EP EG 2 :=
  exterior.certificate.derivative.toForm.inExtChartAt
    (groupLieAlgebraModelEquiv IG) 2 p

end PrincipalConnectionExteriorDerivativeData

namespace PrincipalConnectionData

set_option backward.isDefEq.respectTransparency false in
/-- Coordinate pullback preserves the exact same-connection curvature equation. The derivative term
is still the pullback of the manifold certificate, not `extDerivWithin` of the coordinate one-form. -/
theorem curvatureCoordinatePullbackWithin_eq
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (map : EP → P) (source : Set EP) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    connection.curvatureCoordinatePullbackWithin exterior map source = fun x =>
      exterior.coordinatePullbackWithin map source x + (1 / 2 : ℝ) •
        ContinuousAlternatingMap.continuousBilinearWedgeOneMany
          (groupLieAlgebraCoordinateBracketCLM (I := IG) (G := G)) 1
          (connection.connectionCoordinatePullbackWithin map source x)
          (connection.connectionCoordinatePullbackWithin map source x) := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have wedge_eq :
      connection.pointwise.form.lieBracketWedgeOne connection.pointwise.form =
        connection.pointwise.form.lieBracketWedgeOneMany 1 connection.pointwise.form := by
    funext p
    ext vectors
    rw [ManifoldDifferentialForm.lieBracketWedgeOne_apply,
      ManifoldDifferentialForm.lieBracketWedgeOneMany_apply, Fin.sum_univ_two]
    have remove_zero_eq : Fin.removeNth 0 vectors = fun _ => vectors 1 := by
      funext i
      fin_cases i
      rfl
    have remove_one_eq : Fin.removeNth 1 vectors = fun _ => vectors 0 := by
      funext i
      fin_cases i
      rfl
    rw [remove_zero_eq, remove_one_eq]
    norm_num
    rw [sub_eq_add_neg, lie_skew]
  rw [PrincipalConnectionData.curvatureCoordinatePullbackWithin,
    PrincipalConnectionData.curvatureForm_toForm,
    ManifoldDifferentialForm.normedCoordinatePullbackWithinAlong_add,
    ManifoldDifferentialForm.normedCoordinatePullbackWithinAlong_smul,
    wedge_eq,
    ManifoldDifferentialForm.normedCoordinatePullbackWithinAlong_lieBracketWedgeOneMany]
  rfl

/-- Inverse-chart specialization of the exact same-connection curvature equation. Its tangent
transport is the corner-aware within-range derivative from `inExtChartAt`. -/
theorem curvatureCoordinatesInExtChartAt_eq
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) (p : P) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    connection.curvatureCoordinatesInExtChartAt exterior p = fun x =>
      exterior.coordinatesInExtChartAt p x + (1 / 2 : ℝ) •
        ContinuousAlternatingMap.continuousBilinearWedgeOneMany
          (groupLieAlgebraCoordinateBracketCLM (I := IG) (G := G)) 1
          (connection.connectionCoordinatesInExtChartAt p x)
          (connection.connectionCoordinatesInExtChartAt p x) := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  simpa [connectionCoordinatesInExtChartAt, curvatureCoordinatesInExtChartAt,
    PrincipalConnectionExteriorDerivativeData.coordinatesInExtChartAt,
    connectionCoordinatePullbackWithin, curvatureCoordinatePullbackWithin,
    PrincipalConnectionExteriorDerivativeData.coordinatePullbackWithin,
    ManifoldDifferentialForm.inExtChartAt] using
    connection.curvatureCoordinatePullbackWithin_eq exterior
      (extChartAt IP p).symm (Set.range ⇑IP)

end PrincipalConnectionData

end

end YangMills.Geometry
