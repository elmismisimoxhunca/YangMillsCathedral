/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionCoordinateRegularity
import YangMills.Mathematics.NormedCoordinateBianchiWithin

/-!
# Conditional bridge from principal curvature coordinates to coordinate Bianchi

This module isolates the precise naturality statement still needed to connect the pulled-back
manifold exterior-derivative certificate to Mathlib's `extDerivWithin`. The tangent-transport source
and the calculus set are deliberately separate: for an inverse chart they are respectively
`Set.range IP` and the actual chart target.

Assuming this exact same-connection naturality statement, the coordinate carrier of the derived
principal curvature agrees on the calculus set with `groupLieAlgebraCoordinateCurvatureWithin`.
The already-proved normed-coordinate Bianchi theorem then yields a zero covariant expression for the
exact derived curvature carrier. No Bianchi witness is accepted, and no naturality theorem is
claimed here.
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

/-- Exact local naturality obligation for one connection-indexed derivative certificate. The
coordinate tangent transport uses `transportSource`, while `extDerivWithin` uses `calculusSet`. -/
def PrincipalConnectionCoordinateExteriorDerivativeNaturalityOn
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (map : EP → P) (transportSource calculusSet : Set EP) : Prop :=
  Set.EqOn (exterior.coordinatePullbackWithin map transportSource)
    (extDerivWithin
      (connection.connectionCoordinatePullbackWithin map transportSource) calculusSet)
    calculusSet

namespace PrincipalConnectionExteriorDerivativeData

/-- Exact inverse-chart naturality obligation. It retains the corner-aware model range for tangent
transport and the actual chart target for exterior calculus. -/
def IsNaturalInExtChartAt
    {connection : PrincipalConnectionData smoothBundle}
    (exterior : PrincipalConnectionExteriorDerivativeData connection) (p : P) : Prop :=
  PrincipalConnectionCoordinateExteriorDerivativeNaturalityOn connection exterior
    (extChartAt IP p).symm (Set.range ⇑IP) (extChartAt IP p).target

end PrincipalConnectionExteriorDerivativeData

namespace PrincipalConnectionData

/-- Under exact exterior-derivative naturality, the coordinate carrier of the derived principal
curvature agrees on the calculus set with the curvature built directly by `extDerivWithin`. -/
theorem curvatureCoordinatePullbackWithin_eqOn_coordinateCurvature
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (map : EP → P) (transportSource calculusSet : Set EP)
    (naturality : PrincipalConnectionCoordinateExteriorDerivativeNaturalityOn
      connection exterior map transportSource calculusSet) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    Set.EqOn (connection.curvatureCoordinatePullbackWithin exterior map transportSource)
      (groupLieAlgebraCoordinateCurvatureWithin (I := IG) (G := G)
        (connection.connectionCoordinatePullbackWithin map transportSource) calculusSet)
      calculusSet := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  intro x mem_calculus
  rw [connection.curvatureCoordinatePullbackWithin_eq exterior map transportSource]
  unfold groupLieAlgebraCoordinateCurvatureWithin
  dsimp only
  rw [naturality mem_calculus]

/-- The within-set covariant exterior expression of the exact derived principal-curvature carrier
vanishes once naturality and the coordinate regularity hypotheses are supplied. Bianchi itself is
derived by `groupLieAlgebraCoordinate_bianchiWithin`, not stored as data. -/
theorem curvatureCoordinatePullbackWithin_coordinateBianchi
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (map : EP → P) (transportSource calculusSet : Set EP) (x : EP) {r : ℕ∞}
    (naturality : PrincipalConnectionCoordinateExteriorDerivativeNaturalityOn
      connection exterior map transportSource calculusSet)
    (connection_regular : ContDiffWithinAt ℝ r
      (connection.connectionCoordinatePullbackWithin map transportSource) calculusSet x)
    (regularity_order : minSmoothness ℝ 2 ≤ r)
    (unique_calculus : UniqueDiffOn ℝ calculusSet)
    (mem_closure_interior : x ∈ closure (interior calculusSet))
    (mem_calculus : x ∈ calculusSet) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin (I := IG) (G := G)
      (connection.connectionCoordinatePullbackWithin map transportSource) calculusSet
      (connection.curvatureCoordinatePullbackWithin exterior map transportSource) x = 0 := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  let coordinateConnection := connection.connectionCoordinatePullbackWithin map transportSource
  let exactCurvature := connection.curvatureCoordinatePullbackWithin exterior map transportSource
  let coordinateCurvature := groupLieAlgebraCoordinateCurvatureWithin
    (I := IG) (G := G) coordinateConnection calculusSet
  have curvature_eq : Set.EqOn exactCurvature coordinateCurvature calculusSet :=
    connection.curvatureCoordinatePullbackWithin_eqOn_coordinateCurvature exterior map
      transportSource calculusSet naturality
  have derivative_eq :
      extDerivWithin exactCurvature calculusSet x =
        extDerivWithin coordinateCurvature calculusSet x :=
    extDerivWithin_congr' curvature_eq mem_calculus
  have coordinate_bianchi := groupLieAlgebraCoordinate_bianchiWithin
    (I := IG) (G := G) coordinateConnection calculusSet x connection_regular
      regularity_order unique_calculus mem_closure_interior mem_calculus
  change extDerivWithin exactCurvature calculusSet x +
    (coordinateConnection x).continuousBilinearWedgeOneMany
      (groupLieAlgebraCoordinateBracketCLM (I := IG) (G := G)) 2
      (exactCurvature x) = 0
  rw [derivative_eq, curvature_eq mem_calculus]
  exact coordinate_bianchi

/-- Inverse-chart specialization: the exact principal-curvature carrier agrees with coordinate
curvature on the actual chart target. -/
theorem curvatureCoordinatesInExtChartAt_eqOn_coordinateCurvature
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) (p : P)
    (naturality : exterior.IsNaturalInExtChartAt p) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    Set.EqOn (connection.curvatureCoordinatesInExtChartAt exterior p)
      (groupLieAlgebraCoordinateCurvatureWithin (I := IG) (G := G)
        (connection.connectionCoordinatesInExtChartAt p) (extChartAt IP p).target)
      (extChartAt IP p).target := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  simpa [connectionCoordinatesInExtChartAt, curvatureCoordinatesInExtChartAt,
    PrincipalConnectionExteriorDerivativeData.IsNaturalInExtChartAt,
    PrincipalConnectionCoordinateExteriorDerivativeNaturalityOn,
    connectionCoordinatePullbackWithin, curvatureCoordinatePullbackWithin,
    PrincipalConnectionExteriorDerivativeData.coordinatePullbackWithin,
    ManifoldDifferentialForm.inExtChartAt] using
    connection.curvatureCoordinatePullbackWithin_eqOn_coordinateCurvature exterior
      (extChartAt IP p).symm (Set.range ⇑IP) (extChartAt IP p).target naturality

/-- Inverse-chart conditional Bianchi theorem for the exact derived principal curvature. All
regularity, uniqueness, membership, and closure-of-interior hypotheses remain attached to the
actual chart target. -/
theorem curvatureCoordinatesInExtChartAt_coordinateBianchi
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (p : P) (x : EP) {r : ℕ∞}
    (naturality : exterior.IsNaturalInExtChartAt p)
    (connection_regular : ContDiffWithinAt ℝ r
      (connection.connectionCoordinatesInExtChartAt p) (extChartAt IP p).target x)
    (regularity_order : minSmoothness ℝ 2 ≤ r)
    (unique_target : UniqueDiffOn ℝ (extChartAt IP p).target)
    (mem_closure_interior : x ∈ closure (interior (extChartAt IP p).target))
    (mem_target : x ∈ (extChartAt IP p).target) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin (I := IG) (G := G)
      (connection.connectionCoordinatesInExtChartAt p) (extChartAt IP p).target
      (connection.curvatureCoordinatesInExtChartAt exterior p) x = 0 := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  simpa [connectionCoordinatesInExtChartAt, curvatureCoordinatesInExtChartAt,
    PrincipalConnectionExteriorDerivativeData.IsNaturalInExtChartAt,
    PrincipalConnectionCoordinateExteriorDerivativeNaturalityOn,
    connectionCoordinatePullbackWithin, curvatureCoordinatePullbackWithin,
    PrincipalConnectionExteriorDerivativeData.coordinatePullbackWithin,
    ManifoldDifferentialForm.inExtChartAt] using
    connection.curvatureCoordinatePullbackWithin_coordinateBianchi exterior
      (extChartAt IP p).symm (Set.range ⇑IP) (extChartAt IP p).target x naturality
      connection_regular regularity_order unique_target mem_closure_interior mem_target

/-- For a finite-dimensional principal total-space model, intrinsic smoothness of the exact
connection derives the chart regularity required by the conditional Bianchi theorem. Mathlib's
extended-chart theorems also derive unique differentiability and closure-of-interior membership, so
only exterior naturality and actual target membership remain supplied. -/
theorem curvatureCoordinatesInExtChartAt_coordinateBianchi_of_finiteDimensional
    [FiniteDimensional ℝ EP]
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (p : P) (x : EP)
    (naturality : exterior.IsNaturalInExtChartAt p)
    (mem_target : x ∈ (extChartAt IP p).target) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin (I := IG) (G := G)
      (connection.connectionCoordinatesInExtChartAt p) (extChartAt IP p).target
      (connection.curvatureCoordinatesInExtChartAt exterior p) x = 0 := by
  exact connection.curvatureCoordinatesInExtChartAt_coordinateBianchi exterior p x
    (r := 2) naturality
    ((connection.connectionCoordinatesInExtChartAt_contDiffWithinAt p x mem_target).of_le
      (show (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) from WithTop.coe_le_coe.mpr le_top))
    (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)
    (uniqueDiffOn_extChartAt_target p)
    (extChartAt_target_subset_closure_interior mem_target) mem_target

end PrincipalConnectionData

end

end YangMills.Geometry
