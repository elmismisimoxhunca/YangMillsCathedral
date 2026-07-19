/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCurvatureCoordinateBianchiBridge

/-! Hostile probes for the conditional exact-principal-curvature coordinate Bianchi bridge. -/

namespace YangMills.Geometry.PrincipalCurvatureCoordinateBianchiBridge.Probes

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

omit [FiniteDimensional ℝ EG] in
/-- Naturality retains distinct tangent-transport and exterior-calculus sets. -/
theorem exact_naturality_shape
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (map : EP → P) (transportSource calculusSet : Set EP) :
    PrincipalConnectionCoordinateExteriorDerivativeNaturalityOn
        connection exterior map transportSource calculusSet ↔
      Set.EqOn (exterior.coordinatePullbackWithin map transportSource)
        (extDerivWithin
          (connection.connectionCoordinatePullbackWithin map transportSource) calculusSet)
        calculusSet :=
  Iff.rfl

omit [FiniteDimensional ℝ EG] in
/-- Chart naturality fixes the transport source to `range IP` and calculus to the chart target. -/
theorem exact_chart_naturality_shape
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection) (p : P) :
    exterior.IsNaturalInExtChartAt p ↔
      PrincipalConnectionCoordinateExteriorDerivativeNaturalityOn connection exterior
        (extChartAt IP p).symm (Set.range ⇑IP) (extChartAt IP p).target :=
  Iff.rfl

omit [FiniteDimensional ℝ EG] in
/-- A mismatched derivative value contradicts exact same-connection naturality. -/
theorem mismatched_derivative_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (map : EP → P) (transportSource calculusSet : Set EP) (x : EP)
    (mem_calculus : x ∈ calculusSet)
    (different : exterior.coordinatePullbackWithin map transportSource x ≠
      extDerivWithin (connection.connectionCoordinatePullbackWithin map transportSource)
        calculusSet x)
    (naturality : PrincipalConnectionCoordinateExteriorDerivativeNaturalityOn
      connection exterior map transportSource calculusSet) : False :=
  different (naturality mem_calculus)

/-- Naturality identifies the exact derived curvature with direct coordinate curvature on-set. -/
theorem exact_curvature_identification
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
      calculusSet :=
  connection.curvatureCoordinatePullbackWithin_eqOn_coordinateCurvature exterior map
    transportSource calculusSet naturality

/-- The exact derived curvature receives Bianchi only by the proved coordinate theorem. -/
theorem exact_conditional_bianchi
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (map : EP → P) (transportSource calculusSet : Set EP) (x : EP) {r : ℕ∞}
    (naturality : PrincipalConnectionCoordinateExteriorDerivativeNaturalityOn
      connection exterior map transportSource calculusSet)
    (regular : ContDiffWithinAt ℝ r
      (connection.connectionCoordinatePullbackWithin map transportSource) calculusSet x)
    (order : minSmoothness ℝ 2 ≤ r) (unique : UniqueDiffOn ℝ calculusSet)
    (mem_closure : x ∈ closure (interior calculusSet)) (mem : x ∈ calculusSet) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin (I := IG) (G := G)
      (connection.connectionCoordinatePullbackWithin map transportSource) calculusSet
      (connection.curvatureCoordinatePullbackWithin exterior map transportSource) x = 0 :=
  connection.curvatureCoordinatePullbackWithin_coordinateBianchi exterior map transportSource
    calculusSet x naturality regular order unique mem_closure mem

/-- A claimed nonzero exact-curvature covariant expression is contradictory. -/
theorem nonzero_conditional_bianchi_blocked
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (map : EP → P) (transportSource calculusSet : Set EP) (x : EP) {r : ℕ∞}
    (naturality : PrincipalConnectionCoordinateExteriorDerivativeNaturalityOn
      connection exterior map transportSource calculusSet)
    (regular : ContDiffWithinAt ℝ r
      (connection.connectionCoordinatePullbackWithin map transportSource) calculusSet x)
    (order : minSmoothness ℝ 2 ≤ r) (unique : UniqueDiffOn ℝ calculusSet)
    (mem_closure : x ∈ closure (interior calculusSet)) (mem : x ∈ calculusSet)
    (nonzero :
      letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
      letI : ENat.LEInfty (minSmoothness ℝ 3) := by
        rw [minSmoothness_of_isRCLikeNormedField]
        infer_instance
      groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin (I := IG) (G := G)
        (connection.connectionCoordinatePullbackWithin map transportSource) calculusSet
        (connection.curvatureCoordinatePullbackWithin exterior map transportSource) x ≠ 0) : False :=
  nonzero (connection.curvatureCoordinatePullbackWithin_coordinateBianchi exterior map
    transportSource calculusSet x naturality regular order unique mem_closure mem)

/-- The chart theorem retains the actual chart target in every local hypothesis and conclusion. -/
theorem exact_chart_conditional_bianchi
    (connection : PrincipalConnectionData smoothBundle)
    (exterior : PrincipalConnectionExteriorDerivativeData connection)
    (p : P) (x : EP) {r : ℕ∞}
    (naturality : exterior.IsNaturalInExtChartAt p)
    (regular : ContDiffWithinAt ℝ r
      (connection.connectionCoordinatesInExtChartAt p) (extChartAt IP p).target x)
    (order : minSmoothness ℝ 2 ≤ r)
    (unique : UniqueDiffOn ℝ (extChartAt IP p).target)
    (mem_closure : x ∈ closure (interior (extChartAt IP p).target))
    (mem : x ∈ (extChartAt IP p).target) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    groupLieAlgebraCoordinateCovariantExteriorDerivativeTwoWithin (I := IG) (G := G)
      (connection.connectionCoordinatesInExtChartAt p) (extChartAt IP p).target
      (connection.curvatureCoordinatesInExtChartAt exterior p) x = 0 :=
  connection.curvatureCoordinatesInExtChartAt_coordinateBianchi exterior p x naturality
    regular order unique mem_closure mem

end

end YangMills.Geometry.PrincipalCurvatureCoordinateBianchiBridge.Probes
