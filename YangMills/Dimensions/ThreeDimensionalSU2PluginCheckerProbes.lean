/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.ThreeDimensionalSU2PluginChecker

/-! Hostile and reporting probes for the bounded three-dimensional SU(2) plug-in surface. -/

namespace YangMills.Dimensions.ThreeDimensionalSU2PluginChecker.Probes

open scoped Manifold ContDiff

noncomputable section

universe uEG uEP uHP uGauge uP uLift uH uLabel

variable
    {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    [FiniteDimensional ℝ EG]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {GaugeGroup : Type uGauge} [Group GaugeGroup] [TopologicalSpace GaugeGroup]
    [T2Space GaugeGroup] [SecondCountableTopology GaugeGroup]
    [IsTopologicalGroup GaugeGroup] [ChartedSpace EG GaugeGroup]
    [LieGroup (modelWithCornersSelf ℝ EG) ∞ GaugeGroup]
    {P : Type uP} [TopologicalSpace P]
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : Geometry.PrincipalBundleTorsorData GaugeGroup
      ThreeDimensionalEuclideanBase P}
    {bundle : Geometry.TopologicalPrincipalBundleData torsor}
    {smoothBundle : Geometry.SmoothPrincipalBundleData threeDimensionalEuclideanModel
      (modelWithCornersSelf ℝ EG) IP torsor bundle}
    {PoincareLiftGroup : Type uLift} [Group PoincareLiftGroup]
    [TopologicalSpace PoincareLiftGroup] [IsTopologicalGroup PoincareLiftGroup]
    {lift : Minkowski.ProperOrthochronousPoincareLiftData
      EuclideanDimension.three PoincareLiftGroup}
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : Minkowski.StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : Minkowski.PoincareInvariantVacuumData U}
    {D : Minkowski.CommonInvariantDomainData vacuumData}
    {fieldData : Minkowski.ScalarWightmanFieldOnCommonDomainData D}
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ EG) (G := GaugeGroup)}
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {curvatureCertificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}

/-- A successful report cannot be produced without strongest-tier data. -/
def pass_requires_all_witnesses
    (data : ThreeDimensionalSU2ExistenceMassGapAcceptanceData
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate)) :
    ThreeDimensionalSU2PluginReport
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate) :=
  .pass data

/-- A pass report projects to the exact authoritative proposition. -/
theorem pass_projects_acceptance
    (data : ThreeDimensionalSU2ExistenceMassGapAcceptanceData
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate)) :
    (ThreeDimensionalSU2PluginReport.pass data).acceptanceData? = some data :=
  rfl

/-- Missing continuum existence is reported as incomplete, never as a pass. -/
def latticeOnly_is_incomplete :
    ThreeDimensionalSU2PluginReport
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate) :=
  .incomplete [.continuumWightmanExistence] (by simp)

/-- Disconnected Euclidean/Minkowski data is reported at the explicit same-theory obligation. -/
def disconnectedTheories_are_incomplete :
    ThreeDimensionalSU2PluginReport
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate) :=
  .incomplete [.euclideanMinkowskiSameTheory] (by simp)

/-- An empty or unrelated excitation sector cannot be promoted to pass. -/
def vacuousGap_is_incomplete :
    ThreeDimensionalSU2PluginReport
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate) :=
  .incomplete [.sameJointPVMMassGap, .nonvacuumSpectralSector] (by simp)

/-- A two-dimensional candidate has the exact dimension-mismatch outcome. -/
def twoDimensional_is_mismatch :
    ThreeDimensionalSU2PluginReport
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate) :=
  .dimensionMismatch EuclideanDimension.two (by
    intro equality
    have valueEquality := congrArg EuclideanDimension.value equality
    simp at valueEquality)

/-- A four-dimensional candidate has the exact dimension-mismatch outcome. -/
def fourDimensional_is_mismatch :
    ThreeDimensionalSU2PluginReport
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate) :=
  .dimensionMismatch EuclideanDimension.four (by
    intro equality
    have valueEquality := congrArg EuclideanDimension.value equality
    simp at valueEquality)

example :
    (latticeOnly_is_incomplete
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate)).status =
      "INCOMPLETE" := rfl

example :
    (disconnectedTheories_are_incomplete
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate)).status =
      "INCOMPLETE" := rfl

example :
    (vacuousGap_is_incomplete
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate)).status =
      "INCOMPLETE" := rfl

example :
    (twoDimensional_is_mismatch
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate)).status =
      "DIMENSION MISMATCH" := rfl

example :
    (fourDimensional_is_mismatch
      (fieldData := fieldData) (inner := inner) (connection := connection)
      (exterior := exterior) (curvatureCertificate := curvatureCertificate)).status =
      "DIMENSION MISMATCH" := rfl

end

end YangMills.Dimensions.ThreeDimensionalSU2PluginChecker.Probes
