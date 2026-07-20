/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Observables.CurvaturePowerGaugeTransport

/-!
# Hostile probes for gauge transport of interpreted curvature powers
-/

namespace YangMills.Observables.CurvaturePowerGaugeTransport.Probes

open Bundle
open scoped Bundle ContDiff Manifold Topology

universe uEG uHG uEB uHB uEP uHP uG uB uP uH

noncomputable section

variable
    {d : EuclideanDimension}
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : Geometry.PrincipalBundleTorsorData G B P}
    {bundle : Geometry.TopologicalPrincipalBundleData torsor}
    {smoothBundle : Geometry.SmoothPrincipalBundleData IB IG IP torsor bundle}
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [CompleteSpace EP]
    {liftGroup : Type*} [Group liftGroup] [TopologicalSpace liftGroup]
    [IsTopologicalGroup liftGroup]
    {lift : Minkowski.ProperOrthochronousPoincareLiftData d liftGroup}
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : Minkowski.StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : Minkowski.PoincareInvariantVacuumData U}
    {D : Minkowski.CommonInvariantDomainData vacuumData}
    {family : Minkowski.TemperedLocalObservableFamilyData D}

variable
    (geometry : Classical.EuclideanMetricData (IB := IB) (B := B))
    (inner : Geometry.InvariantInnerProductData (I := IG) (G := G))
    (gauge : Geometry.SmoothGaugeTransformation smoothBundle)
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior)

/-- Both basic classical tags retain their exact functions. -/
theorem exact_basic_classical_transport :
    basicClassicalCurvatureObservable geometry inner
        (Geometry.gaugePullbackConnection gauge connection)
        (Geometry.gaugePullbackConnectionExteriorDerivative gauge connection exterior)
        (Geometry.gaugePullbackCurvatureStructureCertificate
          gauge connection exterior certificate) =
      basicClassicalCurvatureObservable geometry inner connection exterior certificate :=
  basicClassicalCurvatureObservable_gaugePullback
    geometry inner gauge connection exterior certificate

/-- All three finite scalar tags retain their exact classical functions. -/
theorem exact_finite_classical_transport :
    classicalScalarCurvaturePowerObservable geometry inner
        (Geometry.gaugePullbackConnection gauge connection)
        (Geometry.gaugePullbackConnectionExteriorDerivative gauge connection exterior)
        (Geometry.gaugePullbackCurvatureStructureCertificate
          gauge connection exterior certificate) =
      classicalScalarCurvaturePowerObservable geometry inner connection exterior certificate :=
  classicalScalarCurvaturePowerObservable_gaugePullback
    geometry inner gauge connection exterior certificate

variable
    (basic : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family)
    (powers : ScalarCurvaturePowerLocalObservableInterpretationData
      geometry inner connection exterior certificate family basic)

omit [FiniteDimensional ℝ EB] in
/-- Basic transport keeps every quantum label unchanged. -/
theorem exact_basic_quantumLabel (tag : BasicCurvatureObservableTag) :
    (basic.gaugePullback gauge).quantumLabel tag = basic.quantumLabel tag :=
  basic.gaugePullback_quantumLabel gauge tag

/-- Finite-power transport keeps the exposed exact classical carrier unchanged. -/
theorem exact_power_classicalObservable (tag : ScalarCurvaturePowerTag) :
    (powers.gaugePullback gauge).classicalObservable tag = powers.classicalObservable tag :=
  powers.gaugePullback_classicalObservable gauge tag

/-- Finite-power transport keeps every quantum label unchanged. -/
theorem exact_power_quantumLabel (tag : ScalarCurvaturePowerTag) :
    (powers.gaugePullback gauge).quantumLabel tag = powers.quantumLabel tag :=
  powers.gaugePullback_quantumLabel gauge tag

/-- Quartic anti-collapse transports to the exact pulled interpretation. -/
theorem exact_antiCollapse_transport
    (antiCollapse : CurvatureQuarticAntiCollapseData powers) :
    CurvatureQuarticAntiCollapseData (powers.gaugePullback gauge) :=
  antiCollapse.gaugePullback gauge

/-- A changed basic classical carrier contradicts exact gauge transport. -/
theorem changed_basic_classical_blocked
    (wrong :
      basicClassicalCurvatureObservable geometry inner
          (Geometry.gaugePullbackConnection gauge connection)
          (Geometry.gaugePullbackConnectionExteriorDerivative gauge connection exterior)
          (Geometry.gaugePullbackCurvatureStructureCertificate
            gauge connection exterior certificate) ≠
        basicClassicalCurvatureObservable geometry inner connection exterior certificate) : False :=
  wrong (basicClassicalCurvatureObservable_gaugePullback
    geometry inner gauge connection exterior certificate)

/-- A changed finite classical carrier contradicts exact gauge transport. -/
theorem changed_finite_classical_blocked
    (wrong :
      classicalScalarCurvaturePowerObservable geometry inner
          (Geometry.gaugePullbackConnection gauge connection)
          (Geometry.gaugePullbackConnectionExteriorDerivative gauge connection exterior)
          (Geometry.gaugePullbackCurvatureStructureCertificate
            gauge connection exterior certificate) ≠
        classicalScalarCurvaturePowerObservable
          geometry inner connection exterior certificate) : False :=
  wrong (classicalScalarCurvaturePowerObservable_gaugePullback
    geometry inner gauge connection exterior certificate)

/-- The canonical transport cannot secretly replace a finite-fragment quantum label. -/
theorem changed_power_quantumLabel_blocked
    (tag : ScalarCurvaturePowerTag)
    (wrong : (powers.gaugePullback gauge).quantumLabel tag ≠ powers.quantumLabel tag) : False :=
  wrong (powers.gaugePullback_quantumLabel gauge tag)

end

end YangMills.Observables.CurvaturePowerGaugeTransport.Probes
