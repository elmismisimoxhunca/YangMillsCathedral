/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Observables.CurvatureSquaredInterpretation

/-!
# Hostile probes for curvature-squared interpretation

The probes expose the exact classical curvature chain, dimension match, normalized quantum unit,
and nonzero non-unit curvature-squared label. No interpretation datum is constructed.
-/

namespace YangMills.Observables.CurvatureSquaredInterpretation.Probes

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
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB]
    {liftGroup : Type*} [Group liftGroup] [TopologicalSpace liftGroup]
    [IsTopologicalGroup liftGroup]
    {lift : Minkowski.ProperOrthochronousPoincareLiftData d liftGroup}
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : Minkowski.StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : Minkowski.PoincareInvariantVacuumData U}
    {D : Minkowski.CommonInvariantDomainData vacuumData}
    {family : Minkowski.TemperedLocalObservableFamilyData D}
    {geometry : Classical.EuclideanMetricData (IB := IB) (B := B)}
    {inner : Geometry.InvariantInnerProductData (I := IG) (G := G)}
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}

/-- The unit tag has exact constant-one classical meaning. -/
theorem exact_classical_unit :
    basicClassicalCurvatureObservable geometry inner connection exterior certificate .unit =
      (fun _ : B => 1) :=
  rfl

/-- The curvature-squared tag exposes the exact canonical density and cannot be redirected to an
unrelated classical function. -/
theorem exact_classical_curvature_squared :
    basicClassicalCurvatureObservable geometry inner connection exterior certificate
        .curvatureSquared =
      geometry.canonicalCurvatureDensity inner connection exterior certificate :=
  basicClassicalCurvatureObservable_curvatureSquared
    geometry inner connection exterior certificate

omit [FiniteDimensional ℝ EB] in
/-- Classical and quantum spacetime dimensions are explicitly connected at every point. -/
theorem exact_base_dimension
    (interpretation : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family)
    (b : B) :
    Module.finrank ℝ (TangentSpace IB b) = d.value :=
  interpretation.baseDimension_eq b

omit [FiniteDimensional ℝ EB] in
/-- The designated point makes the dimension obligation nonvacuous. -/
theorem exact_designated_base_dimension
    (interpretation : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family) :
    Module.finrank ℝ (TangentSpace IB interpretation.basePoint) = d.value :=
  interpretation.baseDimension_eq interpretation.basePoint

omit [FiniteDimensional ℝ EB] in
/-- The unit tag uses the exact already normalized family unit. -/
theorem exact_quantum_unit
    (interpretation : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family) :
    interpretation.quantumLabel .unit = family.unitLabel :=
  interpretation.quantumLabel_unit

omit [FiniteDimensional ℝ EB] in
/-- The curvature-squared label cannot collapse to the unit label. -/
theorem unit_curvature_squared_identification_blocked
    (interpretation : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family) :
    interpretation.quantumLabel .curvatureSquared ≠ family.unitLabel :=
  interpretation.curvatureSquaredLabel_ne_unit

omit [FiniteDimensional ℝ EB] in
/-- Zero and duplicate-unit operator interpretations are blocked on one exact test/domain vector. -/
theorem zero_or_unit_curvature_squared_operator_blocked
    (interpretation : CurvatureSquaredLocalObservableInterpretationData
      geometry inner connection exterior certificate family) :
    ∃ (f : Minkowski.ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain),
      family.operator (interpretation.quantumLabel .curvatureSquared) f ψ ≠ 0 ∧
      family.operator (interpretation.quantumLabel .curvatureSquared) f ψ ≠
        family.operator family.unitLabel f ψ :=
  interpretation.curvatureSquared_nontrivial

end

end YangMills.Observables.CurvatureSquaredInterpretation.Probes
