/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Observables.CurvatureSquaredOPECoherence

/-! Hostile probes for exact interpreted-`F²` participation in one weak OPE. -/

namespace YangMills.Observables.CurvatureSquaredOPECoherence.Probes

open scoped Bundle ContDiff Manifold Topology

universe uEG uHG uEB uHB uEP uHP uGauge uB uP uLift uH

noncomputable section

variable
    {d : EuclideanDimension}
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {GaugeGroup : Type uGauge} {B : Type uB} {P : Type uP}
    [Group GaugeGroup] [TopologicalSpace GaugeGroup]
    [TopologicalSpace B] [TopologicalSpace P] [IsTopologicalGroup GaugeGroup]
    {IG : ModelWithCorners ℝ EG HG} {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG GaugeGroup] [LieGroup IG ∞ GaugeGroup]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : Geometry.PrincipalBundleTorsorData GaugeGroup B P}
    {bundle : Geometry.TopologicalPrincipalBundleData torsor}
    {smoothBundle : Geometry.SmoothPrincipalBundleData IB IG IP torsor bundle}
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB]
    {PoincareLiftGroup : Type uLift}
    [Group PoincareLiftGroup] [TopologicalSpace PoincareLiftGroup]
    [IsTopologicalGroup PoincareLiftGroup]
    {lift : Minkowski.ProperOrthochronousPoincareLiftData d PoincareLiftGroup}
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : Minkowski.StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : Minkowski.PoincareInvariantVacuumData U}
    {D : Minkowski.CommonInvariantDomainData vacuumData}
    {family : Minkowski.TemperedLocalObservableFamilyData D}
    [DecidableEq family.Label]
    {products : Minkowski.WeakTemperedBilocalObservableProductData family}
    {geometry : Classical.EuclideanMetricData (IB := IB) (B := B)}
    {inner : Geometry.InvariantInnerProductData (I := IG) (G := GaugeGroup)}
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {curvatureCertificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}
    {interpretation : CurvatureSquaredLocalObservableInterpretationData geometry inner connection
      exterior curvatureCertificate family}
    {ope : Minkowski.WeakOperatorProductExpansionData products}
    (coherence : CurvatureSquaredOPECoherenceData geometry inner connection exterior
      curvatureCertificate interpretation ope)

omit [FiniteDimensional ℝ EB] in
/-- The exact ordered inputs are both the interpreted curvature-squared label. -/
theorem exact_curvature_squared_inputs :
    ope.coefficient
      (interpretation.quantumLabel BasicCurvatureObservableTag.curvatureSquared)
      (interpretation.quantumLabel BasicCurvatureObservableTag.curvatureSquared)
      coherence.outputLabel ≠ 0 :=
  coherence.coefficient_nonzero

omit [FiniteDimensional ℝ EB] in
/-- The selected output occurs already at zeroth order and hence at every later order. -/
theorem exact_output_all_orders (order : ℕ) :
    coherence.outputLabel ∈ ope.truncation 0 ∧
      coherence.outputLabel ∈ ope.truncation order :=
  ⟨coherence.output_mem_zero, coherence.output_mem_truncation order⟩

omit [FiniteDimensional ℝ EB] in
/-- The selected exact coefficient/local-field contraction is genuinely nonzero. -/
theorem exact_nonzero_contracted_term :
    ope.contraction.contract
      (ope.coefficient
        (interpretation.quantumLabel BasicCurvatureObservableTag.curvatureSquared)
        (interpretation.quantumLabel BasicCurvatureObservableTag.curvatureSquared)
        coherence.outputLabel)
      (family.matrixElement coherence.outputLabel coherence.bra coherence.ket) ≠ 0 :=
  coherence.contractedTerm_nonzero

omit [FiniteDimensional ℝ EB] in
/-- A zero coefficient cannot masquerade as interpreted `F² × F²` participation. -/
theorem zero_curvature_squared_coefficient_blocked
    (claimed : ope.coefficient
      (interpretation.quantumLabel BasicCurvatureObservableTag.curvatureSquared)
      (interpretation.quantumLabel BasicCurvatureObservableTag.curvatureSquared)
      coherence.outputLabel = 0) : False :=
  coherence.coefficient_nonzero claimed

omit [FiniteDimensional ℝ EB] in
/-- A zero selected output matrix element cannot satisfy the bridge. -/
theorem zero_output_matrixElement_blocked
    (claimed : family.matrixElement coherence.outputLabel coherence.bra coherence.ket = 0) : False :=
  coherence.output_matrixElement_nonzero claimed

omit [FiniteDimensional ℝ EB] [DecidableEq family.Label] in
/-- Replacing either exact input by a known different label is rejected at the label level. -/
theorem unrelated_input_label_blocked
    (wrong : family.Label)
    (different : wrong ≠
      interpretation.quantumLabel BasicCurvatureObservableTag.curvatureSquared)
    (claimed : wrong =
      interpretation.quantumLabel BasicCurvatureObservableTag.curvatureSquared) : False :=
  different claimed

end

end YangMills.Observables.CurvatureSquaredOPECoherence.Probes
