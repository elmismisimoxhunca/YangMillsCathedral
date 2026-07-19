/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WeakOperatorProductExpansion
import YangMills.Observables.CurvatureSquaredInterpretation

/-!
# Coherence between interpreted curvature squared and a weak OPE

Putting an interpreted `F²` label and a weak OPE in one observable family does not by itself ensure
that the OPE ever uses that label. This module requires the ordered `F² × F²` product to have an
actual zeroth-order output term with nonzero coefficient and nonzero local matrix element. The exact
OPE contraction then makes that term nonzero.

This is an anti-disconnection bridge. It supplies no perturbative coefficient, scaling degree,
operator mixing law, remainder estimate, observable family, theory, or mass gap.
-/

namespace YangMills.Observables

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
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
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

/-- Exact nonzero zeroth-order participation of the interpreted curvature-squared label in one weak
OPE on the same observable family. -/
structure CurvatureSquaredOPECoherenceData
    (geometry : Classical.EuclideanMetricData (IB := IB) (B := B))
    (inner : Geometry.InvariantInnerProductData (I := IG) (G := GaugeGroup))
    (connection : Geometry.PrincipalConnectionData smoothBundle)
    (exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection)
    (curvatureCertificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior)
    (interpretation : CurvatureSquaredLocalObservableInterpretationData geometry inner connection
      exterior curvatureCertificate family)
    (ope : Minkowski.WeakOperatorProductExpansionData products) where
  /-- One exact output label in the `F² × F²` expansion. -/
  outputLabel : family.Label
  /-- The selected output is already present at zeroth truncation order. -/
  output_mem_zero : outputLabel ∈ ope.truncation 0
  /-- Its exact relative coefficient distribution is nonzero. -/
  coefficient_nonzero :
    ope.coefficient
      (interpretation.quantumLabel BasicCurvatureObservableTag.curvatureSquared)
      (interpretation.quantumLabel BasicCurvatureObservableTag.curvatureSquared)
      outputLabel ≠ 0
  /-- One exact matrix element makes the selected output local distribution nonzero. -/
  bra : D.domain
  ket : D.domain
  output_matrixElement_nonzero : family.matrixElement outputLabel bra ket ≠ 0

namespace CurvatureSquaredOPECoherenceData

variable
    {geometry : Classical.EuclideanMetricData (IB := IB) (B := B)}
    {inner : Geometry.InvariantInnerProductData (I := IG) (G := GaugeGroup)}
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {curvatureCertificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}
    {interpretation : CurvatureSquaredLocalObservableInterpretationData geometry inner connection
      exterior curvatureCertificate family}
    {ope : Minkowski.WeakOperatorProductExpansionData products}

omit [FiniteDimensional ℝ EB] in
/-- The selected interpreted `F² × F²` OPE term has nonzero exact contracted distribution. -/
theorem contractedTerm_nonzero
    (coherence : CurvatureSquaredOPECoherenceData geometry inner connection exterior
      curvatureCertificate interpretation ope) :
    ope.contraction.contract
      (ope.coefficient
        (interpretation.quantumLabel BasicCurvatureObservableTag.curvatureSquared)
        (interpretation.quantumLabel BasicCurvatureObservableTag.curvatureSquared)
        coherence.outputLabel)
      (family.matrixElement coherence.outputLabel coherence.bra coherence.ket) ≠ 0 :=
  ope.contraction.contract_ne_zero _ _ coherence.coefficient_nonzero
    coherence.output_matrixElement_nonzero

omit [FiniteDimensional ℝ EB] in
/-- Monotonicity keeps the selected `F² × F²` output in every finite truncation order. -/
theorem output_mem_truncation
    (coherence : CurvatureSquaredOPECoherenceData geometry inner connection exterior
      curvatureCertificate interpretation ope) (order : ℕ) :
    coherence.outputLabel ∈ ope.truncation order :=
  ope.truncation_mono (Nat.zero_le order) coherence.output_mem_zero

end CurvatureSquaredOPECoherenceData

end

end YangMills.Observables
