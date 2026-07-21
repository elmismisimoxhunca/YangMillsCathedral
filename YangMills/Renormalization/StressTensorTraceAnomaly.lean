/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.StressEnergyTrace
import YangMills.Observables.CurvatureSquaredInterpretation
import YangMills.Renormalization.StressTensorTraceAnomalyNormalization

/-!
# Physical reduced pure Yang–Mills trace anomaly

Collins–Duncan–Joglekar 1977, §III, equations (3.19)–(3.21), retain a complete
renormalized mixing family at arbitrary momentum and reduce to the beta-function `F²` term only for
physical external wave functions, on shell, at nonzero momentum (and in massless pure Yang–Mills).
This module therefore imposes no unrestricted operator equality. A nonempty selected physical,
on-shell, nonzero-momentum weak-matrix-element sector exposes those qualifications explicitly and
detects the exact already interpreted `F²` operator. The normalization is a separate supplied
source-to-project bridge. No theory, observable, or mass gap is constructed.
-/

namespace YangMills.Renormalization

open scoped Manifold ContDiff

noncomputable section

universe uE uG uEB uHB uEP uHP uB uP uH

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {B : Type uB} {P : Type uP}
    [TopologicalSpace B] [TopologicalSpace P]
    {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : Geometry.PrincipalBundleTorsorData G B P}
    {bundle : Geometry.TopologicalPrincipalBundleData torsor}
    {smoothBundle : Geometry.SmoothPrincipalBundleData
      IB (modelWithCornersSelf ℝ E) IP torsor bundle}
    [FiniteDimensional ℝ EB]
    {liftGroup : Type*} [Group liftGroup] [TopologicalSpace liftGroup]
    [IsTopologicalGroup liftGroup]
    {lift : Minkowski.ProperOrthochronousPoincareLiftData EuclideanDimension.four liftGroup}
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : Minkowski.StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : Minkowski.PoincareInvariantVacuumData U}
    {D : Minkowski.CommonInvariantDomainData vacuumData}
    {family : Minkowski.TemperedLocalObservableFamilyData D}
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    {geometry : Classical.EuclideanMetricData (IB := IB) (B := B)}
    {innerData : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {certificate : Geometry.PrincipalCurvatureStructureCertificate
      smoothBundle connection exterior}
    {interpretation : Observables.CurvatureSquaredLocalObservableInterpretationData
      geometry innerData connection exterior certificate family}
    {stress : Minkowski.LocalStressEnergyTensorData family}
    {freedom : PureYangMillsAsymptoticFreedomData
      EuclideanDimension.four gaugeGroup}
    {normalizedBeta : GroupNormalizedOneLoopBetaData innerData freedom}
    {classicalCoupling : ℝ}
    {reference : ClassicalRunningCouplingReferenceData
      freedom classicalCoupling}
    {normalization : StressTensorTraceAnomalyNormalizationData
      normalizedBeta reference}

/-- Explicit selection of physical reduced matrix elements. Admissibility is definitionally
controlled by three exposed physical predicates, and a selected nonzero exact F-squared matrix
element prevents an empty or vacuous selection. -/
structure PhysicalReducedTraceMatrixElementSelectionData
    (interpretation : Observables.CurvatureSquaredLocalObservableInterpretationData
      geometry innerData connection exterior certificate family) where
  /-- Physical bra vectors in the exact common domain. -/
  physicalBra : D.domain → Prop
  /-- On-shell physical bra vectors in the exact common domain. -/
  onShellBra : D.domain → Prop
  /-- Physical ket vectors in the exact common domain. -/
  physicalKet : D.domain → Prop
  /-- On-shell physical ket vectors in the exact common domain. -/
  onShellKet : D.domain → Prop
  /-- Tests representing a nonzero-momentum insertion in this supplied physical selection. -/
  nonzeroMomentumInsertion :
    Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four → Prop
  /-- Selected triples on which the source reduced-matrix-element identity is imposed. -/
  admissible : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four →
    D.domain → D.domain → Prop
  /-- Admissibility has no hidden branch: it is exactly the conjunction of the exposed physical
  bra, ket, and nonzero-momentum-insertion predicates. -/
  admissible_iff : ∀ f psi phi,
    admissible f psi phi ↔
      physicalBra psi ∧ onShellBra psi ∧ physicalKet phi ∧ onShellKet phi ∧
        nonzeroMomentumInsertion f
  /-- One selected physical test. -/
  selectedTest : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four
  /-- One selected physical bra. -/
  selectedBra : D.domain
  /-- One selected physical ket. -/
  selectedKet : D.domain
  /-- The selected triple is genuinely admissible. -/
  selected_admissible : admissible selectedTest selectedBra selectedKet
  /-- The selected triple detects the exact existing interpreted F-squared operator. -/
  selected_curvatureSquared_matrixElement_ne_zero :
    @inner ℂ H _ selectedBra.val
      (family.operator
        (interpretation.quantumLabel Observables.BasicCurvatureObservableTag.curvatureSquared)
        selectedTest selectedKet).val ≠ 0

namespace PhysicalReducedTraceMatrixElementSelectionData

omit [T2Space G] [SecondCountableTopology G] [FiniteDimensional ℝ EB] in
/-- Every supplied selection contains an admissible triple. -/
theorem exists_admissible
    (selection : PhysicalReducedTraceMatrixElementSelectionData interpretation) :
    ∃ f psi phi, selection.admissible f psi phi :=
  ⟨selection.selectedTest, selection.selectedBra, selection.selectedKet,
    selection.selected_admissible⟩

omit [T2Space G] [SecondCountableTopology G] [FiniteDimensional ℝ EB] in
/-- The selected triple satisfies each exposed physical conjunct. -/
theorem selected_physical_conjunction
    (selection : PhysicalReducedTraceMatrixElementSelectionData interpretation) :
    selection.physicalBra selection.selectedBra ∧
      selection.onShellBra selection.selectedBra ∧
      selection.physicalKet selection.selectedKet ∧
      selection.onShellKet selection.selectedKet ∧
      selection.nonzeroMomentumInsertion selection.selectedTest :=
  (selection.admissible_iff _ _ _).mp selection.selected_admissible

end PhysicalReducedTraceMatrixElementSelectionData

/-- Supplied physical reduced-matrix-element trace anomaly on the exact four-dimensional
stress/F-squared/group-normalized-beta/reference chain. This is acceptance data only. -/
structure StressTensorTraceAnomalyData
    (interpretation : Observables.CurvatureSquaredLocalObservableInterpretationData
      geometry innerData connection exterior certificate family)
    (stress : Minkowski.LocalStressEnergyTensorData family)
    (normalization : StressTensorTraceAnomalyNormalizationData
      normalizedBeta reference)
    (selection : PhysicalReducedTraceMatrixElementSelectionData interpretation) where
  /-- Exact identity only for admissible physical reduced matrix elements. The right side uses the
  already interpreted F-squared label, never a replacement label. -/
  admissible_weak_matrixElement_trace_anomaly :
    ∀ (f : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four)
      (psi phi : D.domain), selection.admissible f psi phi →
      @inner ℂ H _ psi.val (Minkowski.stressTensorTraceOperator stress f phi).val =
        (normalization.coefficient : ℂ) *
          @inner ℂ H _ psi.val
            (family.operator
              (interpretation.quantumLabel Observables.BasicCurvatureObservableTag.curvatureSquared)
              f phi).val

namespace StressTensorTraceAnomalyData

omit [FiniteDimensional ℝ EB] in
/-- The selected nonzero exact F-squared reduced matrix element forces a nonzero direct trace
action on that same selected physical test and ket. -/
theorem selected_traceOperator_ne_zero
    {selection : PhysicalReducedTraceMatrixElementSelectionData interpretation}
    (data : StressTensorTraceAnomalyData interpretation stress normalization selection) :
    Minkowski.stressTensorTraceOperator stress selection.selectedTest selection.selectedKet ≠ 0 := by
  intro traceZero
  have identity := data.admissible_weak_matrixElement_trace_anomaly
    selection.selectedTest selection.selectedBra selection.selectedKet
    selection.selected_admissible
  rw [traceZero] at identity
  simp only [Submodule.coe_zero, inner_zero_right] at identity
  exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr normalization.coefficient_ne_zero)
    selection.selected_curvatureSquared_matrixElement_ne_zero) identity.symm

omit [FiniteDimensional ℝ EB] in
/-- In particular, the direct trace operator cannot collapse on all tests and common-domain
vectors. -/
theorem traceOperator_nontrivial
    {selection : PhysicalReducedTraceMatrixElementSelectionData interpretation}
    (data : StressTensorTraceAnomalyData interpretation stress normalization selection) :
    ∃ (f : Minkowski.ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four) (phi : D.domain),
      Minkowski.stressTensorTraceOperator stress f phi ≠ 0 :=
  ⟨selection.selectedTest, selection.selectedKet, data.selected_traceOperator_ne_zero⟩

end StressTensorTraceAnomalyData


end

end YangMills.Renormalization
