/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Renormalization.AdjointCasimirNormalization

/-!
# Hostile probes for adjoint-Casimir beta normalization

These probes lock the exact gauge Lie algebra, selected invariant pairing, orthonormal basis,
structure-constant identity, positive Casimir, and running-coupling coefficient into one chain. No
basis, Casimir identity, perturbative calculation, or running coupling is constructed.
-/

namespace YangMills.Renormalization.AdjointCasimirNormalization.Probes

open YangMills
open scoped Manifold ContDiff BigOperators

universe uE uG

noncomputable section

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
    [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}

/-- The chosen basis is orthonormal for the exact selected invariant pairing. -/
example (data : AdjointCasimirNormalizationData inner) (a d : Fin data.rank) :
    inner.pairing (data.basis a) (data.basis d) = if a = d then 1 else 0 :=
  data.basis_orthonormal a d

/-- The displayed Gross–Wilczek double contraction uses the bracket of that same exact Lie algebra. -/
example (data : AdjointCasimirNormalizationData inner) (a d : Fin data.rank) :
    (∑ b : Fin data.rank, ∑ c : Fin data.rank,
      compactGaugeStructureCoefficient inner data.basis a b c *
        compactGaugeStructureCoefficient inner data.basis d b c) =
      data.adjointCasimir * (if a = d then 1 else 0) :=
  data.casimir_identity a d

/-- A zero-bracket or zero-structure-coefficient surrogate is rejected. -/
example (data : AdjointCasimirNormalizationData inner) :
    ∃ a b c : Fin data.rank,
      compactGaugeStructureCoefficient inner data.basis a b c ≠ 0 :=
  data.exists_structureCoefficient_ne_zero

/-- The Casimir itself is strictly positive, independently of beta-function positivity. -/
example (data : AdjointCasimirNormalizationData inner) : 0 < data.adjointCasimir :=
  data.adjointCasimir_pos

/-- The preliminary coefficient is exactly the group- and pairing-normalized one-loop value. -/
example
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    {freedom : PureYangMillsAsymptoticFreedomData EuclideanDimension.four gaugeGroup}
    (data : GroupNormalizedOneLoopBetaData inner freedom) :
    freedom.leadingCoefficient =
      (11 * data.casimirNormalization.adjointCasimir) / (3 * (16 * Real.pi ^ 2)) :=
  data.leadingCoefficient_eq

/-- The classical scalar is connected to the same running coupling on an explicit UV scale. -/
example
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    {freedom : PureYangMillsAsymptoticFreedomData EuclideanDimension.four gaugeGroup}
    {classicalCoupling : ℝ}
    (data : ClassicalRunningCouplingReferenceData freedom classicalCoupling) :
    freedom.ultravioletThreshold < data.referenceLogScale ∧
      classicalCoupling = freedom.runningCoupling data.referenceLogScale :=
  ⟨data.reference_mem_ultraviolet, data.coupling_eq_runningCoupling⟩

/-- An independently substituted classical coupling is rejected at the same reference scale. -/
example
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    {freedom : PureYangMillsAsymptoticFreedomData EuclideanDimension.four gaugeGroup}
    {classicalCoupling replacement : ℝ}
    (data : ClassicalRunningCouplingReferenceData freedom classicalCoupling)
    (replacement_eq_running :
      replacement = freedom.runningCoupling data.referenceLogScale) :
    replacement = classicalCoupling :=
  data.replacement_eq replacement_eq_running

/-- Denominator clearing reaches the same exact Casimir, blocking an unrelated positive constant. -/
example
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    {freedom : PureYangMillsAsymptoticFreedomData EuclideanDimension.four gaugeGroup}
    (data : GroupNormalizedOneLoopBetaData inner freedom) :
    freedom.leadingCoefficient * (3 * (16 * Real.pi ^ 2)) =
      11 * data.casimirNormalization.adjointCasimir :=
  data.leadingCoefficient_mul_denominator

end

end YangMills.Renormalization.AdjointCasimirNormalization.Probes
