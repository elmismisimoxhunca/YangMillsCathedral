/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.InvariantInnerProduct
import YangMills.Geometry.LieGroup
import YangMills.Renormalization.RunningCoupling
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Adjoint-Casimir normalization of the one-loop pure-gauge beta coefficient

Gross–Wilczek printed p. 1344, equation (8), gives
`β(g) = -(g³ / 16π²) (11/3) C₂(G) + O(g⁵)` and immediately fixes its convention by
`∑_{b,c} C_{abc} C_{dbc} = C₂(G) δ_{ad}`.

This module states that normalization on an explicit finite orthonormal basis of the exact tangent
Lie algebra and ties the preliminary running-coupling coefficient to it. The basis, Casimir identity,
and coefficient equality are acceptance data; none is constructed and no perturbative remainder is
claimed.
-/

namespace YangMills.Renormalization

open scoped Manifold ContDiff BigOperators

universe uE uG

noncomputable section

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
    [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

/-- The exact Mathlib tangent Lie bracket, packaged without leaking the local finite-dimensional
completeness and smoothness instances required by `GroupLieAlgebra`. -/
noncomputable def compactGaugeLieBracket
    (X Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    GroupLieAlgebra (modelWithCornersSelf ℝ E) G := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  exact ⁅X, Y⁆

/-- Structure coefficient of the exact tangent bracket in a basis, lowered with the selected
invariant inner product. -/
noncomputable def compactGaugeStructureCoefficient
    (inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G))
    {rank : ℕ}
    (basis : Module.Basis (Fin rank) ℝ (GroupLieAlgebra (modelWithCornersSelf ℝ E) G))
    (a b c : Fin rank) : ℝ :=
  inner.pairing (basis a) (compactGaugeLieBracket (basis b) (basis c))

/-- Exact adjoint quadratic-Casimir convention on one orthonormal basis of the actual gauge Lie
algebra. This is normalization data, not an existence theorem for such a basis. -/
structure AdjointCasimirNormalizationData
    (inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)) where
  /-- Finite basis rank, retained explicitly for source-indexed sums. -/
  rank : ℕ
  /-- Anti-vacuity: the basis index is nonempty. -/
  rank_pos : 0 < rank
  /-- Basis of the exact tangent Lie algebra. -/
  basis : Module.Basis (Fin rank) ℝ (GroupLieAlgebra (modelWithCornersSelf ℝ E) G)
  /-- Orthonormality uses the exact invariant pairing that normalizes the classical action. -/
  basis_orthonormal : ∀ a d,
    inner.pairing (basis a) (basis d) = if a = d then 1 else 0
  /-- Positive adjoint quadratic Casimir in this exact convention. -/
  adjointCasimir : ℝ
  adjointCasimir_pos : 0 < adjointCasimir
  /-- Gross–Wilczek's displayed structure-constant normalization identity. -/
  casimir_identity : ∀ a d,
    (∑ b : Fin rank, ∑ c : Fin rank,
      compactGaugeStructureCoefficient inner basis a b c *
        compactGaugeStructureCoefficient inner basis d b c) =
      adjointCasimir * (if a = d then 1 else 0)

namespace AdjointCasimirNormalizationData

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G] in
/-- Positive Casimir normalization forces at least one actual nonzero bracket structure
coefficient; a zero-bracket surrogate cannot satisfy the certificate. -/
theorem exists_structureCoefficient_ne_zero
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (data : AdjointCasimirNormalizationData inner) :
    ∃ a b c : Fin data.rank,
      compactGaugeStructureCoefficient inner data.basis a b c ≠ 0 := by
  let a : Fin data.rank := ⟨0, data.rank_pos⟩
  by_contra noCoefficient
  push Not at noCoefficient
  have identity := data.casimir_identity a a
  simp only [if_pos] at identity
  simp [noCoefficient] at identity
  exact (ne_of_gt data.adjointCasimir_pos) identity.symm

end AdjointCasimirNormalizationData

/-- Group- and pairing-normalized one-loop coefficient for the exact preliminary running coupling. -/
structure GroupNormalizedOneLoopBetaData
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    (inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G))
    (freedom : PureYangMillsAsymptoticFreedomData EuclideanDimension.four gaugeGroup) where
  /-- Exact basis-level adjoint-Casimir convention. -/
  casimirNormalization : AdjointCasimirNormalizationData inner
  /-- Equation (8), in the project's `β(g) = -b₀g³ + o(g³)` convention. -/
  leadingCoefficient_eq : freedom.leadingCoefficient =
    (11 * casimirNormalization.adjointCasimir) / (3 * (16 * Real.pi ^ 2))

/-- Reference-scale identification of an outer classical-action coupling with the exact running
coupling whose beta function is normalized above. This records the project's convention in which
the coupling is placed outside the curvature-squared action. -/
structure ClassicalRunningCouplingReferenceData
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    (freedom : PureYangMillsAsymptoticFreedomData EuclideanDimension.four gaugeGroup)
    (classicalCoupling : ℝ) where
  /-- Dimensionless logarithmic reference scale `t = log (μ/μ₀)`. -/
  referenceLogScale : ℝ
  /-- The selected reference lies on the exact ultraviolet tail controlled by the flow equation. -/
  reference_mem_ultraviolet : freedom.ultravioletThreshold < referenceLogScale
  /-- The classical outer coupling is the value of the same running coupling at that scale. -/
  coupling_eq_runningCoupling :
    classicalCoupling = freedom.runningCoupling referenceLogScale

namespace ClassicalRunningCouplingReferenceData

/-- A second scalar cannot replace the connected classical coupling while retaining the same
reference datum unless it is equal to the original scalar. -/
theorem replacement_eq
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    {freedom : PureYangMillsAsymptoticFreedomData EuclideanDimension.four gaugeGroup}
    {classicalCoupling replacement : ℝ}
    (data : ClassicalRunningCouplingReferenceData freedom classicalCoupling)
    (replacement_eq_running :
      replacement = freedom.runningCoupling data.referenceLogScale) :
    replacement = classicalCoupling :=
  replacement_eq_running.trans data.coupling_eq_runningCoupling.symm

end ClassicalRunningCouplingReferenceData

namespace GroupNormalizedOneLoopBetaData

/-- The normalized coefficient remains tied to the exact positive adjoint Casimir. -/
theorem leadingCoefficient_mul_denominator
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {freedom : PureYangMillsAsymptoticFreedomData EuclideanDimension.four gaugeGroup}
    (data : GroupNormalizedOneLoopBetaData inner freedom) :
    freedom.leadingCoefficient * (3 * (16 * Real.pi ^ 2)) =
      11 * data.casimirNormalization.adjointCasimir := by
  rw [data.leadingCoefficient_eq]
  field_simp

end GroupNormalizedOneLoopBetaData

end

end YangMills.Renormalization
