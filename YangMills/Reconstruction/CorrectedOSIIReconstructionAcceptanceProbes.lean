/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Reconstruction.CorrectedOSIIReconstructionAcceptance

/-!
# Hostile probes for corrected OS-II reconstruction acceptance

The probes force selected `(R0′)`, relative analytic, and source-Wick data to share the same full
correlator family and force every same-lift, heterogeneous-Hilbert alternative to provide both unitary equivalence and
all-arity full-distribution equality. They construct no output or equivalence.
-/

namespace YangMills.Reconstruction.CorrectedOSIIReconstructionAcceptance.Probes

open YangMills
open YangMills.Minkowski

universe uG uH

variable
    {G₁ : Type uG} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    {lift₁ : ProperOrthochronousPoincareLiftData EuclideanDimension.four G₁}
    {H₁ : Type uH} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [TopologicalSpace.SeparableSpace H₁]
    {U₁ : StronglyContinuousUnitaryPoincareRepresentation lift₁ H₁}
    {vacuum₁ : PoincareInvariantVacuumData U₁}
    {D₁ : CommonInvariantDomainData vacuum₁}
    {field₁ : ScalarWightmanFieldOnCommonDomainData D₁}
    {euclideanFamily : ScalarSchwingerDistributionFamily EuclideanDimension.four}
    {surface₁ : ScalarWightmanAxiomSurfaceData field₁}
    {full₁ : ScalarWightmanJointTemperedCorrelatorData field₁}
    (acceptance : CorrectedOSIIReconstructionAcceptanceData euclideanFamily surface₁ full₁)

/-- Selected corrected growth constrains the exact selected full family. -/
example : OSIIWightmanLinearGrowthData full₁ := acceptance.selectedGrowth

/-- Relative analyticity uses that same selected family. -/
example : ScalarWightmanRelativeAnalyticCorrelatorData full₁ :=
  acceptance.selectedRelative

/-- Source Wick continuation uses the exact selected relative family. -/
example : OSSourceOrderedScalarWickContinuationData
    euclideanFamily acceptance.selectedRelative :=
  acceptance.selectedWick

/-- A same-lift corrected output on another Hilbert carrier must be equivalent and distributionally identical. -/
example
    {H₂ : Type uH} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [TopologicalSpace.SeparableSpace H₂]
    {U₂ : StronglyContinuousUnitaryPoincareRepresentation lift₁ H₂}
    {vacuum₂ : PoincareInvariantVacuumData U₂}
    {D₂ : CommonInvariantDomainData vacuum₂}
    {field₂ : ScalarWightmanFieldOnCommonDomainData D₂}
    (surface₂ : ScalarWightmanAxiomSurfaceData field₂)
    (full₂ : ScalarWightmanJointTemperedCorrelatorData field₂)
    (growth₂ : OSIIWightmanLinearGrowthData full₂)
    (relative₂ : ScalarWightmanRelativeAnalyticCorrelatorData full₂)
    (wick₂ : OSSourceOrderedScalarWickContinuationData euclideanFamily relative₂) :
    Nonempty (ScalarWightmanFixedLiftUnitaryEquivalence field₁ field₂) ∧
      ∀ n, full₂.nPointDistribution n = full₁.nPointDistribution n :=
  acceptance.all_outputs_equivalent surface₂ full₂ growth₂ relative₂ wick₂

/-- All-arity distribution equality reaches each exact full Schwartz test value. -/
example
    {H₂ : Type uH} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [TopologicalSpace.SeparableSpace H₂]
    {U₂ : StronglyContinuousUnitaryPoincareRepresentation lift₁ H₂}
    {vacuum₂ : PoincareInvariantVacuumData U₂}
    {D₂ : CommonInvariantDomainData vacuum₂}
    {field₂ : ScalarWightmanFieldOnCommonDomainData D₂}
    (surface₂ : ScalarWightmanAxiomSurfaceData field₂)
    (full₂ : ScalarWightmanJointTemperedCorrelatorData field₂)
    (growth₂ : OSIIWightmanLinearGrowthData full₂)
    (relative₂ : ScalarWightmanRelativeAnalyticCorrelatorData full₂)
    (wick₂ : OSSourceOrderedScalarWickContinuationData euclideanFamily relative₂)
    (n : ℕ) (test : ScalarMinkowskiNPointSchwartzTestFunction EuclideanDimension.four n) :
    full₂.nPointDistribution n test = full₁.nPointDistribution n test :=
  acceptance.alternative_distribution_value_eq
    surface₂ full₂ growth₂ relative₂ wick₂ n test

end YangMills.Reconstruction.CorrectedOSIIReconstructionAcceptance.Probes
