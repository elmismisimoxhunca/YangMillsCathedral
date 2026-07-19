/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanLinearGrowth
import YangMills.Minkowski.WightmanRelativeAnalyticCorrelators
import YangMills.Reconstruction.OSSourceOrderedWickContinuation
import YangMills.Reconstruction.WightmanRealizationUnitaryEquivalence

/-!
# Corrected OS-II reconstruction acceptance

OS-II corrects the reconstruction theorem by strengthening the Euclidean growth requirement, while
Streater–Wightman printed p. 118 gives the appropriate uniqueness conclusion as unitary equivalence
of Wightman realizations. This module combines those two obligations without implementing a
reconstruction algorithm or constructing an output.

A selected output must use one exact Wightman axiom surface, corrected `(R0′)` growth, relative
analytic family, and exact-source Wick continuation. Every other corrected, coherent output for the
same Euclidean family must be unitarily equivalent and have the same full tempered distributions.
Alternative Hilbert carriers may differ, but the exact Poincaré lift is fixed as in the cited
theorem. The quantifier is explicitly universe-relative (`Type uH`), as required by Lean; no
cross-universe classification claim is made.
-/

namespace YangMills.Reconstruction

open YangMills
open Minkowski

universe uG uH

/-- Corrected OS-II reconstruction acceptance for one selected four-dimensional Wightman output.
This is an uninhabited requirement surface, not an existence theorem or construction. -/
structure CorrectedOSIIReconstructionAcceptanceData
    {G₁ : Type uG} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    {lift₁ : ProperOrthochronousPoincareLiftData EuclideanDimension.four G₁}
    {H₁ : Type uH} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [TopologicalSpace.SeparableSpace H₁]
    {U₁ : StronglyContinuousUnitaryPoincareRepresentation lift₁ H₁}
    {vacuum₁ : PoincareInvariantVacuumData U₁}
    {D₁ : CommonInvariantDomainData vacuum₁}
    {field₁ : ScalarWightmanFieldOnCommonDomainData D₁}
    (euclideanFamily : ScalarSchwingerDistributionFamily EuclideanDimension.four)
    (surface₁ : ScalarWightmanAxiomSurfaceData field₁)
    (full₁ : ScalarWightmanJointTemperedCorrelatorData field₁) where
  /-- Corrected OS-II output growth on the selected exact full distributions. -/
  selectedGrowth : OSIIWightmanLinearGrowthData full₁
  /-- Relative analytic data for those same selected full distributions. -/
  selectedRelative : ScalarWightmanRelativeAnalyticCorrelatorData full₁
  /-- Exact-source Wick continuation from the supplied Euclidean family to that same output. -/
  selectedWick : OSSourceOrderedScalarWickContinuationData euclideanFamily selectedRelative
  /-- Every other complete corrected/coherent scalar Wightman output over the same exact lift and
  selected Hilbert universe is equivalent to the selected one and has the same full tempered
  distributions at every arity. -/
  all_outputs_equivalent : ∀
    {H₂ : Type uH} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [TopologicalSpace.SeparableSpace H₂]
    {U₂ : StronglyContinuousUnitaryPoincareRepresentation lift₁ H₂}
    {vacuum₂ : PoincareInvariantVacuumData U₂}
    {D₂ : CommonInvariantDomainData vacuum₂}
    {field₂ : ScalarWightmanFieldOnCommonDomainData D₂}
    (_surface₂ : ScalarWightmanAxiomSurfaceData field₂)
    (full₂ : ScalarWightmanJointTemperedCorrelatorData field₂)
    (_growth₂ : OSIIWightmanLinearGrowthData full₂)
    (relative₂ : ScalarWightmanRelativeAnalyticCorrelatorData full₂)
    (_wick₂ : OSSourceOrderedScalarWickContinuationData euclideanFamily relative₂),
    Nonempty (ScalarWightmanFixedLiftUnitaryEquivalence field₁ field₂) ∧
      ∀ n, full₂.nPointDistribution n = full₁.nPointDistribution n

namespace CorrectedOSIIReconstructionAcceptanceData

/-- Corrected reconstruction uniqueness reaches every exact full Schwartz test value when the
alternative realization has a different Hilbert carrier but the same source-facing Poincaré lift. -/
theorem alternative_distribution_value_eq
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
    full₂.nPointDistribution n test = full₁.nPointDistribution n test := by
  rw [(acceptance.all_outputs_equivalent surface₂ full₂ growth₂ relative₂ wick₂).2 n]

end CorrectedOSIIReconstructionAcceptanceData

end YangMills.Reconstruction
