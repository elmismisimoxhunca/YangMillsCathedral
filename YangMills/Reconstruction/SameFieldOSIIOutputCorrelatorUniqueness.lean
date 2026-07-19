/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanLinearGrowth
import YangMills.Minkowski.WightmanRelativeAnalyticCorrelators
import YangMills.Reconstruction.OSSourceOrderedWickContinuation

/-!
# Same-field OS-II output correlator uniqueness

This module packages one supplied full Wightman correlator family together with `(R0′)`, its relative
analytic chain, and exact-source Wick coherence. It requires equality of all distributions for any
alternative corrected/coherent correlator extension on the exact same field, Hilbert space, vacuum,
domain, and representation.

This is deliberately not called reconstruction acceptance or Wightman-theory uniqueness. It is a
narrow same-realization correlator-extension uniqueness obligation. Heterogeneous reconstructed
realizations still require a unitary-equivalence notion. No output, theory, or mass gap is
constructed.
-/

namespace YangMills.Reconstruction

open YangMills
open Minkowski

/-- Selected corrected-output correlator data and uniqueness among alternatives on the same exact
field realization. -/
structure SameFieldOSIIOutputCorrelatorUniquenessData
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData EuclideanDimension.four G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {fieldData : ScalarWightmanFieldOnCommonDomainData D}
    (euclideanFamily : ScalarSchwingerDistributionFamily EuclideanDimension.four)
    (full : ScalarWightmanJointTemperedCorrelatorData fieldData) where
  /-- Corrected OS-II output growth on the selected exact full distributions. -/
  selectedGrowth : OSIIWightmanLinearGrowthData full
  /-- Selected relative analytic chain derived from those same full distributions. -/
  selectedRelative : ScalarWightmanRelativeAnalyticCorrelatorData full
  /-- Exact-source Wick coherence for that same selected relative chain. -/
  selectedWick : OSSourceOrderedScalarWickContinuationData
    euclideanFamily selectedRelative
  /-- Every alternative `(R0′)`/source-Wick-coherent correlator extension on this same field
  realization has the selected distributions at every arity. -/
  distribution_unique : ∀
    (otherFull : ScalarWightmanJointTemperedCorrelatorData fieldData)
    (_otherGrowth : OSIIWightmanLinearGrowthData otherFull)
    (otherRelative : ScalarWightmanRelativeAnalyticCorrelatorData otherFull)
    (_otherWick : OSSourceOrderedScalarWickContinuationData euclideanFamily otherRelative)
    (n : ℕ),
    otherFull.nPointDistribution n = full.nPointDistribution n

namespace SameFieldOSIIOutputCorrelatorUniquenessData

/-- Same-field uniqueness reaches every exact full Schwartz test value. -/
theorem distribution_value_unique
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData EuclideanDimension.four G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {fieldData : ScalarWightmanFieldOnCommonDomainData D}
    {euclideanFamily : ScalarSchwingerDistributionFamily EuclideanDimension.four}
    {full : ScalarWightmanJointTemperedCorrelatorData fieldData}
    (data : SameFieldOSIIOutputCorrelatorUniquenessData euclideanFamily full)
    (otherFull : ScalarWightmanJointTemperedCorrelatorData fieldData)
    (otherGrowth : OSIIWightmanLinearGrowthData otherFull)
    (otherRelative : ScalarWightmanRelativeAnalyticCorrelatorData otherFull)
    (otherWick : OSSourceOrderedScalarWickContinuationData euclideanFamily otherRelative)
    (n : ℕ) (test : ScalarMinkowskiNPointSchwartzTestFunction EuclideanDimension.four n) :
    otherFull.nPointDistribution n test = full.nPointDistribution n test := by
  rw [data.distribution_unique otherFull otherGrowth otherRelative otherWick n]

end SameFieldOSIIOutputCorrelatorUniquenessData

end YangMills.Reconstruction
