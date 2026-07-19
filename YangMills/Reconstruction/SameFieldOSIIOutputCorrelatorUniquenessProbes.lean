/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Reconstruction.SameFieldOSIIOutputCorrelatorUniqueness

/-!
# Hostile probes for same-field OS-II output correlator uniqueness

The probes extract the selected `(R0′)`, relative, and exact-source Wick data from the uniqueness
record itself and require all-arity/every-test equality for corrected alternatives. They make no
heterogeneous reconstruction claim.
-/

namespace YangMills.Reconstruction.SameFieldOSIIOutputCorrelatorUniqueness.Probes

open YangMills
open YangMills.Minkowski

variable
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

/-- The selected `(R0′)` belongs to the exact selected full distributions. -/
example : OSIIWightmanLinearGrowthData full :=
  data.selectedGrowth

/-- The selected relative chain belongs to those same distributions. -/
example : ScalarWightmanRelativeAnalyticCorrelatorData full :=
  data.selectedRelative

/-- The selected Wick bridge uses the exact Euclidean family and selected relative chain. -/
example : OSSourceOrderedScalarWickContinuationData
    euclideanFamily data.selectedRelative :=
  data.selectedWick

/-- Corrected alternatives agree at every arity, not merely arity zero. -/
example
    (otherFull : ScalarWightmanJointTemperedCorrelatorData fieldData)
    (otherGrowth : OSIIWightmanLinearGrowthData otherFull)
    (otherRelative : ScalarWightmanRelativeAnalyticCorrelatorData otherFull)
    (otherWick : OSSourceOrderedScalarWickContinuationData euclideanFamily otherRelative)
    (n : ℕ) :
    otherFull.nPointDistribution n = full.nPointDistribution n :=
  data.distribution_unique otherFull otherGrowth otherRelative otherWick n

/-- Equality reaches every exact full Schwartz test. -/
example
    (otherFull : ScalarWightmanJointTemperedCorrelatorData fieldData)
    (otherGrowth : OSIIWightmanLinearGrowthData otherFull)
    (otherRelative : ScalarWightmanRelativeAnalyticCorrelatorData otherFull)
    (otherWick : OSSourceOrderedScalarWickContinuationData euclideanFamily otherRelative)
    (n : ℕ)
    (test : ScalarMinkowskiNPointSchwartzTestFunction EuclideanDimension.four n) :
    otherFull.nPointDistribution n test = full.nPointDistribution n test :=
  data.distribution_value_unique otherFull otherGrowth otherRelative otherWick n test

end YangMills.Reconstruction.SameFieldOSIIOutputCorrelatorUniqueness.Probes
