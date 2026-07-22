/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxPlaquetteDifferenceEquiv

/-!
# Probes for exact square-box plaquette differences
-/

namespace YangMills.Dimensions.TwoDimensionalSquareLatticeBoxPlaquetteDifferenceEquiv.Probes

open YangMills.Mathematics.RootedGroupDifference

noncomputable section

universe uG

variable {G : Type uG} [Group G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)

/-- Upper and lower actual plaquette chains use the intended rooted transforms. -/
theorem exact_chain_transforms
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (horizontal : SquareLatticeBoxHorizontalIndex radius) (index : Fin radius.1) :
    boxPlaquetteDifferenceForward spacing radius configuration
        (boxPlaquetteChainEquiv spacing radius (horizontal, Sum.inl index)) =
        upperForward (boxUpperCoordinateChain spacing radius configuration horizontal) index ∧
      boxPlaquetteDifferenceForward spacing radius configuration
        (boxPlaquetteChainEquiv spacing radius (horizontal, Sum.inr index)) =
        lowerForward (boxLowerCoordinateChain spacing radius configuration horizontal) index :=
  ⟨boxPlaquetteDifferenceForward_chain_inl spacing radius configuration horizontal index,
    boxPlaquetteDifferenceForward_chain_inr spacing radius configuration horizontal index⟩

/-- Forward and recursive recovery are exact two-sided inverses on the actual carriers. -/
theorem exact_inverse_laws
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (differences : EpsilonSquareLatticeBoxPlaquette spacing radius → G) :
    boxPlaquetteDifferenceRecover spacing radius
        (boxPlaquetteDifferenceForward spacing radius configuration) = configuration ∧
      boxPlaquetteDifferenceForward spacing radius
        (boxPlaquetteDifferenceRecover spacing radius differences) = differences :=
  ⟨boxPlaquetteDifferenceRecover_forward spacing radius configuration,
    boxPlaquetteDifferenceForward_recover spacing radius differences⟩

/-- The constructed difference at every actual plaquette is its exact axial holonomy under the same
finite extension; no disconnected plaquette variable may be substituted. -/
theorem exact_forward_is_holonomy
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G)
    (plaquette : EpsilonSquareLatticeBoxPlaquette spacing radius) :
    boxPlaquetteDifferenceForward spacing radius configuration plaquette =
      epsilonSquareLatticeAxialPlaquetteHolonomy plaquette.1
        (epsilonSquareLatticeBoxAxialExtension spacing radius configuration) :=
  boxPlaquetteDifferenceForward_eq_holonomy spacing radius configuration plaquette

section Measurable

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- Both directions of the exact actual-carrier equivalence are measurable. -/
theorem exact_measurable_equivalence :
    Measurable (boxPlaquetteDifferenceMeasurableEquiv (G := G) spacing radius) ∧
      Measurable (boxPlaquetteDifferenceMeasurableEquiv (G := G) spacing radius).symm :=
  ⟨(boxPlaquetteDifferenceMeasurableEquiv (G := G) spacing radius).measurable,
    (boxPlaquetteDifferenceMeasurableEquiv (G := G) spacing radius).measurable_invFun⟩

end Measurable

end

end YangMills.Dimensions.TwoDimensionalSquareLatticeBoxPlaquetteDifferenceEquiv.Probes
