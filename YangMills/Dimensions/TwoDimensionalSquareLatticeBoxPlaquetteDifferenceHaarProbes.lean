/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxPlaquetteDifferenceHaar

/-!
# Probes for product-Haar preservation of square-box differences
-/

namespace YangMills.Dimensions.TwoDimensionalSquareLatticeBoxPlaquetteDifferenceHaar.Probes

open MeasureTheory
open YangMills.Mathematics

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]
  (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)

/-- The actual coordinate-to-plaquette map preserves the unchanged normalized product-Haar law. -/
theorem exact_forward_product_haar :
    MeasurePreserving (boxPlaquetteDifferenceForward (G := G) spacing radius)
      (normalizedCompactHaarFiniteProductMeasure
        (EpsilonSquareLatticeBoxCoordinate spacing radius) G)
      (normalizedCompactHaarFiniteProductMeasure
        (EpsilonSquareLatticeBoxPlaquette spacing radius) G) :=
  boxPlaquetteDifferenceForward_normalizedHaar_measurePreserving spacing radius

/-- The explicit recursive inverse preserves the corresponding actual product-Haar law. -/
theorem exact_recovery_product_haar :
    MeasurePreserving (boxPlaquetteDifferenceRecover (G := G) spacing radius)
      (normalizedCompactHaarFiniteProductMeasure
        (EpsilonSquareLatticeBoxPlaquette spacing radius) G)
      (normalizedCompactHaarFiniteProductMeasure
        (EpsilonSquareLatticeBoxCoordinate spacing radius) G) :=
  boxPlaquetteDifferenceRecover_normalizedHaar_measurePreserving spacing radius

/-- The forward pushforward is literally the plaquette-indexed product Haar measure. -/
theorem exact_forward_map_eq :
    Measure.map (boxPlaquetteDifferenceForward (G := G) spacing radius)
        (normalizedCompactHaarFiniteProductMeasure
          (EpsilonSquareLatticeBoxCoordinate spacing radius) G) =
      normalizedCompactHaarFiniteProductMeasure
        (EpsilonSquareLatticeBoxPlaquette spacing radius) G :=
  (boxPlaquetteDifferenceForward_normalizedHaar_measurePreserving spacing radius).map_eq

end

end YangMills.Dimensions.TwoDimensionalSquareLatticeBoxPlaquetteDifferenceHaar.Probes
