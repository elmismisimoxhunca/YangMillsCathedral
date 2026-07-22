/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxActionFactorization
import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxProjectiveConsistency

/-!
# Probes for exact square-box action factorization
-/

namespace YangMills.Dimensions.TwoDimensionalSquareLatticeBoxActionFactorization.Probes

open MeasureTheory Set
open YangMills.Mathematics

noncomputable section

universe uG uI

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (action : TwoDimensionalLatticeActionData G)

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The same normalized action gives a genuine single-plaquette probability law. -/
theorem exact_single_plaquette_probability :
    twoDimensionalPlaquetteActionMeasure action Set.univ = 1 ∧
      IsProbabilityMeasure (twoDimensionalPlaquetteActionMeasure action) :=
  ⟨twoDimensionalPlaquetteActionMeasure.apply_univ action, inferInstance⟩

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Every finite product density factors into the product of the unchanged one-plaquette law. -/
theorem exact_finite_density_factorization (I : Type uI) [Fintype I] :
    (normalizedCompactHaarFiniteProductMeasure I G).withDensity
        (fun values => ∏ i, ENNReal.ofReal (action.action (values i))) =
      twoDimensionalPlaquetteActionFiniteProduct I action :=
  finiteActionProductDensity I action

omit [MeasurableMul₂ G] in
/-- The original coordinate weight is exactly the product density evaluated on actual plaquette
holonomies. -/
theorem exact_weight_coherence
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G) :
    twoDimensionalSquareLatticeBoxWeight spacing radius action configuration =
      twoDimensionalSquareLatticeBoxPlaquetteDensity spacing radius action
        (boxPlaquetteDifferenceForward spacing radius configuration) :=
  twoDimensionalSquareLatticeBoxWeight_eq_plaquetteDensity_comp
    spacing radius action configuration

/-- Definition 7.1 normalization and the exact Haar change of variables force every box partition
function to be one. -/
theorem exact_box_normalizer :
    twoDimensionalSquareLatticeBoxNormalizer spacing radius action = 1 :=
  twoDimensionalSquareLatticeBoxNormalizer_eq_one spacing radius action

/-- The unnormalized density law already pushes forward to the exact product action law; the
normalizer is not used to hide a mismatch. -/
theorem exact_unnormalized_box_pushforward :
    Measure.map (boxPlaquetteDifferenceForward (G := G) spacing radius)
      ((normalizedCompactHaarFiniteProductMeasure
        (EpsilonSquareLatticeBoxCoordinate spacing radius) G).withDensity
          (twoDimensionalSquareLatticeBoxWeight spacing radius action)) =
      twoDimensionalPlaquetteActionFiniteProduct
        (EpsilonSquareLatticeBoxPlaquette spacing radius) action :=
  map_box_unnormalized_eq_plaquetteActionFiniteProduct spacing radius action

/-- The normalized actual coordinate law pushes forward to the exact finite independent
plaquette-action product law. -/
theorem exact_normalized_box_pushforward :
    Measure.map (boxPlaquetteDifferenceForward (G := G) spacing radius)
        (twoDimensionalSquareLatticeBoxMeasure spacing radius action) =
      twoDimensionalPlaquetteActionFiniteProduct
        (EpsilonSquareLatticeBoxPlaquette spacing radius) action :=
  map_twoDimensionalSquareLatticeBoxMeasure_eq_plaquetteActionFiniteProduct
    spacing radius action

/-- A changed box normalizer is incompatible with exact Definition 7.1 factorization. -/
theorem changed_normalizer_blocked (wrong : ENNReal)
    (different : wrong ≠ 1)
    (claimed : wrong = twoDimensionalSquareLatticeBoxNormalizer spacing radius action) : False := by
  apply different
  rw [claimed, twoDimensionalSquareLatticeBoxNormalizer_eq_one]

/-- An unrelated proposed plaquette law cannot replace the exact product pushforward. -/
theorem unrelated_product_law_blocked
    (wrong : Measure (EpsilonSquareLatticeBoxPlaquette spacing radius → G))
    (different : wrong ≠ twoDimensionalPlaquetteActionFiniteProduct
      (EpsilonSquareLatticeBoxPlaquette spacing radius) action)
    (claimed : Measure.map (boxPlaquetteDifferenceForward (G := G) spacing radius)
      (twoDimensionalSquareLatticeBoxMeasure spacing radius action) = wrong) : False := by
  apply different
  rw [← claimed]
  exact map_twoDimensionalSquareLatticeBoxMeasure_eq_plaquetteActionFiniteProduct
    spacing radius action

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- A disconnected replacement for the exact holonomy transform is rejected pointwise. -/
theorem disconnected_holonomy_transform_blocked
    (wrongForward :
      (EpsilonSquareLatticeBoxCoordinate spacing radius → G) →
        EpsilonSquareLatticeBoxPlaquette spacing radius → G)
    (different : wrongForward ≠ boxPlaquetteDifferenceForward spacing radius)
    (claimed : ∀ configuration plaquette,
      wrongForward configuration plaquette =
        epsilonSquareLatticeAxialPlaquetteHolonomy plaquette.1
          (epsilonSquareLatticeBoxAxialExtension spacing radius configuration)) : False := by
  apply different
  funext configuration plaquette
  rw [claimed]
  exact (boxPlaquetteDifferenceForward_eq_holonomy
    spacing radius configuration plaquette).symm

/-- Finite factorization alone cannot silently supply consecutive-box projectivity when one of its
required pushforward equalities is explicitly known to fail. -/
theorem failed_projectivity_not_repaired_by_factorization
    (failedRadius : PositiveSquareLatticeBoxRadius)
    (failure : Measure.map
      (epsilonSquareLatticeBoxCoordinateRestriction (G := G) spacing failedRadius)
      (twoDimensionalSquareLatticeBoxMeasure spacing
        (squareLatticeBoxSuccessorRadius failedRadius) action) ≠
      twoDimensionalSquareLatticeBoxMeasure spacing failedRadius action) :
    ¬ TwoDimensionalSquareLatticeBoxProjectiveConsistencyData spacing action := by
  intro projectivity
  exact failure (projectivity.consecutive_pushforward failedRadius)

end

end YangMills.Dimensions.TwoDimensionalSquareLatticeBoxActionFactorization.Probes
