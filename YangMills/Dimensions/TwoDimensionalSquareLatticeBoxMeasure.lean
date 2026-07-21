/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxPresentation
import YangMills.Dimensions.TwoDimensionalFiniteAxialPushforwardMeasure

/-!
# Normalized finite axial measures on exact square boxes

For every positive radius and one Definition 7.1 action, the exact box presentation has an everywhere
positive measurable finite action weight. Compactness bounds the action uniformly, proving that the
exact product-Haar partition function is finite; positivity and product-Haar normalization prove it
is nonzero. The generic normalized finite measure and its same-extension pushforward therefore
specialize constructively to every exact box.

This constructs finite box measures only, not boundary-conditioned measures, an infinite-volume
limit, or lattice-continuum convergence.
-/

namespace YangMills.Dimensions

open MeasureTheory Set
open YangMills.Mathematics

noncomputable section

universe uG

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)
    (action : TwoDimensionalLatticeActionData G)

/-- Exact finite-coordinate box action weight. -/
def twoDimensionalSquareLatticeBoxWeight :
    (EpsilonSquareLatticeBoxCoordinate spacing radius → G) → ENNReal :=
  twoDimensionalFiniteAxialPlaquetteWeight action
    (twoDimensionalSquareLatticeBoxPresentation spacing radius)

/-- Exact finite box partition function against product Haar probability. -/
def twoDimensionalSquareLatticeBoxNormalizer : ENNReal :=
  twoDimensionalFiniteAxialNormalizer action
    (twoDimensionalSquareLatticeBoxPresentation spacing radius)

namespace twoDimensionalSquareLatticeBoxNormalizer

/-- The exact box partition function is nonzero. -/
theorem ne_zero :
    twoDimensionalSquareLatticeBoxNormalizer spacing radius action ≠ 0 := by
  let presentation := twoDimensionalSquareLatticeBoxPresentation
    (G := G) spacing radius
  letI := presentation.coordinateFintype
  have weightMeasurable := twoDimensionalFiniteAxialPlaquetteWeight.measurable action presentation
  have weightNonzero := twoDimensionalFiniteAxialPlaquetteWeight.ne_zero action presentation
  apply ne_of_gt
  apply (lintegral_pos_iff_support weightMeasurable).mpr
  have support_eq : Function.support
      (twoDimensionalFiniteAxialPlaquetteWeight action presentation) = univ := by
    apply Set.eq_univ_of_forall
    intro configuration
    exact weightNonzero configuration
  rw [support_eq, normalizedCompactHaarFiniteProductMeasure_univ]
  exact zero_lt_one

omit [MeasurableMul₂ G] in
/-- The exact box partition function is finite. -/
theorem ne_top :
    twoDimensionalSquareLatticeBoxNormalizer spacing radius action ≠ ⊤ := by
  let presentation := twoDimensionalSquareLatticeBoxPresentation
    (G := G) spacing radius
  letI := presentation.coordinateFintype
  letI := presentation.plaquetteFintype
  letI := presentation.plaquetteDecidableEq
  obtain ⟨bound, boundProperty⟩ :=
    isCompact_univ.bddAbove_image action.action_continuous.continuousOn
  have action_le_bound : ∀ g, action.action g ≤ bound := by
    intro g
    exact boundProperty ⟨g, Set.mem_univ g, rfl⟩
  have weight_bound : ∀ configuration,
      twoDimensionalFiniteAxialPlaquetteWeight action presentation configuration ≤
        (ENNReal.ofReal bound) ^ (Finset.univ : Finset presentation.Plaquette).card := by
    intro configuration
    change (∏ label : presentation.Plaquette,
      ENNReal.ofReal (action.action
        (epsilonSquareLatticeAxialPlaquetteHolonomy
          (presentation.plaquette label) (presentation.extension configuration)))) ≤ _
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro label _
      exact bot_le
    · intro label _
      exact ENNReal.ofReal_le_ofReal (action_le_bound _)
  have integral_bound :
      twoDimensionalSquareLatticeBoxNormalizer spacing radius action ≤
        (ENNReal.ofReal bound) ^ (Finset.univ : Finset presentation.Plaquette).card := by
    apply le_trans (lintegral_mono weight_bound)
    simp [normalizedCompactHaarFiniteProductMeasure_univ]
  exact ne_top_of_le_ne_top
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) integral_bound

end twoDimensionalSquareLatticeBoxNormalizer

/-- Constructed source-facing normalizer certificate for every exact box. -/
def twoDimensionalSquareLatticeBoxNormalizerData :
    TwoDimensionalFiniteAxialNormalizerData action
      (twoDimensionalSquareLatticeBoxPresentation spacing radius) where
  normalizer_ne_zero := twoDimensionalSquareLatticeBoxNormalizer.ne_zero spacing radius action
  normalizer_ne_top := twoDimensionalSquareLatticeBoxNormalizer.ne_top spacing radius action

/-- Normalized finite-coordinate measure for the exact square box. -/
def twoDimensionalSquareLatticeBoxMeasure :
    Measure (EpsilonSquareLatticeBoxCoordinate spacing radius → G) :=
  twoDimensionalFiniteAxialMeasure action
    (twoDimensionalSquareLatticeBoxPresentation spacing radius)

/-- Same-extension pushforward of the exact box law to the infinite axial carrier. -/
def twoDimensionalSquareLatticeBoxPushforwardMeasure :
    Measure (EpsilonSquareLatticeAxialConfiguration G spacing) :=
  twoDimensionalFiniteAxialPushforwardMeasure action
    (twoDimensionalSquareLatticeBoxPresentation spacing radius)

namespace twoDimensionalSquareLatticeBoxMeasure

/-- Every exact finite box measure has total mass one. -/
theorem apply_univ :
    twoDimensionalSquareLatticeBoxMeasure spacing radius action univ = 1 :=
  twoDimensionalFiniteAxialMeasure.apply_univ action _
    (twoDimensionalSquareLatticeBoxNormalizerData spacing radius action)

/-- Every exact finite box measure is nonzero. -/
theorem ne_zero :
    twoDimensionalSquareLatticeBoxMeasure spacing radius action ≠ 0 :=
  twoDimensionalFiniteAxialMeasure.ne_zero action _
    (twoDimensionalSquareLatticeBoxNormalizerData spacing radius action)

end twoDimensionalSquareLatticeBoxMeasure

namespace twoDimensionalSquareLatticeBoxPushforwardMeasure

/-- The exact box pushforward has total mass one on the infinite axial carrier. -/
theorem apply_univ :
    twoDimensionalSquareLatticeBoxPushforwardMeasure spacing radius action univ = 1 :=
  twoDimensionalFiniteAxialPushforwardMeasure.apply_univ action _
    (twoDimensionalSquareLatticeBoxNormalizerData spacing radius action)

/-- The exact box pushforward is nonzero. -/
theorem ne_zero :
    twoDimensionalSquareLatticeBoxPushforwardMeasure spacing radius action ≠ 0 :=
  twoDimensionalFiniteAxialPushforwardMeasure.ne_zero action _
    (twoDimensionalSquareLatticeBoxNormalizerData spacing radius action)

end twoDimensionalSquareLatticeBoxPushforwardMeasure

end

end YangMills.Dimensions
