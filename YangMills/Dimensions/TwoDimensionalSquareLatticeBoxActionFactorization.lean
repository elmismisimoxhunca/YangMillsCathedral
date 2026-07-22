/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxPlaquetteDifferenceHaar
import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxMeasure
import YangMills.Mathematics.MeasurableEquivWithDensity
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Exact factorization of finite square-box action laws

A normalized Driver Definition 7.1 action defines a one-plaquette probability measure. Finite
products of its density factor exactly into products of that law. Transport through the exact
product-Haar-preserving box holonomy equivalence proves that every square-box normalizer is one and
that the normalized coordinate law pushes forward to the independent plaquette-action product law.

This is a finite-cutoff factorization theorem. Consecutive-box projectivity and any infinite-volume
or continuum limit remain separate.
-/

namespace YangMills.Dimensions

open MeasureTheory Set
open YangMills.Mathematics

noncomputable section

universe uG uI

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]

/-- Single normalized Definition 7.1 plaquette action law. -/
def twoDimensionalPlaquetteActionMeasure
    (action : TwoDimensionalLatticeActionData G) : Measure G :=
  (normalizedCompactHaarMeasure G).withDensity
    (fun g => ENNReal.ofReal (action.action g))

namespace TwoDimensionalLatticeActionData

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Compact continuity makes a Definition 7.1 action integrable against normalized Haar. -/
theorem action_integrable (action : TwoDimensionalLatticeActionData G) :
    Integrable action.action (normalizedCompactHaarMeasure G) := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  rw [← integrableOn_univ]
  exact action.action_continuous.continuousOn.integrableOn_of_subset_isCompact
    isCompact_univ MeasurableSet.univ Subset.rfl (by simp)

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The ENNReal density has lintegral one. -/
theorem lintegral_action_toENNReal (action : TwoDimensionalLatticeActionData G) :
    ∫⁻ g, ENNReal.ofReal (action.action g) ∂normalizedCompactHaarMeasure G = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal action.action_integrable
    (Filter.Eventually.of_forall fun g => (action.action_pos g).le)]
  rw [action.action_integral_normalized]
  simp

end TwoDimensionalLatticeActionData


namespace twoDimensionalPlaquetteActionMeasure

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The single-plaquette law has total mass one. -/
theorem apply_univ (action : TwoDimensionalLatticeActionData G) :
    twoDimensionalPlaquetteActionMeasure action Set.univ = 1 := by
  rw [twoDimensionalPlaquetteActionMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact action.lintegral_action_toENNReal

/-- The single-plaquette action law is a probability measure. -/
instance instIsProbabilityMeasure (action : TwoDimensionalLatticeActionData G) :
    IsProbabilityMeasure (twoDimensionalPlaquetteActionMeasure action) :=
  ⟨apply_univ action⟩

end twoDimensionalPlaquetteActionMeasure

/-- Finite product of the one-plaquette action law. -/
def twoDimensionalPlaquetteActionFiniteProduct
    (I : Type uI) [Fintype I]
    (action : TwoDimensionalLatticeActionData G) : Measure (I → G) :=
  Measure.pi fun _ : I => twoDimensionalPlaquetteActionMeasure action

private theorem measure_map_equiv_injective
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (equiv : α ≃ᵐ β) :
    Function.Injective (Measure.map equiv : Measure α → Measure β) := by
  intro first second equality
  have mappedBack := congrArg (Measure.map equiv.symm) equality
  simpa only [equiv.map_symm_map] using mappedBack

omit [MeasurableMul₂ G] [MeasurableInv G] in
private theorem actionDensity_measurable (action : TwoDimensionalLatticeActionData G) :
    Measurable (fun g : G => ENNReal.ofReal (action.action g)) :=
  ENNReal.measurable_ofReal.comp action.action_continuous.measurable

omit [MeasurableMul₂ G] [MeasurableInv G] in
private theorem finiteActionDensity_measurable {I : Type*} [Fintype I]
    (action : TwoDimensionalLatticeActionData G) :
    Measurable (fun values : I → G => ∏ i, ENNReal.ofReal (action.action (values i))) := by
  apply Finset.measurable_prod
  intro i _
  exact (actionDensity_measurable action).comp (measurable_pi_apply i)

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- On a finite `Fin` chain, the density product equals the product of the single action laws. -/
theorem finiteActionProductDensity_fin (action : TwoDimensionalLatticeActionData G) :
    ∀ n : ℕ,
      (normalizedCompactHaarFiniteProductMeasure (Fin n) G).withDensity
          (fun values => ∏ i, ENNReal.ofReal (action.action (values i))) =
        twoDimensionalPlaquetteActionFiniteProduct (Fin n) action := by
  intro n
  induction n with
  | zero =>
      ext set setMeasurable
      have set_cases : set = ∅ ∨ set = Set.univ := by
        by_cases empty : set = ∅
        · exact Or.inl empty
        · right
          apply Set.eq_univ_of_forall
          intro value
          by_contra absent
          apply empty
          ext other
          have value_eq : other = value := Subsingleton.elim _ _
          subst other
          simp [absent]
      rcases set_cases with rfl | rfl
      · simp
      · rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        simp [normalizedCompactHaarFiniteProductMeasure,
          twoDimensionalPlaquetteActionFiniteProduct]
  | succ n inductionHypothesis =>
      let μH : Measure G := normalizedCompactHaarMeasure G
      let μA : Measure G := twoDimensionalPlaquetteActionMeasure action
      let baseTail : Measure (Fin n → G) := normalizedCompactHaarFiniteProductMeasure (Fin n) G
      let actionTail : Measure (Fin n → G) := twoDimensionalPlaquetteActionFiniteProduct (Fin n) action
      let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) (0 : Fin (n + 1))
      have splitBase : Measure.map split
          (normalizedCompactHaarFiniteProductMeasure (Fin (n + 1)) G) =
          μH.prod baseTail := by
        letI : IsProbabilityMeasure μH := normalizedCompactHaarMeasure_isProbability G
        simpa [split, μH, baseTail, normalizedCompactHaarFiniteProductMeasure] using
          (measurePreserving_piFinSuccAbove
            (fun _ : Fin (n + 1) => μH) (0 : Fin (n + 1))).map_eq
      have splitAction : Measure.map split
          (twoDimensionalPlaquetteActionFiniteProduct (Fin (n + 1)) action) =
          μA.prod actionTail := by
        letI : IsProbabilityMeasure μA :=
          twoDimensionalPlaquetteActionMeasure.instIsProbabilityMeasure action
        simpa [split, μA, actionTail, twoDimensionalPlaquetteActionFiniteProduct] using
          (measurePreserving_piFinSuccAbove
            (fun _ : Fin (n + 1) => μA) (0 : Fin (n + 1))).map_eq
      apply measure_map_equiv_injective split
      rw [splitAction]
      let headDensity : G → ENNReal := fun g => ENNReal.ofReal (action.action g)
      let tailDensity : (Fin n → G) → ENNReal :=
        fun values => ∏ i, ENNReal.ofReal (action.action (values i))
      have density_comp :
          (fun values : Fin (n + 1) → G =>
            ∏ i, ENNReal.ofReal (action.action (values i))) =
          (fun pair : G × (Fin n → G) => headDensity pair.1 * tailDensity pair.2) ∘ split := by
        funext values
        rw [Fin.prod_univ_succ]
        change _ = headDensity (values 0) * tailDensity (Fin.tail values)
        congr 1
      have pairDensity_measurable : Measurable
          (fun pair : G × (Fin n → G) => headDensity pair.1 * tailDensity pair.2) :=
        ((actionDensity_measurable action).comp measurable_fst).mul
          ((finiteActionDensity_measurable action).comp measurable_snd)
      rw [density_comp,
        MeasurableEquiv.map_withDensity_comp split _ _ pairDensity_measurable]
      rw [splitBase]
      letI : IsProbabilityMeasure baseTail :=
        ⟨by simpa [baseTail] using
          normalizedCompactHaarFiniteProductMeasure_univ (Fin n) G⟩
      rw [← prod_withDensity (actionDensity_measurable action)
        (finiteActionDensity_measurable action)]
      change (μH.withDensity headDensity).prod (baseTail.withDensity tailDensity) = _
      rw [show μH.withDensity headDensity = μA by rfl]
      rw [show baseTail.withDensity tailDensity = actionTail by
        simpa [baseTail, actionTail] using inductionHypothesis]

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- Product-density factorization for every finite index type. -/
theorem finiteActionProductDensity
    (I : Type uI) [Fintype I] (action : TwoDimensionalLatticeActionData G) :
    (normalizedCompactHaarFiniteProductMeasure I G).withDensity
        (fun values => ∏ i, ENNReal.ofReal (action.action (values i))) =
      twoDimensionalPlaquetteActionFiniteProduct I action := by
  let indexEquiv : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let reindex := MeasurableEquiv.piCongrLeft (fun _ : I => G) indexEquiv
  let μH : Measure G := normalizedCompactHaarMeasure G
  let μA : Measure G := twoDimensionalPlaquetteActionMeasure action
  let finDensity : (Fin (Fintype.card I) → G) → ENNReal :=
    fun values => ∏ i, ENNReal.ofReal (action.action (values i))
  have reindexBaseMP : MeasurePreserving reindex
      (normalizedCompactHaarFiniteProductMeasure (Fin (Fintype.card I)) G)
      (normalizedCompactHaarFiniteProductMeasure I G) := by
    letI : IsProbabilityMeasure μH := normalizedCompactHaarMeasure_isProbability G
    simpa [reindex, μH, normalizedCompactHaarFiniteProductMeasure] using
      (measurePreserving_piCongrLeft (fun _ : I => μH) indexEquiv)
  have reindexActionMP : MeasurePreserving reindex
      (twoDimensionalPlaquetteActionFiniteProduct (Fin (Fintype.card I)) action)
      (twoDimensionalPlaquetteActionFiniteProduct I action) := by
    letI : IsProbabilityMeasure μA :=
      twoDimensionalPlaquetteActionMeasure.instIsProbabilityMeasure action
    simpa [reindex, μA, twoDimensionalPlaquetteActionFiniteProduct] using
      (measurePreserving_piCongrLeft (fun _ : I => μA) indexEquiv)
  have density_comp :
      (fun values : I → G => ∏ i, ENNReal.ofReal (action.action (values i))) =
        finDensity ∘ reindex.symm := by
    funext values
    simp only [finDensity, reindex, Function.comp_apply]
    exact (indexEquiv.prod_comp
      (fun i => ENNReal.ofReal (action.action (values i)))).symm
  apply measure_map_equiv_injective reindex.symm
  rw [density_comp,
    MeasurableEquiv.map_withDensity_comp reindex.symm _ finDensity
      (finiteActionDensity_measurable action)]
  rw [(MeasurePreserving.symm reindex reindexBaseMP).map_eq]
  rw [(MeasurePreserving.symm reindex reindexActionMP).map_eq]
  exact finiteActionProductDensity_fin action (Fintype.card I)

variable (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)

/-- Product action density on the actual box-plaquette function carrier. -/
def twoDimensionalSquareLatticeBoxPlaquetteDensity
    (action : TwoDimensionalLatticeActionData G)
    (values : EpsilonSquareLatticeBoxPlaquette spacing radius → G) : ENNReal :=
  ∏ plaquette, ENNReal.ofReal (action.action (values plaquette))

omit [MeasurableMul₂ G] in
/-- The original finite-coordinate box weight is exactly the plaquette product density after the
actual holonomy difference transform. -/
theorem twoDimensionalSquareLatticeBoxWeight_eq_plaquetteDensity_comp
    (action : TwoDimensionalLatticeActionData G)
    (configuration : EpsilonSquareLatticeBoxCoordinate spacing radius → G) :
    twoDimensionalSquareLatticeBoxWeight spacing radius action configuration =
      twoDimensionalSquareLatticeBoxPlaquetteDensity spacing radius action
        (boxPlaquetteDifferenceForward spacing radius configuration) := by
  change (∏ plaquette : EpsilonSquareLatticeBoxPlaquette spacing radius,
      ENNReal.ofReal (action.action
        (epsilonSquareLatticeAxialPlaquetteHolonomy plaquette.1
          (epsilonSquareLatticeBoxAxialExtension spacing radius configuration)))) = _
  apply Finset.prod_congr rfl
  intro plaquette _
  rw [boxPlaquetteDifferenceForward_eq_holonomy]

/-- The exact square-box normalizer is one. -/
theorem twoDimensionalSquareLatticeBoxNormalizer_eq_one
    (action : TwoDimensionalLatticeActionData G) :
    twoDimensionalSquareLatticeBoxNormalizer spacing radius action = 1 := by
  let coordinateMeasure := normalizedCompactHaarFiniteProductMeasure
    (EpsilonSquareLatticeBoxCoordinate spacing radius) G
  let plaquetteMeasure := normalizedCompactHaarFiniteProductMeasure
    (EpsilonSquareLatticeBoxPlaquette spacing radius) G
  let forward := boxPlaquetteDifferenceForward (G := G) spacing radius
  let density := twoDimensionalSquareLatticeBoxPlaquetteDensity spacing radius action
  have densityMeasurable : Measurable density := by
    exact finiteActionDensity_measurable action
  have forwardMP : MeasurePreserving forward coordinateMeasure plaquetteMeasure := by
    exact boxPlaquetteDifferenceForward_normalizedHaar_measurePreserving spacing radius
  change ∫⁻ configuration,
    twoDimensionalSquareLatticeBoxWeight spacing radius action configuration
      ∂coordinateMeasure = 1
  simp_rw [twoDimensionalSquareLatticeBoxWeight_eq_plaquetteDensity_comp]
  rw [← lintegral_map densityMeasurable forwardMP.measurable]
  rw [forwardMP.map_eq]
  have factorization := finiteActionProductDensity
    (EpsilonSquareLatticeBoxPlaquette spacing radius) action
  have probability :
      twoDimensionalPlaquetteActionFiniteProduct
        (EpsilonSquareLatticeBoxPlaquette spacing radius) action Set.univ = 1 := by
    letI : ∀ _ : EpsilonSquareLatticeBoxPlaquette spacing radius,
        IsProbabilityMeasure (twoDimensionalPlaquetteActionMeasure action) :=
      fun _ => twoDimensionalPlaquetteActionMeasure.instIsProbabilityMeasure action
    simp [twoDimensionalPlaquetteActionFiniteProduct]
  rw [← probability, ← factorization]
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp [density, plaquetteMeasure, twoDimensionalSquareLatticeBoxPlaquetteDensity]

/-- The unnormalized box density law pushes forward to the finite product of the one-plaquette
action law. -/
theorem map_box_unnormalized_eq_plaquetteActionFiniteProduct
    (action : TwoDimensionalLatticeActionData G) :
    Measure.map (boxPlaquetteDifferenceForward (G := G) spacing radius)
      ((normalizedCompactHaarFiniteProductMeasure
        (EpsilonSquareLatticeBoxCoordinate spacing radius) G).withDensity
          (twoDimensionalSquareLatticeBoxWeight spacing radius action)) =
      twoDimensionalPlaquetteActionFiniteProduct
        (EpsilonSquareLatticeBoxPlaquette spacing radius) action := by
  let coordinateMeasure := normalizedCompactHaarFiniteProductMeasure
    (EpsilonSquareLatticeBoxCoordinate spacing radius) G
  let plaquetteMeasure := normalizedCompactHaarFiniteProductMeasure
    (EpsilonSquareLatticeBoxPlaquette spacing radius) G
  let forward := boxPlaquetteDifferenceForward (G := G) spacing radius
  let density := twoDimensionalSquareLatticeBoxPlaquetteDensity spacing radius action
  have densityMeasurable : Measurable density := finiteActionDensity_measurable action
  have forwardMP : MeasurePreserving forward coordinateMeasure plaquetteMeasure :=
    boxPlaquetteDifferenceForward_normalizedHaar_measurePreserving spacing radius
  have weight_comp : twoDimensionalSquareLatticeBoxWeight spacing radius action =
      density ∘ forward := by
    funext configuration
    exact twoDimensionalSquareLatticeBoxWeight_eq_plaquetteDensity_comp
      spacing radius action configuration
  rw [weight_comp]
  have forward_eq :
      (boxPlaquetteDifferenceMeasurableEquiv (G := G) spacing radius :
        (EpsilonSquareLatticeBoxCoordinate spacing radius → G) →
          (EpsilonSquareLatticeBoxPlaquette spacing radius → G)) = forward := rfl
  calc
    Measure.map forward (coordinateMeasure.withDensity (density ∘ forward)) =
        (Measure.map forward coordinateMeasure).withDensity density := by
      rw [← forward_eq]
      exact MeasurableEquiv.map_withDensity_comp
        (boxPlaquetteDifferenceMeasurableEquiv (G := G) spacing radius)
        coordinateMeasure density densityMeasurable
    _ = plaquetteMeasure.withDensity density := by rw [forwardMP.map_eq]
    _ = twoDimensionalPlaquetteActionFiniteProduct
        (EpsilonSquareLatticeBoxPlaquette spacing radius) action := by
      have density_eq : density =
          (fun values : EpsilonSquareLatticeBoxPlaquette spacing radius → G =>
            ∏ i, ENNReal.ofReal (action.action (values i))) := rfl
      rw [density_eq]
      exact finiteActionProductDensity
        (EpsilonSquareLatticeBoxPlaquette spacing radius) action

/-- The normalized box law has the same exact finite product pushforward because its normalizer is
one. -/
theorem map_twoDimensionalSquareLatticeBoxMeasure_eq_plaquetteActionFiniteProduct
    (action : TwoDimensionalLatticeActionData G) :
    Measure.map (boxPlaquetteDifferenceForward (G := G) spacing radius)
      (twoDimensionalSquareLatticeBoxMeasure spacing radius action) =
      twoDimensionalPlaquetteActionFiniteProduct
        (EpsilonSquareLatticeBoxPlaquette spacing radius) action := by
  change Measure.map (boxPlaquetteDifferenceForward (G := G) spacing radius)
    ((twoDimensionalSquareLatticeBoxNormalizer spacing radius action)⁻¹ •
      (normalizedCompactHaarFiniteProductMeasure
        (EpsilonSquareLatticeBoxCoordinate spacing radius) G).withDensity
          (twoDimensionalSquareLatticeBoxWeight spacing radius action)) = _
  rw [twoDimensionalSquareLatticeBoxNormalizer_eq_one spacing radius action]
  simp only [inv_one, one_smul]
  exact map_box_unnormalized_eq_plaquetteActionFiniteProduct spacing radius action

end
end YangMills.Dimensions
