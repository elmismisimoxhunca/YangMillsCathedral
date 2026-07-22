/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalSquareLatticeBoxPlaquetteDifferenceEquiv
import YangMills.Mathematics.RootedGroupDifferenceMeasurePreserving
import YangMills.Mathematics.NormalizedCompactHaarFiniteProduct
import Mathlib.Probability.ProductMeasure

/-!
# Product-Haar preservation of square-box plaquette differences

The exact box coordinate-to-plaquette difference equivalence preserves normalized compact Haar
product measure. The proof splits upper/lower row chains, applies rooted Haar preservation in each
horizontal column, takes the product across columns, and reindexes through the literal coordinate
and plaquette chain equivalences. Both the forward holonomy map and its recursive inverse preserve
the corresponding actual finite product measures.

This is a finite-cutoff change-of-variables theorem, not projective consistency or a continuum law.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics
open YangMills.Mathematics.RootedGroupDifference

noncomputable section

set_option linter.unusedSectionVars false

universe uG
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]
  (spacing : PositiveLatticeSpacing) (radius : PositiveSquareLatticeBoxRadius)

local notation "μH" => normalizedCompactHaarMeasure G

private def boxColumnDifferenceForward
    (values : Fin radius.1 ⊕ Fin radius.1 → G) : Fin radius.1 ⊕ Fin radius.1 → G
  | Sum.inl i => upperForward (fun j => values (Sum.inl j)) i
  | Sum.inr i => lowerForward (fun j => values (Sum.inr j)) i

private theorem boxColumnDifferenceForward_eq_splitComposition :
    (boxColumnDifferenceForward (G := G) radius) =
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin radius.1 ⊕ Fin radius.1 => G)).symm ∘
      Prod.map (upperForward : (Fin radius.1 → G) → (Fin radius.1 → G))
        (lowerForward : (Fin radius.1 → G) → (Fin radius.1 → G)) ∘
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin radius.1 ⊕ Fin radius.1 => G)) := by
  funext values branch
  rcases branch with i | i <;> rfl

private theorem boxColumnDifferenceForward_measurePreserving :
    MeasurePreserving (boxColumnDifferenceForward (G := G) radius)
      (Measure.pi fun _ : Fin radius.1 ⊕ Fin radius.1 => μH)
      (Measure.pi fun _ : Fin radius.1 ⊕ Fin radius.1 => μH) := by
  letI : IsProbabilityMeasure μH := normalizedCompactHaarMeasure_isProbability G
  letI : Measure.IsMulLeftInvariant μH :=
    (normalizedCompactHaarMeasure_isHaar G).toIsMulLeftInvariant
  letI : Measure.IsMulRightInvariant μH :=
    normalizedCompactHaarMeasure_isMulRightInvariant G
  letI : Measure.IsInvInvariant μH :=
    normalizedCompactHaarMeasure_isInvInvariant G
  let split := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin radius.1 ⊕ Fin radius.1 => G)
  have splitMP : MeasurePreserving split
      (Measure.pi fun _ : Fin radius.1 ⊕ Fin radius.1 => μH)
      ((Measure.pi fun _ : Fin radius.1 => μH).prod
        (Measure.pi fun _ : Fin radius.1 => μH)) := by
    simpa [split] using
      (measurePreserving_sumPiEquivProdPi
        (fun _ : Fin radius.1 ⊕ Fin radius.1 => μH))
  have pairMP : MeasurePreserving
      (Prod.map (upperForward : (Fin radius.1 → G) → (Fin radius.1 → G))
        (lowerForward : (Fin radius.1 → G) → (Fin radius.1 → G)))
      ((Measure.pi fun _ : Fin radius.1 => μH).prod
        (Measure.pi fun _ : Fin radius.1 => μH))
      ((Measure.pi fun _ : Fin radius.1 => μH).prod
        (Measure.pi fun _ : Fin radius.1 => μH)) :=
    (upperForward_measurePreserving μH).prod (lowerForward_measurePreserving μH)
  rw [boxColumnDifferenceForward_eq_splitComposition (G := G) radius]
  exact (MeasurePreserving.symm split splitMP).comp (pairMP.comp splitMP)

private theorem curry_normalizedHaar_measurePreserving
    (Horizontal Branch : Type*) [Fintype Horizontal] [Fintype Branch] :
    MeasurePreserving (MeasurableEquiv.curry Horizontal Branch G)
      (Measure.pi fun _ : Horizontal × Branch => μH)
      (Measure.pi fun _ : Horizontal => Measure.pi fun _ : Branch => μH) := by
  letI : IsProbabilityMeasure μH := normalizedCompactHaarMeasure_isProbability G
  refine ⟨(MeasurableEquiv.curry Horizontal Branch G).measurable, ?_⟩
  rw [← Measure.infinitePi_eq_pi]
  rw [← Measure.infinitePi_eq_pi]
  rw [← Measure.infinitePi_eq_pi]
  exact Measure.infinitePi_map_curry (fun _ : Horizontal => fun _ : Branch => μH)

private def commonBoxDifferenceForward
    (values : SquareLatticeBoxHorizontalIndex radius ×
      (Fin radius.1 ⊕ Fin radius.1) → G) :
    SquareLatticeBoxHorizontalIndex radius ×
      (Fin radius.1 ⊕ Fin radius.1) → G :=
  fun index => boxColumnDifferenceForward (G := G) radius (fun branch =>
    values (index.1, branch)) index.2

private theorem commonBoxDifferenceForward_measurePreserving :
    MeasurePreserving
      (commonBoxDifferenceForward (G := G) radius)
      (Measure.pi fun _ : SquareLatticeBoxHorizontalIndex radius ×
        (Fin radius.1 ⊕ Fin radius.1) => μH)
      (Measure.pi fun _ : SquareLatticeBoxHorizontalIndex radius ×
        (Fin radius.1 ⊕ Fin radius.1) => μH) := by
  letI : IsProbabilityMeasure μH := normalizedCompactHaarMeasure_isProbability G
  let Horizontal := SquareLatticeBoxHorizontalIndex radius
  let Branch := Fin radius.1 ⊕ Fin radius.1
  let flat : Measure (Horizontal × Branch → G) := Measure.pi fun _ => μH
  let nested : Measure (Horizontal → Branch → G) :=
    Measure.pi fun _ => Measure.pi fun _ => μH
  have curryMP : MeasurePreserving (MeasurableEquiv.curry Horizontal Branch G) flat nested :=
    curry_normalizedHaar_measurePreserving (G := G) Horizontal Branch
  have columnsMP : MeasurePreserving
      (fun values : Horizontal → Branch → G =>
        fun horizontal => boxColumnDifferenceForward (G := G) radius (values horizontal))
      nested nested := by
    exact measurePreserving_pi
      (fun _ : Horizontal => Measure.pi fun _ : Branch => μH)
      (fun _ : Horizontal => Measure.pi fun _ : Branch => μH)
      (fun _ => boxColumnDifferenceForward_measurePreserving (G := G) radius)
  have uncurryMP : MeasurePreserving (MeasurableEquiv.curry Horizontal Branch G).symm
      nested flat := MeasurePreserving.symm _ curryMP
  exact uncurryMP.comp (columnsMP.comp curryMP)

private def boxCoordinateChainReindex :
    (SquareLatticeBoxHorizontalIndex radius ×
      (Fin radius.1 ⊕ Fin radius.1) → G) ≃ᵐ
      (EpsilonSquareLatticeBoxCoordinate spacing radius → G) :=
  MeasurableEquiv.piCongrLeft (fun _ : EpsilonSquareLatticeBoxCoordinate spacing radius => G)
    (boxCoordinateChainEquiv spacing radius)

private def boxPlaquetteChainReindex :
    (SquareLatticeBoxHorizontalIndex radius ×
      (Fin radius.1 ⊕ Fin radius.1) → G) ≃ᵐ
      (EpsilonSquareLatticeBoxPlaquette spacing radius → G) :=
  MeasurableEquiv.piCongrLeft (fun _ : EpsilonSquareLatticeBoxPlaquette spacing radius => G)
    (boxPlaquetteChainEquiv spacing radius)

private theorem boxPlaquetteDifferenceForward_eq_reindexedCommon :
    (boxPlaquetteDifferenceForward (G := G) spacing radius) =
      boxPlaquetteChainReindex (G := G) spacing radius ∘
        commonBoxDifferenceForward (G := G) radius ∘
          (boxCoordinateChainReindex (G := G) spacing radius).symm := by
  funext configuration plaquette
  obtain ⟨⟨horizontal, branch⟩, rfl⟩ :=
    (boxPlaquetteChainEquiv spacing radius).surjective plaquette
  rcases branch with index | index
  · rw [boxPlaquetteDifferenceForward_chain_inl]
    simp only [Function.comp_apply, boxPlaquetteChainReindex, boxCoordinateChainReindex,
      MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply,
      commonBoxDifferenceForward, boxColumnDifferenceForward]
    congr 1
  · rw [boxPlaquetteDifferenceForward_chain_inr]
    simp only [Function.comp_apply, boxPlaquetteChainReindex, boxCoordinateChainReindex,
      MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply,
      commonBoxDifferenceForward, boxColumnDifferenceForward]
    congr 1

private theorem boxCoordinateChainReindex_measurePreserving :
    MeasurePreserving (boxCoordinateChainReindex (G := G) spacing radius)
      (normalizedCompactHaarFiniteProductMeasure
        (SquareLatticeBoxHorizontalIndex radius × (Fin radius.1 ⊕ Fin radius.1)) G)
      (normalizedCompactHaarFiniteProductMeasure
        (EpsilonSquareLatticeBoxCoordinate spacing radius) G) := by
  letI : IsProbabilityMeasure μH := normalizedCompactHaarMeasure_isProbability G
  simpa [boxCoordinateChainReindex, normalizedCompactHaarFiniteProductMeasure] using
    (measurePreserving_piCongrLeft
      (fun _ : EpsilonSquareLatticeBoxCoordinate spacing radius => μH)
      (boxCoordinateChainEquiv spacing radius))

private theorem boxPlaquetteChainReindex_measurePreserving :
    MeasurePreserving (boxPlaquetteChainReindex (G := G) spacing radius)
      (normalizedCompactHaarFiniteProductMeasure
        (SquareLatticeBoxHorizontalIndex radius × (Fin radius.1 ⊕ Fin radius.1)) G)
      (normalizedCompactHaarFiniteProductMeasure
        (EpsilonSquareLatticeBoxPlaquette spacing radius) G) := by
  letI : IsProbabilityMeasure μH := normalizedCompactHaarMeasure_isProbability G
  simpa [boxPlaquetteChainReindex, normalizedCompactHaarFiniteProductMeasure] using
    (measurePreserving_piCongrLeft
      (fun _ : EpsilonSquareLatticeBoxPlaquette spacing radius => μH)
      (boxPlaquetteChainEquiv spacing radius))

/-- The exact coordinate-to-plaquette holonomy transform preserves normalized compact Haar product
measure on the actual finite carriers. -/
theorem boxPlaquetteDifferenceForward_normalizedHaar_measurePreserving :
    MeasurePreserving (boxPlaquetteDifferenceForward (G := G) spacing radius)
      (normalizedCompactHaarFiniteProductMeasure
        (EpsilonSquareLatticeBoxCoordinate spacing radius) G)
      (normalizedCompactHaarFiniteProductMeasure
        (EpsilonSquareLatticeBoxPlaquette spacing radius) G) := by
  let commonMeasure := normalizedCompactHaarFiniteProductMeasure
    (SquareLatticeBoxHorizontalIndex radius × (Fin radius.1 ⊕ Fin radius.1)) G
  have commonMP : MeasurePreserving (commonBoxDifferenceForward (G := G) radius)
      commonMeasure commonMeasure := by
    simpa [commonMeasure, normalizedCompactHaarFiniteProductMeasure] using
      commonBoxDifferenceForward_measurePreserving (G := G) radius
  rw [boxPlaquetteDifferenceForward_eq_reindexedCommon (G := G) spacing radius]
  exact (boxPlaquetteChainReindex_measurePreserving (G := G) spacing radius).comp
    (commonMP.comp
      (MeasurePreserving.symm (boxCoordinateChainReindex (G := G) spacing radius)
        (boxCoordinateChainReindex_measurePreserving (G := G) spacing radius)))

/-- The exact recursive inverse preserves normalized compact Haar product measure in the reverse
direction. -/
theorem boxPlaquetteDifferenceRecover_normalizedHaar_measurePreserving :
    MeasurePreserving (boxPlaquetteDifferenceRecover (G := G) spacing radius)
      (normalizedCompactHaarFiniteProductMeasure
        (EpsilonSquareLatticeBoxPlaquette spacing radius) G)
      (normalizedCompactHaarFiniteProductMeasure
        (EpsilonSquareLatticeBoxCoordinate spacing radius) G) := by
  exact MeasurePreserving.symm
    (boxPlaquetteDifferenceMeasurableEquiv (G := G) spacing radius)
    (boxPlaquetteDifferenceForward_normalizedHaar_measurePreserving
      (G := G) spacing radius)

end
end YangMills.Dimensions
