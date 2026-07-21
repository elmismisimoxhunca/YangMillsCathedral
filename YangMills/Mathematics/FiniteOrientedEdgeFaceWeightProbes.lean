/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.FiniteOrientedEdgeFaceWeight

/-!
# Probes for finite oriented-edge face weights

The probes pin measurable reverse-order word holonomy, the exact finite density product, and its
`withDensity` carrier. They retain the legitimate face-free endpoint and do not assert generic
normalization.
-/

namespace YangMills.Mathematics.FiniteOrientedEdgeFaceWeight.Probes

open MeasureTheory

universe uEdge uFace uG

variable
    {Edge : Type uEdge} {Face : Type uFace} [Fintype Face]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G] in
/-- Exact finite-word holonomy is measurable on edge configurations. -/
theorem exact_word_measurable (word : List (OrientedEdge Edge)) :
    Measurable (fun configuration : Edge → G =>
      finiteOrientedWordHolonomy configuration word) :=
  finiteOrientedWordHolonomy_measurable word

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The face weight uses one exact unchanged density value at each supplied face word. -/
theorem exact_face_density_product
    (density : ℝ → G → ENNReal) (faceParameter : Face → ℝ)
    (boundaryWord : Face → List (OrientedEdge Edge)) (configuration : Edge → G) :
    finiteOrientedFaceDensityProduct Face density faceParameter boundaryWord configuration =
      ∏ face : Face,
        density (faceParameter face)
          (finiteOrientedWordHolonomy configuration (boundaryWord face)) :=
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G] in
/-- Measurability is derived from the exact used density slices and finite boundary words. -/
theorem exact_face_density_measurable
    (density : ℝ → G → ENNReal) (faceParameter : Face → ℝ)
    (boundaryWord : Face → List (OrientedEdge Edge))
    (density_measurable : ∀ face, Measurable (density (faceParameter face))) :
    Measurable (finiteOrientedFaceDensityProduct Face density faceParameter boundaryWord) :=
  finiteOrientedFaceDensityProduct_measurable
    Face density faceParameter boundaryWord density_measurable

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- The weighted carrier is exactly `withDensity` over one normalized-Haar factor per edge. -/
theorem exact_weighted_measure [Fintype Edge]
    (density : ℝ → G → ENNReal) (faceParameter : Face → ℝ)
    (boundaryWord : Face → List (OrientedEdge Edge)) :
    finiteOrientedFaceWeightMeasure Edge Face G density faceParameter boundaryWord =
      (normalizedCompactHaarFiniteProductMeasure Edge G).withDensity
        (finiteOrientedFaceDensityProduct Face density faceParameter boundaryWord) :=
  rfl

omit [MeasurableMul₂ G] [MeasurableInv G] in
/-- A legitimate face-free finite graph retains unweighted product Haar rather than being rejected
by a false face-nonemptiness premise. -/
theorem faceFree_weightMeasure_eq_productHaar [Fintype Edge]
    (density : ℝ → G → ENNReal) :
    finiteOrientedFaceWeightMeasure Edge Empty G density
        (fun face => nomatch face) (fun face => nomatch face) =
      normalizedCompactHaarFiniteProductMeasure Edge G := by
  have density_eq_one :
      finiteOrientedFaceDensityProduct Empty density
          (fun face => nomatch face) (fun face => nomatch face) =
        (fun _ : Edge → G => 1) := by
    funext configuration
    simp [finiteOrientedFaceDensityProduct]
  rw [finiteOrientedFaceWeightMeasure, density_eq_one]
  simp

end YangMills.Mathematics.FiniteOrientedEdgeFaceWeight.Probes
