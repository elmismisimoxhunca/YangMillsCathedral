/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.NormalizedCompactHaarFiniteProduct
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Measurable finite oriented-edge face weights

Finite oriented-word holonomy is measurable as a function of one group coordinate per underlying
edge. Given a finite index of proposed faces, a parameterized measurable nonnegative density, a
parameter for each face, and one oriented boundary word per face, this module constructs the finite
product of the density values and the corresponding `withDensity` measure over finite product Haar.

The words and parameters are deliberately arbitrary finite input here. In particular, this module
does not assert that they arise from embedded planar edges, complementary regions, connected
boundaries, actual areas, or a Yang--Mills law. Consequently no normalization theorem is claimed for
the weighted measure.
-/

namespace YangMills.Mathematics

open MeasureTheory

universe uEdge uFace uG

/-- Evaluation of one oriented edge is measurable on the configuration product measurable space. -/
theorem orientedEdge_eval_measurable
    {Edge : Type uEdge} {G : Type uG}
    [Group G] [MeasurableSpace G] [MeasurableInv G]
    (edge : OrientedEdge Edge) :
    Measurable (fun configuration : Edge → G => OrientedEdge.eval configuration edge) := by
  cases edge with
  | forward edge => exact measurable_pi_apply edge
  | reverse edge => exact (measurable_pi_apply edge).inv

/-- Holonomy of every finite oriented word is measurable in the underlying edge coordinates. -/
theorem finiteOrientedWordHolonomy_measurable
    {Edge : Type uEdge} {G : Type uG}
    [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (word : List (OrientedEdge Edge)) :
    Measurable (fun configuration : Edge → G =>
      finiteOrientedWordHolonomy configuration word) := by
  induction word with
  | nil => exact measurable_const
  | cons edge tail ih =>
      exact ih.mul (orientedEdge_eval_measurable edge)

/-- Product of one unchanged density value for each finite face index, evaluated on that face's
supplied finite oriented boundary word. -/
noncomputable def finiteOrientedFaceDensityProduct
    {Edge : Type uEdge} (Face : Type uFace) [Fintype Face]
    {G : Type uG} [Group G]
    (density : ℝ → G → ENNReal) (faceParameter : Face → ℝ)
    (boundaryWord : Face → List (OrientedEdge Edge))
    (configuration : Edge → G) : ENNReal :=
  ∏ face : Face,
    density (faceParameter face)
      (finiteOrientedWordHolonomy configuration (boundaryWord face))

/-- The finite face-density product is measurable whenever every used parameter slice of the
unchanged density family is measurable. -/
theorem finiteOrientedFaceDensityProduct_measurable
    {Edge : Type uEdge} (Face : Type uFace) [Fintype Face]
    {G : Type uG}
    [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (density : ℝ → G → ENNReal) (faceParameter : Face → ℝ)
    (boundaryWord : Face → List (OrientedEdge Edge))
    (density_measurable : ∀ face, Measurable (density (faceParameter face))) :
    Measurable (finiteOrientedFaceDensityProduct Face density faceParameter boundaryWord) := by
  apply Finset.measurable_fun_prod
  intro face _
  exact (density_measurable face).comp
    (finiteOrientedWordHolonomy_measurable (boundaryWord face))

/-- Finite product Haar weighted by the exact finite oriented-face density product. No probability
normalization is inferred without genuine graph/face hypotheses and a source theorem. -/
noncomputable def finiteOrientedFaceWeightMeasure
    (Edge : Type uEdge) [Fintype Edge]
    (Face : Type uFace) [Fintype Face]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (density : ℝ → G → ENNReal) (faceParameter : Face → ℝ)
    (boundaryWord : Face → List (OrientedEdge Edge)) :
    Measure (Edge → G) :=
  (normalizedCompactHaarFiniteProductMeasure Edge G).withDensity
    (finiteOrientedFaceDensityProduct Face density faceParameter boundaryWord)

end YangMills.Mathematics
