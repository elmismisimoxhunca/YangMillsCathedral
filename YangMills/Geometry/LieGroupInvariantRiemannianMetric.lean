/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.LieGroupInvariantMetricPairing
import YangMills.Geometry.LieGroupLeftMaurerCartanCoordinateSmooth
import YangMills.Mathematics.ContinuousBilinearDiagonalPrecomposition
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Smooth invariant Riemannian metric on a finite-dimensional Lie group

An explicitly supplied invariant positive pairing on the Lie algebra determines a smooth
Riemannian metric by left Maurer--Cartan transport. This module completes that construction as
Mathlib's exact `Bundle.ContMDiffRiemannianMetric` structure.

The proof is coordinate-sensitive. It first re-bundles the unchanged Lie-algebra pairing over the
normed model space, then precomposes both slots by the smooth tangent-coordinate Maurer--Cartan
coefficient. On the base set of the tangent trivialization, `inCoordinates_apply_eq₂` identifies
this local polynomial model with the two nested Hom-bundle coordinates of the pointwise metric.
Centerwise equality on a neighborhood gives the required smooth dependent section.

This constructs a metric only from already supplied group and invariant-pairing data. It does not
construct a Yang--Mills measure or theory, and it does not yet identify the project's basis-sum
operator with the metric's Laplace--Beltrami operator.
-/

namespace YangMills.Geometry

open scoped Manifold ContDiff Bundle
open Bundle

noncomputable section

universe uE uH uG

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]
    [FiniteDimensional ℝ E]

/-- The unchanged Lie-algebra pairing re-bundled over the normed model-space instances. This
identity bridge avoids selecting the bounded-convergence topology accidentally at the outer Hom
coordinate. -/
noncomputable def invariantPairingModel
    (inner : InvariantInnerProductData (I := I) (G := G)) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  let modelToLie : E →L[ℝ] GroupLieAlgebra I G :=
    { toLinearMap := LinearMap.id
      cont := continuous_id }
  (ContinuousLinearMap.precomp ℝ modelToLie).comp
    (inner.pairing.comp modelToLie)

omit [FiniteDimensional ℝ E] in
/-- Re-bundling changes no pointwise pairing value. -/
@[simp]
theorem invariantPairingModel_apply
    (inner : InvariantInnerProductData (I := I) (G := G)) (v w : E) :
    invariantPairingModel inner v w = inner.pairing v w :=
  rfl

/-- Polynomial local-coordinate model for the invariant metric at a fixed tangent-trivialization
center. -/
noncomputable def invariantMetricLocalCoordinateModel
    (inner : InvariantInnerProductData (I := I) (G := G)) (center : G) :
    G → (E →L[ℝ] E →L[ℝ] ℝ) := fun x =>
  YangMills.Mathematics.continuousBilinearDiagonalPrecomp
    (invariantPairingModel inner)
    (leftMaurerCartanInTangentCoordinates (I := I) center x)

/-- Exact nested Hom-bundle coordinates of the previously constructed pointwise metric. -/
noncomputable def invariantMetricHomCoordinates
    (inner : InvariantInnerProductData (I := I) (G := G)) (center : G) :
    G → (E →L[ℝ] E →L[ℝ] ℝ) := fun x =>
  ContinuousLinearMap.inCoordinates E (TangentSpace I)
    (E →L[ℝ] ℝ) (fun y : G => TangentSpace I y →L[ℝ] ℝ)
    center x center x (lieGroupInvariantMetricInner inner x)

omit [FiniteDimensional ℝ E] in
/-- On the exact tangent-trivialization base set, the nested Hom-bundle coordinate expression is
the polynomial obtained by precomposing both slots with the tangent-coordinate Maurer--Cartan
coefficient. -/
theorem invariantMetricHomCoordinates_eq_localCoordinateModel
    (inner : InvariantInnerProductData (I := I) (G := G))
    (center x : G) (hx : x ∈ (trivializationAt E (TangentSpace I) center).baseSet) :
    invariantMetricHomCoordinates inner center x =
      invariantMetricLocalCoordinateModel inner center x := by
  ext v w
  unfold invariantMetricHomCoordinates
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  simp only [invariantMetricLocalCoordinateModel,
    YangMills.Mathematics.continuousBilinearDiagonalPrecomp_apply,
    invariantPairingModel_apply, lieGroupInvariantMetricInner_apply]
  have hcoord (z : E) :
      leftMaurerCartanInTangentCoordinates (I := I) center x z =
      mfderiv I I (fun y : G => x⁻¹ * y) x
        ((trivializationAt E (TangentSpace I) center).symm x z) := by
    unfold leftMaurerCartanInTangentCoordinates
    rw [inTangentCoordinates_eq]
    · have hchart : x ∈ (chartAt H center).source := by
        simpa using hx
      simp only [inv_mul_cancel x, inv_mul_cancel center, ContinuousLinearMap.comp_apply]
      rw [tangentCoordChange_self (mem_extChartAt_source (I := I) (x := (1 : G)))]
      change _ = mfderiv I I (fun y : G => x⁻¹ * y) x
        (((trivializationAt E (TangentSpace I) center).symmL ℝ x) z)
      rw [TangentBundle.symmL_trivializationAt_eq_core hchart]
      exact Eq.refl _
    · exact hx
    · simp
  simp only [hcoord]
  simp only [leftMaurerCartanApply, lieGroupLeftTranslation,
    Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq]
  rfl

/-- The polynomial local-coordinate metric model is smooth at every chosen center. -/
theorem invariantMetricLocalCoordinateModel_smoothAt
    (inner : InvariantInnerProductData (I := I) (G := G)) (center : G) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (invariantMetricLocalCoordinateModel inner center) center := by
  exact (YangMills.Mathematics.continuousBilinearDiagonalPrecomp_contDiff
      (invariantPairingModel inner)).comp_contMDiffAt
    (leftMaurerCartanInTangentCoordinates_smoothAt center)

/-- The smooth bi-invariant Riemannian metric determined by the exact supplied invariant pairing.
Its pointwise inner form is definitionally `lieGroupInvariantMetricInner`; symmetry, positivity,
bounded unit ellipsoids, and dependent-section smoothness are all derived. -/
noncomputable def lieGroupInvariantContMDiffRiemannianMetric
    (inner : InvariantInnerProductData (I := I) (G := G)) :
    Bundle.ContMDiffRiemannianMetric I ∞ E (fun g : G => TangentSpace I g) where
  inner := lieGroupInvariantMetricInner inner
  symm := lieGroupInvariantMetricInner_symmetric inner
  pos := lieGroupInvariantMetricInner_positive inner
  isVonNBounded := lieGroupInvariantMetricInner_isVonNBounded inner
  contMDiff := by
    intro center
    rw [contMDiffAt_section]
    simp only [hom_trivializationAt_apply]
    apply (invariantMetricLocalCoordinateModel_smoothAt inner center).congr_of_eventuallyEq
    filter_upwards [((trivializationAt E (TangentSpace I) center).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) center))] with x hx
    exact invariantMetricHomCoordinates_eq_localCoordinateModel inner center x hx

/-- The packaged Riemannian metric retains exactly the previously constructed pointwise pairing. -/
@[simp]
theorem lieGroupInvariantContMDiffRiemannianMetric_inner
    (inner : InvariantInnerProductData (I := I) (G := G))
    (g : G) (v w : TangentSpace I g) :
    (lieGroupInvariantContMDiffRiemannianMetric inner).inner g v w =
      lieGroupInvariantMetricInner inner g v w :=
  rfl

end

end YangMills.Geometry
