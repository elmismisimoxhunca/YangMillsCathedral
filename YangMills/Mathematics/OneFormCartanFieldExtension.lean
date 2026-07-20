/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldOneFormExtChartNaturality

namespace YangMills.Mathematics

/-!
# Field-extension independence for one-form Cartan expressions

In normed spaces, Mathlib's exterior derivative proves that the Cartan expression depends only on
the two field values at the base point. This file also packages the exact centered extended-chart
coordinate fields, proves their value and regularity properties, and derives coordinate-level
extension independence on the corner-aware set `chart.symm ⁻¹' s ∩ Set.range I`. Finally, any
already supplied manifold Cartan certificate yields intrinsic extension independence.

The certificate-based intrinsic theorem is downstream only: using it to construct that same
certificate would be circular. Arbitrary-field partial-chart transport is supplied downstream;
generic derivation of alternating-map-valued coordinate-form regularity remains required for
unconditional intrinsic tensoriality.
-/

open Set
open scoped Manifold ContDiff

/-- The normed-space Cartan expression only depends on the values of its field
extensions at the base point. -/
theorem NormedSpaceDifferentialForm.oneFormCartanExpressionCoordinates_congr_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (form : NormedSpaceDifferentialForm E W 1) (s : Set E) (x : E)
    (first second first' second' : E → E)
    (form_differentiable : DifferentiableWithinAt ℝ form s x)
    (first_differentiable : DifferentiableWithinAt ℝ first s x)
    (second_differentiable : DifferentiableWithinAt ℝ second s x)
    (first'_differentiable : DifferentiableWithinAt ℝ first' s x)
    (second'_differentiable : DifferentiableWithinAt ℝ second' s x)
    (unique : UniqueDiffWithinAt ℝ s x)
    (hfirst : first x = first' x) (hsecond : second x = second' x) :
    form.toManifoldForm.oneFormCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
        s x first second =
      form.toManifoldForm.oneFormCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
        s x first' second' := by
  rw [← form.extDerivWithin_eq_oneFormCartanExpression s x first second
      form_differentiable first_differentiable second_differentiable unique,
    ← form.extDerivWithin_eq_oneFormCartanExpression s x first' second'
      form_differentiable first'_differentiable second'_differentiable unique]
  congr 1
  funext i
  fin_cases i
  · exact hfirst
  · exact hsecond

/-- Coordinate representation of a manifold tangent field in the extended chart centered at `p`. -/
noncomputable def extChartCoordinateField
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E H) [ChartedSpace H M]
    (p : M) (field : (y : M) → TangentSpace I y) : E → E :=
  VectorField.mpullbackWithin (modelWithCornersSelf ℝ E) I
    (extChartAt I p).symm field (Set.range ⇑I)

/-- Equality of tangent vectors at the chart center gives equality of their coordinate fields there. -/
theorem extChartCoordinateField_eq_at_center
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E H) [ChartedSpace H M]
    (p : M) (first second : (y : M) → TangentSpace I y)
    (h : first p = second p) :
    extChartCoordinateField I p first ((extChartAt I p) p) =
      extChartCoordinateField I p second ((extChartAt I p) p) := by
  simp only [extChartCoordinateField, VectorField.mpullbackWithin_apply]
  rw [extChartAt_to_inv p, h]

/-- Smooth manifold fields give differentiable coordinate fields on the exact set used by
Mathlib's chart-local Lie bracket. -/
theorem extChartCoordinateField_differentiableWithinAt
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace H] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I ∞ M]
    (s : Set M) (p : M) (hp : p ∈ s)
    (field : (y : M) → TangentSpace I y)
    (field_smooth : ManifoldTangentField.IsSmoothOn I s field) :
    DifferentiableWithinAt ℝ (extChartCoordinateField I p field)
      ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p) := by
  apply MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField
  exact (field_smooth p hp).mdifferentiableWithinAt (by simp)

/-- Checked chart-local reduction: after expressing manifold fields in the centered extended
chart, the coordinate Cartan expression is extension-independent. The remaining missing bridge is
its identification with the intrinsic manifold Cartan expression for arbitrary (not constant)
fields. -/
theorem inExtChart_oneFormCartanExpressionCoordinates_eq_of_eq_at
    {E H M V W : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace H]
    [TopologicalSpace M]
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I ∞ M]
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (s : Set M) (p : M) (hp : p ∈ s) (unique_s : UniqueMDiffOn I s)
    (first second first' second' : (y : M) → TangentSpace I y)
    (first_smooth : ManifoldTangentField.IsSmoothOn I s first)
    (second_smooth : ManifoldTangentField.IsSmoothOn I s second)
    (first'_smooth : ManifoldTangentField.IsSmoothOn I s first')
    (second'_smooth : ManifoldTangentField.IsSmoothOn I s second')
    (hfirst : first p = first' p) (hsecond : second p = second' p)
    (form_differentiable : DifferentiableWithinAt ℝ
      (form.toForm.inExtChartAt coordinates 1 p)
      ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p)) :
    (form.toForm.inExtChartAt coordinates 1 p).toManifoldForm.oneFormCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
        ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p)
        (extChartCoordinateField I p first) (extChartCoordinateField I p second) =
      (form.toForm.inExtChartAt coordinates 1 p).toManifoldForm.oneFormCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
        ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p)
        (extChartCoordinateField I p first') (extChartCoordinateField I p second') := by
  apply NormedSpaceDifferentialForm.oneFormCartanExpressionCoordinates_congr_at
    (form_differentiable := form_differentiable)
    (first_differentiable := extChartCoordinateField_differentiableWithinAt
      I s p hp first first_smooth)
    (second_differentiable := extChartCoordinateField_differentiableWithinAt
      I s p hp second second_smooth)
    (first'_differentiable := extChartCoordinateField_differentiableWithinAt
      I s p hp first' first'_smooth)
    (second'_differentiable := extChartCoordinateField_differentiableWithinAt
      I s p hp second' second'_smooth)
  · rw [inter_comm]
    apply unique_s.uniqueDiffWithinAt_range_inter p
    exact ⟨mem_extChartAt_target p, by simpa using hp⟩
  · exact extChartCoordinateField_eq_at_center I p first first' hfirst
  · exact extChartCoordinateField_eq_at_center I p second second' hsecond

/-- Any existing Cartan certificate immediately forces extension independence on an
arbitrary manifold. This is useful downstream but is circular if used to construct the certificate. -/
theorem SmoothManifoldOneFormExteriorDerivativeCertificate.cartan_expression_congr_at
    {E H M V W : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace M]
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I ∞ M]
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (certificate : SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form)
    (s : Set M) (x : M) (open_s : IsOpen s) (mem_s : x ∈ s)
    (unique_s : UniqueMDiffOn I s)
    (first second first' second' : (y : M) → TangentSpace I y)
    (first_smooth : ManifoldTangentField.IsSmoothOn I s first)
    (second_smooth : ManifoldTangentField.IsSmoothOn I s second)
    (first'_smooth : ManifoldTangentField.IsSmoothOn I s first')
    (second'_smooth : ManifoldTangentField.IsSmoothOn I s second')
    (hfirst : first x = first' x) (hsecond : second x = second' x) :
    form.toForm.oneFormCartanExpressionCoordinates coordinates s x first second =
      form.toForm.oneFormCartanExpressionCoordinates coordinates s x first' second' := by
  rw [← certificate.cartan_formula s x open_s mem_s unique_s
      first second first_smooth second_smooth,
    ← certificate.cartan_formula s x open_s mem_s unique_s
      first' second' first'_smooth second'_smooth]
  congr 2
  funext i
  fin_cases i
  · exact hfirst
  · exact hsecond

end YangMills.Mathematics
