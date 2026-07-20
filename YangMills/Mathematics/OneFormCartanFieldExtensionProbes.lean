/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.OneFormCartanFieldExtension

/-!
# Hostile probes for Cartan field-extension independence
-/

namespace YangMills.Mathematics.OneFormCartanFieldExtension.Probes

open Set
open scoped Manifold ContDiff

universe uE uH uM uV uW

/-- Normed-space Cartan expressions depend only on the two field values at the point. -/
theorem exact_normed_extension_independence
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (form : NormedSpaceDifferentialForm E W 1) (s : Set E) (x : E)
    (first second first' second' : E → E)
    (form_differentiable : DifferentiableWithinAt ℝ form s x)
    (first_differentiable : DifferentiableWithinAt ℝ first s x)
    (second_differentiable : DifferentiableWithinAt ℝ second s x)
    (first'_differentiable : DifferentiableWithinAt ℝ first' s x)
    (second'_differentiable : DifferentiableWithinAt ℝ second' s x)
    (unique : UniqueDiffWithinAt ℝ s x)
    (first_eq : first x = first' x) (second_eq : second x = second' x) :
    form.toManifoldForm.oneFormCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
        s x first second =
      form.toManifoldForm.oneFormCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
        s x first' second' :=
  form.oneFormCartanExpressionCoordinates_congr_at s x first second first' second'
    form_differentiable first_differentiable second_differentiable
    first'_differentiable second'_differentiable unique first_eq second_eq

/-- Equal tangent values give equal centered-chart coordinate-field values. -/
theorem exact_center_coordinate_value
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace M] (I : ModelWithCorners ℝ E H) [ChartedSpace H M]
    (p : M) (first second : (y : M) → TangentSpace I y)
    (h : first p = second p) :
    extChartCoordinateField I p first ((extChartAt I p) p) =
      extChartCoordinateField I p second ((extChartAt I p) p) :=
  extChartCoordinateField_eq_at_center I p first second h

/-- Smooth manifold fields give differentiable centered-chart coordinates on the exact corner-aware
range-intersection set. -/
theorem exact_chart_coordinate_regularity
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace H] [TopologicalSpace M]
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [IsManifold I ∞ M]
    (s : Set M) (p : M) (hp : p ∈ s)
    (field : (y : M) → TangentSpace I y)
    (field_smooth : ManifoldTangentField.IsSmoothOn I s field) :
    DifferentiableWithinAt ℝ (extChartCoordinateField I p field)
      ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p) :=
  extChartCoordinateField_differentiableWithinAt I s p hp field field_smooth

/-- Centered-chart Cartan expressions are extension-independent on the exact corner-aware set. -/
theorem exact_chart_extension_independence
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
        (extChartCoordinateField I p first') (extChartCoordinateField I p second') :=
  inExtChart_oneFormCartanExpressionCoordinates_eq_of_eq_at I coordinates form s p hp unique_s
    first second first' second' first_smooth second_smooth first'_smooth second'_smooth
    hfirst hsecond form_differentiable

/-- A claimed discrepancy on the exact centered-chart range-intersection set is inconsistent. -/
theorem changed_chart_extension_blocked
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
      ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p))
    (wrong :
      (form.toForm.inExtChartAt coordinates 1 p).toManifoldForm.oneFormCartanExpressionCoordinates
          (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
          ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p)
          (extChartCoordinateField I p first) (extChartCoordinateField I p second) ≠
        (form.toForm.inExtChartAt coordinates 1 p).toManifoldForm.oneFormCartanExpressionCoordinates
          (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
          ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p)
          (extChartCoordinateField I p first') (extChartCoordinateField I p second')) : False :=
  wrong (inExtChart_oneFormCartanExpressionCoordinates_eq_of_eq_at
    I coordinates form s p hp unique_s first second first' second'
    first_smooth second_smooth first'_smooth second'_smooth hfirst hsecond form_differentiable)

/-- Any already supplied manifold Cartan certificate forces intrinsic field-extension independence. -/
theorem exact_certified_extension_independence
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]
    {coordinates : V ≃L[ℝ] W}
    {form : SmoothManifoldDifferentialForm I M V coordinates 1}
    (certificate : SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form)
    (s : Set M) (x : M) (open_s : IsOpen s) (mem_s : x ∈ s)
    (unique_s : UniqueMDiffOn I s)
    (first second first' second' : (x : M) → TangentSpace I x)
    (first_smooth : ManifoldTangentField.IsSmoothOn I s first)
    (second_smooth : ManifoldTangentField.IsSmoothOn I s second)
    (first'_smooth : ManifoldTangentField.IsSmoothOn I s first')
    (second'_smooth : ManifoldTangentField.IsSmoothOn I s second')
    (first_eq : first x = first' x) (second_eq : second x = second' x) :
    form.toForm.oneFormCartanExpressionCoordinates coordinates s x first second =
      form.toForm.oneFormCartanExpressionCoordinates coordinates s x first' second' :=
  SmoothManifoldOneFormExteriorDerivativeCertificate.cartan_expression_congr_at
    I coordinates form certificate s x open_s mem_s unique_s
    first second first' second' first_smooth second_smooth first'_smooth second'_smooth
    first_eq second_eq

/-- A claimed intrinsic discrepancy contradicts an exact supplied Cartan certificate. -/
theorem changed_certified_extension_blocked
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]
    {coordinates : V ≃L[ℝ] W}
    {form : SmoothManifoldDifferentialForm I M V coordinates 1}
    (certificate : SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form)
    (s : Set M) (x : M) (open_s : IsOpen s) (mem_s : x ∈ s)
    (unique_s : UniqueMDiffOn I s)
    (first second first' second' : (x : M) → TangentSpace I x)
    (first_smooth : ManifoldTangentField.IsSmoothOn I s first)
    (second_smooth : ManifoldTangentField.IsSmoothOn I s second)
    (first'_smooth : ManifoldTangentField.IsSmoothOn I s first')
    (second'_smooth : ManifoldTangentField.IsSmoothOn I s second')
    (first_eq : first x = first' x) (second_eq : second x = second' x)
    (wrong :
      form.toForm.oneFormCartanExpressionCoordinates coordinates s x first second ≠
        form.toForm.oneFormCartanExpressionCoordinates coordinates s x first' second') : False :=
  wrong (SmoothManifoldOneFormExteriorDerivativeCertificate.cartan_expression_congr_at
    I coordinates form certificate s x open_s mem_s unique_s
    first second first' second' first_smooth second_smooth first'_smooth second'_smooth
    first_eq second_eq)

/-- A claimed discrepancy between differentiable normed extensions with equal point values is
inconsistent. -/
theorem changed_normed_extension_blocked
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (form : NormedSpaceDifferentialForm E W 1) (s : Set E) (x : E)
    (first second first' second' : E → E)
    (form_differentiable : DifferentiableWithinAt ℝ form s x)
    (first_differentiable : DifferentiableWithinAt ℝ first s x)
    (second_differentiable : DifferentiableWithinAt ℝ second s x)
    (first'_differentiable : DifferentiableWithinAt ℝ first' s x)
    (second'_differentiable : DifferentiableWithinAt ℝ second' s x)
    (unique : UniqueDiffWithinAt ℝ s x)
    (first_eq : first x = first' x) (second_eq : second x = second' x)
    (wrong :
      form.toManifoldForm.oneFormCartanExpressionCoordinates
          (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
          s x first second ≠
        form.toManifoldForm.oneFormCartanExpressionCoordinates
          (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
          s x first' second') : False :=
  wrong (form.oneFormCartanExpressionCoordinates_congr_at s x
    first second first' second' form_differentiable first_differentiable
    second_differentiable first'_differentiable second'_differentiable unique
    first_eq second_eq)

end YangMills.Mathematics.OneFormCartanFieldExtension.Probes
