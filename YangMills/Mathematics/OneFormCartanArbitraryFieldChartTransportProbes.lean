/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.OneFormCartanArbitraryFieldChartTransport

/-!
# Hostile probes for arbitrary-field Cartan chart transport
-/

namespace YangMills.Mathematics.OneFormCartanArbitraryFieldChartTransport.Probes

open Set
open scoped Manifold ContDiff

universe uE uH uM uV uW

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]

/-- Exact transport retains arbitrary smooth fields and the corner-aware range-intersection set. -/
theorem exact_arbitrary_field_chart_transport
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (s : Set M) (p : M) (hp : p ∈ s)
    (first second : (y : M) → TangentSpace I y)
    (first_smooth : ManifoldTangentField.IsSmoothOn I s first)
    (second_smooth : ManifoldTangentField.IsSmoothOn I s second) :
    form.toForm.oneFormCartanExpressionCoordinates coordinates s p first second =
      (form.toForm.inExtChartAt coordinates 1 p).toManifoldForm.oneFormCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
        ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p)
        (extChartCoordinateField I p first) (extChartCoordinateField I p second) :=
  SmoothManifoldDifferentialForm.oneFormCartanExpressionCoordinates_inExtChartAt_arbitraryFields
    coordinates form s p hp first second first_smooth second_smooth

/-- Under exact coordinate-form differentiability, intrinsic Cartan expressions are independent of
all admissible smooth extensions with equal point values. -/
theorem exact_intrinsic_extension_independence
    [CompleteSpace E]
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
    form.toForm.oneFormCartanExpressionCoordinates coordinates s p first second =
      form.toForm.oneFormCartanExpressionCoordinates coordinates s p first' second' :=
  SmoothManifoldDifferentialForm.oneFormCartanExpressionCoordinates_congr_at_of_inExtChartAt
    coordinates form s p hp unique_s first second first' second'
    first_smooth second_smooth first'_smooth second'_smooth hfirst hsecond form_differentiable

/-- Finite-dimensional evaluation-based smoothness makes intrinsic extension independence
unconditional on extra coordinate-regularity data. -/
theorem exact_finiteDimensional_intrinsic_extension_independence
    [FiniteDimensional ℝ E]
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (s : Set M) (p : M) (hp : p ∈ s) (unique_s : UniqueMDiffOn I s)
    (first second first' second' : (y : M) → TangentSpace I y)
    (first_smooth : ManifoldTangentField.IsSmoothOn I s first)
    (second_smooth : ManifoldTangentField.IsSmoothOn I s second)
    (first'_smooth : ManifoldTangentField.IsSmoothOn I s first')
    (second'_smooth : ManifoldTangentField.IsSmoothOn I s second')
    (hfirst : first p = first' p) (hsecond : second p = second' p) :
    form.toForm.oneFormCartanExpressionCoordinates coordinates s p first second =
      form.toForm.oneFormCartanExpressionCoordinates coordinates s p first' second' :=
  SmoothManifoldDifferentialForm.oneFormCartanExpressionCoordinates_congr_at
    coordinates form s p hp unique_s first second first' second'
    first_smooth second_smooth first'_smooth second'_smooth hfirst hsecond

/-- A claimed intrinsic discrepancy contradicts the coordinate-regularity transport theorem. -/
theorem mismatched_intrinsic_extension_blocked
    [CompleteSpace E]
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
      form.toForm.oneFormCartanExpressionCoordinates coordinates s p first second ≠
        form.toForm.oneFormCartanExpressionCoordinates coordinates s p first' second') : False :=
  wrong (SmoothManifoldDifferentialForm.oneFormCartanExpressionCoordinates_congr_at_of_inExtChartAt
    coordinates form s p hp unique_s first second first' second'
    first_smooth second_smooth first'_smooth second'_smooth hfirst hsecond form_differentiable)

/-- A finite-dimensional intrinsic discrepancy is rejected without caller-supplied coordinate
regularity. -/
theorem mismatched_finiteDimensional_intrinsic_extension_blocked
    [FiniteDimensional ℝ E]
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (s : Set M) (p : M) (hp : p ∈ s) (unique_s : UniqueMDiffOn I s)
    (first second first' second' : (y : M) → TangentSpace I y)
    (first_smooth : ManifoldTangentField.IsSmoothOn I s first)
    (second_smooth : ManifoldTangentField.IsSmoothOn I s second)
    (first'_smooth : ManifoldTangentField.IsSmoothOn I s first')
    (second'_smooth : ManifoldTangentField.IsSmoothOn I s second')
    (hfirst : first p = first' p) (hsecond : second p = second' p)
    (wrong :
      form.toForm.oneFormCartanExpressionCoordinates coordinates s p first second ≠
        form.toForm.oneFormCartanExpressionCoordinates coordinates s p first' second') : False :=
  wrong (SmoothManifoldDifferentialForm.oneFormCartanExpressionCoordinates_congr_at
    coordinates form s p hp unique_s first second first' second'
    first_smooth second_smooth first'_smooth second'_smooth hfirst hsecond)

/-- Replacing the exact range-intersection coordinate expression by a distinguishable value is
inconsistent with arbitrary-field chart transport. -/
theorem mismatched_arbitrary_field_chart_transport_blocked
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (s : Set M) (p : M) (hp : p ∈ s)
    (first second : (y : M) → TangentSpace I y)
    (first_smooth : ManifoldTangentField.IsSmoothOn I s first)
    (second_smooth : ManifoldTangentField.IsSmoothOn I s second)
    (wrong :
      form.toForm.oneFormCartanExpressionCoordinates coordinates s p first second ≠
        (form.toForm.inExtChartAt coordinates 1 p).toManifoldForm.oneFormCartanExpressionCoordinates
          (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W)
          ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p)
          (extChartCoordinateField I p first) (extChartCoordinateField I p second)) : False :=
  wrong (SmoothManifoldDifferentialForm.oneFormCartanExpressionCoordinates_inExtChartAt_arbitraryFields
    coordinates form s p hp first second first_smooth second_smooth)

end YangMills.Mathematics.OneFormCartanArbitraryFieldChartTransport.Probes
