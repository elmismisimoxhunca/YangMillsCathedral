/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.PositiveDegreeCartanArbitraryFieldChartTransport

namespace YangMills.Mathematics.PositiveDegreeCartanArbitraryFieldChartTransport.Probes

open Set Filter
open scoped Manifold ContDiff Topology
open YangMills.Mathematics

universe uE uH uM uV uW

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable section

/-- Arbitrary-degree transport retains the exact preimage/intersection coordinate set. -/
theorem exact_arbitrary_field_chart_transport
    (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (s : Set M) (p : M) (hp : p ∈ s)
    (fields : Fin (n + 2) → (y : M) → TangentSpace I y)
    (fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields i)) :
    form.toForm.positiveDegreeCartanExpressionCoordinates coordinates n s p fields =
      ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W) n
        (form.toForm.inExtChartAt coordinates (n + 1) p).toManifoldForm
        ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p)
        (fun i => extChartCoordinateField I p (fields i)) :=
  form.positiveDegreeCartanExpressionCoordinates_inExtChartAt_arbitraryFields
    coordinates n s p hp fields fields_smooth

/-- Replacing the exact transported Cartan expression is rejected. -/
theorem changed_arbitrary_field_chart_transport_blocked
    (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (s : Set M) (p : M) (hp : p ∈ s)
    (fields : Fin (n + 2) → (y : M) → TangentSpace I y)
    (fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields i))
    (changed : form.toForm.positiveDegreeCartanExpressionCoordinates coordinates n s p fields ≠
      ManifoldDifferentialForm.positiveDegreeCartanExpressionCoordinates
        (I := modelWithCornersSelf ℝ E) (ContinuousLinearEquiv.refl ℝ W) n
        (form.toForm.inExtChartAt coordinates (n + 1) p).toManifoldForm
        ((extChartAt I p).symm ⁻¹' s ∩ Set.range ⇑I) ((extChartAt I p) p)
        (fun i => extChartCoordinateField I p (fields i))) : False :=
  changed (form.positiveDegreeCartanExpressionCoordinates_inExtChartAt_arbitraryFields
    coordinates n s p hp fields fields_smooth)

/-- Finite-dimensional field-extension independence retains openness through `UniqueMDiffOn`, local
smoothness of both families, and exact equality of every field value at the base point. -/
theorem exact_finiteDimensional_extension_independence
    [FiniteDimensional ℝ E]
    (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (s : Set M) (p : M) (hp : p ∈ s) (unique_s : UniqueMDiffOn I s)
    (fields fields' : Fin (n + 2) → (y : M) → TangentSpace I y)
    (fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields i))
    (fields'_smooth : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields' i))
    (hfields : ∀ i, fields i p = fields' i p) :
    form.toForm.positiveDegreeCartanExpressionCoordinates coordinates n s p fields =
      form.toForm.positiveDegreeCartanExpressionCoordinates coordinates n s p fields' :=
  form.positiveDegreeCartanExpressionCoordinates_congr_at coordinates n s p hp unique_s
    fields fields' fields_smooth fields'_smooth hfields

/-- A hostile disagreement despite identical field values contradicts certificate-free tensoriality. -/
theorem changed_extension_independence_blocked
    [FiniteDimensional ℝ E]
    (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (s : Set M) (p : M) (hp : p ∈ s) (unique_s : UniqueMDiffOn I s)
    (fields fields' : Fin (n + 2) → (y : M) → TangentSpace I y)
    (fields_smooth : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields i))
    (fields'_smooth : ∀ i, ManifoldTangentField.IsSmoothOn I s (fields' i))
    (hfields : ∀ i, fields i p = fields' i p)
    (changed : form.toForm.positiveDegreeCartanExpressionCoordinates coordinates n s p fields ≠
      form.toForm.positiveDegreeCartanExpressionCoordinates coordinates n s p fields') : False :=
  changed (form.positiveDegreeCartanExpressionCoordinates_congr_at coordinates n s p hp unique_s
    fields fields' fields_smooth fields'_smooth hfields)

omit [IsManifold I ∞ M] in
/-- Exact neighborhood-germ equality, not arbitrary set replacement, controls Cartan locality. -/
theorem exact_set_germ_locality
    (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : ManifoldDifferentialForm I M V (n + 1))
    (s t : Set M) (p : M)
    (fields : Fin (n + 2) → (y : M) → TangentSpace I y)
    (hst : s =ᶠ[𝓝 p] t) :
    form.positiveDegreeCartanExpressionCoordinates coordinates n s p fields =
      form.positiveDegreeCartanExpressionCoordinates coordinates n t p fields :=
  form.positiveDegreeCartanExpressionCoordinates_congr_set coordinates n s t p fields hst

end

end YangMills.Mathematics.PositiveDegreeCartanArbitraryFieldChartTransport.Probes
