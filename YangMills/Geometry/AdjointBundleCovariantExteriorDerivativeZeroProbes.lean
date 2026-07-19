/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleCovariantExteriorDerivativeZero

/-!
# Hostile probes for degree-zero adjoint covariant exterior differentiation

These probes lock the unique degree-one slot to the existing intrinsic covariant derivative, retain
the exact input section, reject an unrelated output at any mismatching evaluation, and expose the
same principal connection's local `d + ad(A)` formula.
-/

namespace YangMills.Geometry.AdjointBundleCovariantExteriorDerivativeZero.Probes

open scoped Manifold ContDiff Bundle Topology

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}
    {connection : PrincipalConnectionData smoothBundle}

/-- The sole alternating slot is exactly the existing covariant derivative value. -/
theorem exact_unique_slot
    (data : PrincipalConnectionAdjointCovariantDerivativeData connection)
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 0)
    (b : B) (X : TangentSpace IB b) :
    (data.covariantExteriorDerivativeZero form b) (fun _ => X) =
      data.covariantDerivative (AdjointBundle.DifferentialForm.toSection form) b X := by
  rfl

/-- Repackaging an exact section as degree zero cannot replace the section being differentiated. -/
theorem exact_input_section
    (data : PrincipalConnectionAdjointCovariantDerivativeData connection)
    (adjointSection : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (b : B) (X : TangentSpace IB b) :
    (data.covariantExteriorDerivativeZero
      (AdjointBundle.DifferentialForm.ofSection
        (IB := IB) (bundle := bundle) adjointSection) b) (fun _ => X) =
      data.covariantDerivative adjointSection b X := by
  exact data.covariantExteriorDerivativeZero_ofSection adjointSection b (fun _ => X)

/-- A one-form with even one mismatching evaluation cannot be the derived packaged output. -/
theorem unrelated_output_blocked
    (data : PrincipalConnectionAdjointCovariantDerivativeData connection)
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 0)
    (other : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 1)
    (b : B) (X : TangentSpace IB b)
    (hne : (other b) (fun _ => X) ≠
      data.covariantDerivative (AdjointBundle.DifferentialForm.toSection form) b X) :
    other ≠ data.covariantExteriorDerivativeZero form := by
  intro h
  apply hne
  rw [h]
  rfl

/-- Agreement on every tangent evaluation forces exact equality with the packaged output. -/
theorem exact_evaluation_uniqueness
    (data : PrincipalConnectionAdjointCovariantDerivativeData connection)
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 0)
    (other : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 1)
    (h : ∀ b X, (other b) (fun _ => X) =
      data.covariantDerivative (AdjointBundle.DifferentialForm.toSection form) b X) :
    other = data.covariantExteriorDerivativeZero form :=
  data.eq_covariantExteriorDerivativeZero_of_eval form other h

/-- In exact chart coordinates, the result uses the same connection's ordinary derivative and
bracket correction. -/
theorem exact_same_connection_local_formula
    (data : PrincipalConnectionAdjointCovariantDerivativeData connection)
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 0)
    (form_smooth : AdjointBundle.DifferentialForm.IsSmooth smoothBundle form)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet) (X : TangentSpace IB b) :
    AdjointBundle.DifferentialForm.inCoordinates
        (data.covariantExteriorDerivativeZero form) chart hb (fun _ => X) =
      PrincipalConnectionData.adjointLocalOrdinaryDerivative
          (IG := IG) (IB := IB) (bundle := bundle) chart
          (AdjointBundle.DifferentialForm.toSection form) b X +
        connection.adjointLocalConnectionBracketTerm chart
          (AdjointBundle.DifferentialForm.toSection form) b X := by
  simpa using data.covariantExteriorDerivativeZero_eq_d_add_bracket
    form form_smooth chart chart_mem hb (fun _ => X)

end

end YangMills.Geometry.AdjointBundleCovariantExteriorDerivativeZero.Probes
