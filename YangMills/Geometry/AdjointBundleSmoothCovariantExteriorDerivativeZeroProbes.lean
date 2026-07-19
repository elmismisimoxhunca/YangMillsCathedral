/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleSmoothCovariantExteriorDerivativeZero

/-!
# Hostile probes for smooth degree-zero adjoint covariant exterior differentiation

These probes ensure that smoothness belongs to the exact pointwise output, forgetting smoothness
recovers the earlier same-connection packaging, evaluation remains unchanged, and the local formula
still uses that same connection.
-/

namespace YangMills.Geometry.AdjointBundleSmoothCovariantExteriorDerivativeZero.Probes

open Set
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

/-- The derived smoothness proof is attached to the exact same pointwise output. -/
theorem exact_smooth_output
    (data : SmoothPrincipalConnectionAdjointCovariantDerivativeData connection)
    (form : AdjointBundle.DifferentialForm.Smooth smoothBundle 0) :
    AdjointBundle.DifferentialForm.IsSmooth smoothBundle
      (data.toCovariantDerivativeData.covariantExteriorDerivativeZero form.toForm) :=
  (data.covariantExteriorDerivativeZero form).smooth

/-- Forgetting smoothness cannot replace the earlier pointwise one-form. -/
theorem exact_pointwise_output
    (data : SmoothPrincipalConnectionAdjointCovariantDerivativeData connection)
    (form : AdjointBundle.DifferentialForm.Smooth smoothBundle 0) :
    (data.covariantExteriorDerivativeZero form).toForm =
      data.toCovariantDerivativeData.covariantExteriorDerivativeZero form.toForm :=
  rfl

/-- The smooth wrapper retains the exact original derivative evaluation. -/
theorem exact_unique_slot
    (data : SmoothPrincipalConnectionAdjointCovariantDerivativeData connection)
    (form : AdjointBundle.DifferentialForm.Smooth smoothBundle 0)
    (b : B) (X : TangentSpace IB b) :
    ((data.covariantExteriorDerivativeZero form).toForm b) (fun _ => X) =
      data.toCovariantDerivativeData.covariantDerivative
        (AdjointBundle.DifferentialForm.toSection form.toForm) b X := by
  rfl

/-- A smooth form with a different pointwise carrier cannot be the derived smooth output. -/
theorem unrelated_smooth_output_blocked
    (data : SmoothPrincipalConnectionAdjointCovariantDerivativeData connection)
    (form : AdjointBundle.DifferentialForm.Smooth smoothBundle 0)
    (other : AdjointBundle.DifferentialForm.Smooth smoothBundle 1)
    (hne : other.toForm ≠
      data.toCovariantDerivativeData.covariantExteriorDerivativeZero form.toForm) :
    other ≠ data.covariantExteriorDerivativeZero form := by
  intro h
  apply hne
  rw [h]
  rfl

/-- The smooth output retains the same connection's exact local `d + ad(A)` expression. -/
theorem exact_same_connection_local_formula
    (data : SmoothPrincipalConnectionAdjointCovariantDerivativeData connection)
    (form : AdjointBundle.DifferentialForm.Smooth smoothBundle 0)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet) (X : TangentSpace IB b) :
    AdjointBundle.DifferentialForm.inCoordinates
        (data.covariantExteriorDerivativeZero form).toForm chart hb (fun _ => X) =
      PrincipalConnectionData.adjointLocalOrdinaryDerivative
          (IG := IG) (IB := IB) (bundle := bundle) chart
          (AdjointBundle.DifferentialForm.toSection form.toForm) b X +
        connection.adjointLocalConnectionBracketTerm chart
          (AdjointBundle.DifferentialForm.toSection form.toForm) b X := by
  exact data.toCovariantDerivativeData.covariantExteriorDerivativeZero_eq_d_add_bracket
    form.toForm form.smooth chart chart_mem hb (fun _ => X)

end

end YangMills.Geometry.AdjointBundleSmoothCovariantExteriorDerivativeZero.Probes
