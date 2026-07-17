/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleSmoothDifferentialForm

/-!
# Hostile probes for smooth adjoint-bundle-valued differential forms
-/

namespace YangMills.Geometry.Probes

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
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)

omit [IsManifold IB ∞ B] in
/-- Totalized evaluation cannot disagree with the exact quotient-derived coordinate on a chart's
base set. -/
theorem replacement_adjointBundle_smoothFormCoordinate_blocked
    {k : ℕ} (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (fields : Fin k → (b : B) → TangentSpace IB b)
    {b : B} (hb : b ∈ chart.baseSet)
    (mismatch :
      AdjointBundle.DifferentialForm.coordinateEvaluation form chart fields b ≠
        AdjointBundle.DifferentialForm.inCoordinates form chart hb
          (fun i => fields i b)) : False :=
  mismatch
    (AdjointBundle.DifferentialForm.coordinateEvaluation_eq_inCoordinates
      form chart fields hb)

/-- Smoothness cannot omit any designated atlas chart or disconnect from evaluated exact
coordinates. -/
theorem nonsmooth_adjointBundle_designatedFormCoordinate_blocked
    {k : ℕ} (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k)
    (hs : AdjointBundle.DifferentialForm.IsSmooth smoothBundle form)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (s : Set B) (fields : Fin k → (b : B) → TangentSpace IB b)
    (hs_chart : s ⊆ chart.baseSet)
    (fields_smooth : ∀ i, ContMDiffOn IB (IB.prod 𝓘(ℝ, EB)) ∞
      (fun b => (⟨b, fields i b⟩ : TangentBundle IB B)) s)
    (failure : ¬ContMDiffOn IB 𝓘(ℝ, EG) ∞
      (AdjointBundle.DifferentialForm.coordinateEvaluation form chart fields) s) : False :=
  failure (hs chart chart_mem s fields hs_chart fields_smooth)

/-- The exact pointwise carrier of the bundled smooth zero form cannot be replaced. -/
theorem replacement_adjointBundle_smoothZeroCarrier_blocked
    (k : ℕ)
    (mismatch :
      (AdjointBundle.DifferentialForm.Smooth.zero smoothBundle k).toForm ≠
        AdjointBundle.DifferentialForm.zero (IG := IG) (IB := IB) bundle k) : False :=
  mismatch (AdjointBundle.DifferentialForm.Smooth.zero_toForm smoothBundle k)

/-- The named zero varying-fiber form cannot fail the exact local smoothness predicate. -/
theorem nonsmooth_adjointBundle_zeroDifferentialForm_blocked
    (k : ℕ)
    (failure :
      ¬AdjointBundle.DifferentialForm.IsSmooth smoothBundle
        (AdjointBundle.DifferentialForm.zero (IG := IG) (IB := IB) bundle k)) : False :=
  failure (AdjointBundle.DifferentialForm.Smooth.zero smoothBundle k).smooth

end

end YangMills.Geometry.Probes
