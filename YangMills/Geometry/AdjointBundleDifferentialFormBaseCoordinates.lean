/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleSmoothDifferentialForm
import YangMills.Mathematics.ManifoldDifferentialFormNormedCoordinates

/-!
# Base extended-chart coordinates of adjoint-bundle-valued forms

An adjoint-bundle-valued form has varying quotient fibers. This module converts it, on the exact
overlap of a base extended chart and a designated principal chart, into a fixed-model normed-space
differential form. Inverse-chart tangent transport remains corner-aware through
`mfderivWithin ... (Set.range IB)`.

The carrier is totalized by zero outside the overlap only to obtain a function on the model space;
all geometric statements retain the explicit overlap hypothesis. This is coordinate infrastructure,
not yet a positive-degree covariant exterior derivative.
-/

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff Bundle Topology
open YangMills.Mathematics

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

namespace AdjointBundle.DifferentialForm

/-- Exact overlap where the base inverse extended chart and designated adjoint fiber coordinates both
have geometric meaning. -/
def baseExtChartDomain
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B) : Set EB :=
  (extChartAt IB b).target ∩ {x | (extChartAt IB b).symm x ∈ chart.baseSet}

omit [IsTopologicalGroup G] [IsManifold IB ∞ B] in
/-- The base-chart center lies in the overlap whenever the designated principal chart contains it. -/
theorem center_mem_baseExtChartDomain
    (chart : PrincipalBundleLocalTrivialization torsor) {b : B}
    (hb : b ∈ chart.baseSet) :
    (extChartAt IB b) b ∈ baseExtChartDomain (IB := IB) chart b := by
  refine ⟨mem_extChartAt_target b, ?_⟩
  simpa only [Set.mem_setOf_eq, extChartAt_to_inv] using hb

/-- Fixed-model coordinates of a varying-fiber form in a principal chart and a base inverse extended
chart. Outside their exact overlap the carrier is totalized by zero. -/
noncomputable def inBaseExtChartAt
    {k : ℕ}
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B) :
    NormedSpaceDifferentialForm EB EG k := fun x => by
  classical
  let q := (extChartAt IB b).symm x
  if hx : x ∈ baseExtChartDomain (IB := IB) chart b then
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) q) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle q
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) q) :=
      AdjointBundle.fiberModule (I := IG) bundle q
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) q) :=
      AdjointBundle.fiberTopology (I := IG) bundle q
    exact (AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hx.2)
      |>.toContinuousLinearMap.compContinuousAlternatingMap
        ((form q).compContinuousLinearMap
          (mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
            (Set.range ⇑IB) x))
  else exact 0

omit [IsManifold IB ∞ B] in
/-- Exact evaluation on the meaningful overlap, retaining quotient-derived fiber coordinates and
corner-aware inverse-chart tangent transport. -/
@[simp] theorem inBaseExtChartAt_apply
    {k : ℕ}
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B)
    (x : EB) (hx : x ∈ baseExtChartDomain (IB := IB) chart b)
    (vectors : Fin k → EB) :
    form.inBaseExtChartAt chart b x vectors =
      AdjointBundle.fiberModelEquiv (I := IG) bundle chart hx.2
        (form ((extChartAt IB b).symm x) (fun i =>
          mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
            (Set.range ⇑IB) x (vectors i))) := by
  classical
  simp only [inBaseExtChartAt, dif_pos hx]
  rfl

omit [IsManifold IB ∞ B] in
/-- The totalized carrier is exactly zero outside the declared coordinate overlap. -/
@[simp] theorem inBaseExtChartAt_of_not_mem
    {k : ℕ}
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B)
    (x : EB) (hx : x ∉ baseExtChartDomain (IB := IB) chart b) :
    form.inBaseExtChartAt chart b x = 0 := by
  simp [inBaseExtChartAt, hx]

omit [IsManifold IB ∞ B] in
/-- On the exact overlap, base coordinates of the intrinsic zero form are zero. -/
theorem inBaseExtChartAt_zero
    (k : ℕ) (chart : PrincipalBundleLocalTrivialization torsor) (b : B) :
    Set.EqOn
      ((AdjointBundle.DifferentialForm.zero (IG := IG) (IB := IB) bundle k)
        |>.inBaseExtChartAt chart b)
      0 (baseExtChartDomain (IB := IB) chart b) := by
  intro x hx
  let q := (extChartAt IB b).symm x
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) q) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle q
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) q) :=
    AdjointBundle.fiberModule (I := IG) bundle q
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) q) :=
    AdjointBundle.fiberTopology (I := IG) bundle q
  apply ContinuousAlternatingMap.ext
  intro vectors
  rw [inBaseExtChartAt_apply _ chart b x hx vectors]
  rw [AdjointBundle.DifferentialForm.zero_apply]
  rw [← AdjointBundle.fiberModelContinuousLinearEquiv_apply]
  exact map_zero (AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hx.2)

end AdjointBundle.DifferentialForm

end
end YangMills.Geometry
