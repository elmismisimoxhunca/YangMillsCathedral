/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleDifferentialFormBaseCoordinates

/-!
# Hostile probes for adjoint-form base coordinates
-/

namespace YangMills.Geometry.AdjointBundleDifferentialFormBaseCoordinates.Probes

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

omit [IsTopologicalGroup G] [IsManifold IB ∞ B] in
/-- The exact overlap cannot be vacuous at a charted base point. -/
theorem exact_center_in_domain
    (chart : PrincipalBundleLocalTrivialization torsor) {b : B}
    (hb : b ∈ chart.baseSet) :
    (extChartAt IB b) b ∈
      AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b :=
  AdjointBundle.DifferentialForm.center_mem_baseExtChartDomain chart hb

omit [IsManifold IB ∞ B] in
/-- Coordinates retain the quotient-derived fiber value and exact corner-aware tangent transport. -/
theorem exact_base_coordinate_evaluation
    {k : ℕ}
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B)
    (x : EB) (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)
    (vectors : Fin k → EB) :
    form.inBaseExtChartAt chart b x vectors =
      AdjointBundle.fiberModelEquiv (I := IG) bundle chart hx.2
        (form ((extChartAt IB b).symm x) (fun i =>
          mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
            (Set.range ⇑IB) x (vectors i))) :=
  AdjointBundle.DifferentialForm.inBaseExtChartAt_apply form chart b x hx vectors

omit [IsManifold IB ∞ B] in
/-- A substituted base-coordinate value is rejected. -/
theorem mismatched_base_coordinate_blocked
    {k : ℕ}
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B)
    (x : EB) (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)
    (vectors : Fin k → EB)
    (wrong : form.inBaseExtChartAt chart b x vectors ≠
      AdjointBundle.fiberModelEquiv (I := IG) bundle chart hx.2
        (form ((extChartAt IB b).symm x) (fun i =>
          mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
            (Set.range ⇑IB) x (vectors i)))) : False :=
  wrong (AdjointBundle.DifferentialForm.inBaseExtChartAt_apply
    form chart b x hx vectors)

omit [IsManifold IB ∞ B] in
/-- Outside the exact overlap, totalization is provably zero. -/
theorem exact_outside_domain_zero
    {k : ℕ}
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B)
    (x : EB)
    (hx : x ∉ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b) :
    form.inBaseExtChartAt chart b x = 0 :=
  AdjointBundle.DifferentialForm.inBaseExtChartAt_of_not_mem form chart b x hx

omit [IsManifold IB ∞ B] in
/-- In-domain nonzero quotient coordinates are not erased by outside-domain totalization. -/
theorem nonzero_base_coordinate_not_erased
    {k : ℕ}
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B)
    (x : EB) (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)
    (vectors : Fin k → EB)
    (nonzero : AdjointBundle.fiberModelEquiv (I := IG) bundle chart hx.2
      (form ((extChartAt IB b).symm x) (fun i =>
        mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
          (Set.range ⇑IB) x (vectors i))) ≠ 0) :
    form.inBaseExtChartAt chart b x vectors ≠ 0 := by
  rw [AdjointBundle.DifferentialForm.inBaseExtChartAt_apply form chart b x hx vectors]
  exact nonzero

omit [IsManifold IB ∞ B] in
/-- Replacing the exact range-within tangent transport by any different proposed value is blocked. -/
theorem wrong_tangent_transport_blocked
    {k : ℕ}
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k)
    (chart : PrincipalBundleLocalTrivialization torsor) (b : B)
    (x : EB) (hx : x ∈ AdjointBundle.DifferentialForm.baseExtChartDomain (IB := IB) chart b)
    (vectors : Fin k → EB) (proposed : EG)
    (changed : proposed ≠ AdjointBundle.fiberModelEquiv (I := IG) bundle chart hx.2
      (form ((extChartAt IB b).symm x) (fun i =>
        mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
          (Set.range ⇑IB) x (vectors i))))
    (claims_exact : proposed = form.inBaseExtChartAt chart b x vectors) : False := by
  apply changed
  rw [claims_exact]
  exact AdjointBundle.DifferentialForm.inBaseExtChartAt_apply form chart b x hx vectors

end

end YangMills.Geometry.AdjointBundleDifferentialFormBaseCoordinates.Probes
