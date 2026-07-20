/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleGaugeHomeomorph

/-!
# Hostile probes for topological adjoint-bundle gauge automorphisms
-/

namespace YangMills.Geometry.AdjointBundleGaugeHomeomorph.Probes

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
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

open SmoothGaugeTransformation

/-- Continuity descends through the exact quotient map. -/
theorem exact_quotient_action_continuity
    (gauge : SmoothGaugeTransformation smoothBundle) :
    Continuous gauge.inducedAdjointBundleAction :=
  gauge.inducedAdjointBundleAction_continuous

/-- The quotient homeomorphism retains the exact set-level action. -/
theorem exact_quotient_homeomorph_carrier
    (gauge : SmoothGaugeTransformation smoothBundle)
    (z : AdjointBundle (I := IG) torsor) :
    gauge.inducedAdjointBundleHomeomorph z = gauge.inducedAdjointBundleAction z := rfl

/-- The direct dependent action preserves the base exactly. -/
theorem exact_dependent_base
    (gauge : SmoothGaugeTransformation smoothBundle)
    (z : Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :
    (gauge.inducedAdjointDependentTotalSpaceAction z).proj = z.proj :=
  gauge.inducedAdjointDependentTotalSpaceAction_proj z

/-- Every fixed fiber restriction is exactly the continuous-linear action. -/
theorem exact_dependent_fiber_continuousLinear
    (gauge : SmoothGaugeTransformation smoothBundle) (b : B)
    (z : AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    (gauge.inducedAdjointDependentTotalSpaceAction ⟨b, z⟩).snd =
      gauge.inducedAdjointFiberContinuousLinearEquiv b z :=
  gauge.inducedAdjointDependentTotalSpaceAction_fiber b z

/-- The direct carrier is exactly conjugation through the quotient homeomorphism. -/
theorem exact_dependent_conjugation
    (gauge : SmoothGaugeTransformation smoothBundle)
    (z : Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :
    letI : TopologicalSpace
        (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
      AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
    gauge.inducedAdjointDependentTotalSpaceAction z =
      (AdjointBundle.dependentTotalSpaceHomeomorphQuotient
        (I := IG) (torsor := torsor)).symm
        (gauge.inducedAdjointBundleHomeomorph
          (AdjointBundle.dependentTotalSpaceHomeomorphQuotient
            (I := IG) (torsor := torsor) z)) :=
  gauge.inducedAdjointDependentTotalSpaceAction_eq_conjugate z

/-- The dependent homeomorphism retains the direct action carrier. -/
theorem exact_dependent_homeomorph_carrier
    (gauge : SmoothGaugeTransformation smoothBundle)
    (z : Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :
    letI : TopologicalSpace
        (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
      AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
    gauge.inducedAdjointDependentTotalSpaceHomeomorph z =
      gauge.inducedAdjointDependentTotalSpaceAction z :=
  gauge.inducedAdjointDependentTotalSpaceHomeomorph_apply z

/-- The dependent homeomorphism inverse is exactly the inverse-gauge action. -/
theorem exact_dependent_homeomorph_inverse
    (gauge : SmoothGaugeTransformation smoothBundle)
    (z : Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :
    letI : TopologicalSpace
        (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
      AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
    gauge.inducedAdjointDependentTotalSpaceHomeomorph.symm z =
      gauge⁻¹.inducedAdjointDependentTotalSpaceAction z :=
  gauge.inducedAdjointDependentTotalSpaceHomeomorph_symm_apply z

/-- A discontinuous quotient action contradicts the derived quotient topology. -/
theorem discontinuous_quotient_action_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (wrong : ¬ Continuous gauge.inducedAdjointBundleAction) : False :=
  wrong gauge.inducedAdjointBundleAction_continuous

/-- A disconnected dependent homeomorphism carrier is rejected. -/
theorem mismatched_dependent_homeomorph_carrier_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (z : Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)))
    (wrong :
      letI : TopologicalSpace
          (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
        AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
      gauge.inducedAdjointDependentTotalSpaceHomeomorph z ≠
        gauge.inducedAdjointDependentTotalSpaceAction z) : False :=
  wrong (gauge.inducedAdjointDependentTotalSpaceHomeomorph_apply z)

end

end YangMills.Geometry.AdjointBundleGaugeHomeomorph.Probes
