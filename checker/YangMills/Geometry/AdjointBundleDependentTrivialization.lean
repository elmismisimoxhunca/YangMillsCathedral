/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleFiberLinearity

/-!
# Dependent adjoint-fiber topologies and trivializations

This file equips each dependent fiber with the named topology pulled back through its selected model
coordinate. It also transports every established quotient trivialization across the exact
base-preserving total-space homeomorphism, obtaining genuine Mathlib bundle trivializations on the
dependent total space without regenerating or replacing its topology.

The structures remain named data. No global topology, `FiberBundle`, or `VectorBundle` instance is
installed here.
-/

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff Bundle Topology

universe uE uH uG uB uP

noncomputable section

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]
    {torsor : PrincipalBundleTorsorData G B P}
    (bundle : TopologicalPrincipalBundleData torsor)

/-- Named topology on a dependent fiber, induced by its selected exact model coordinate. -/
@[reducible]
def AdjointBundle.fiberTopology (b : B) :
    TopologicalSpace (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
  TopologicalSpace.induced
    (AdjointBundle.selectedFiberModelEquiv (I := I) bundle b) inferInstance

/-- The selected fiber coordinate is a homeomorphism for the named induced fiber topology. -/
def AdjointBundle.selectedFiberModelHomeomorph (b : B) :
    @Homeomorph (AdjointBundle.Fiber (I := I) (torsor := torsor) b) E
      (AdjointBundle.fiberTopology (I := I) bundle b) inferInstance := by
  letI : TopologicalSpace (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := I) bundle b
  exact (AdjointBundle.selectedFiberModelEquiv (I := I) bundle b).toHomeomorphOfIsInducing
    (Topology.IsInducing.induced _)

/-- An established quotient trivialization transported, with unchanged local coordinate, across the
base-preserving dependent-total-space homeomorphism. -/
def AdjointBundle.dependentModelBundleTrivialization
    (chart : PrincipalBundleLocalTrivialization torsor) :
    @Bundle.Trivialization B E
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor)))
      inferInstance inferInstance
      (AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor))
      (@Bundle.TotalSpace.proj B E
        (AdjointBundle.Fiber (I := I) (torsor := torsor))) := by
  letI : TopologicalSpace
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
  let h := AdjointBundle.dependentTotalSpaceHomeomorphQuotient
    (I := I) (torsor := torsor)
  let raw := (AdjointBundle.modelBundleTrivialization (I := I) bundle chart).compHomeomorph h
  exact
    { toOpenPartialHomeomorph := raw.toOpenPartialHomeomorph
      baseSet := raw.baseSet
      open_baseSet := raw.open_baseSet
      source_eq := by
        rw [raw.source_eq]
        ext z
        simp only [Set.mem_preimage, Function.comp_apply]
        rw [AdjointBundle.projection_dependentTotalSpaceHomeomorphQuotient
          (I := I) (torsor := torsor) z]
      target_eq := raw.target_eq
      proj_toFun := by
        intro z hz
        rw [raw.proj_toFun z hz]
        exact AdjointBundle.projection_dependentTotalSpaceHomeomorphQuotient
          (I := I) (torsor := torsor) z }

/-- The transported dependent trivialization has exactly the original quotient-derived forward
coordinate after forgetting the dependent package. -/
@[simp]
theorem AdjointBundle.dependentModelBundleTrivialization_apply
    (chart : PrincipalBundleLocalTrivialization torsor)
    (z : Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :
    AdjointBundle.dependentModelBundleTrivialization (I := I) bundle chart z =
      AdjointBundle.modelBundleTrivialization (I := I) bundle chart
        (AdjointBundle.totalSpaceToQuotient (I := I) (torsor := torsor) z) :=
  rfl

/-- Its inverse is exact quotient packaging after the original quotient trivialization inverse. -/
@[simp]
theorem AdjointBundle.dependentModelBundleTrivialization_symm_apply
    (chart : PrincipalBundleLocalTrivialization torsor) (z : B × E) :
    letI : TopologicalSpace
        (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
      AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
    (AdjointBundle.dependentModelBundleTrivialization
      (I := I) bundle chart).toOpenPartialHomeomorph.symm z =
      AdjointBundle.quotientToTotalSpace (I := I) (torsor := torsor)
        ((AdjointBundle.modelBundleTrivialization
          (I := I) bundle chart).toOpenPartialHomeomorph.symm z) :=
  rfl

/-- The dependent trivialization retains exactly the principal chart's base set. -/
@[simp]
theorem AdjointBundle.dependentModelBundleTrivialization_baseSet
    (chart : PrincipalBundleLocalTrivialization torsor) :
    letI : TopologicalSpace
        (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
      AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
    (AdjointBundle.dependentModelBundleTrivialization (I := I) bundle chart).baseSet =
      chart.baseSet :=
  rfl

end

end YangMills.Geometry
