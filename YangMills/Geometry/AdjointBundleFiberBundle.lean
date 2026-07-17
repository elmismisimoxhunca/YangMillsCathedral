/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleDependentTrivialization
import Mathlib.Topology.FiberBundle.Basic

/-!
# A topology-coherent fiber bundle for the dependent adjoint bundle

The named quotient-induced total-space topology and selected-coordinate fiber topologies satisfy
Mathlib's fiber-inclusion coherence requirement. The transported dependent trivializations therefore
package into a named `FiberBundle` value without generating a replacement total-space topology.

No global instance, `VectorBundle`, or smooth-vector-bundle mixin is installed here.
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

/-- The inclusion of every dependent fiber is continuous for the named fiber and total-space
topologies. -/
theorem AdjointBundle.continuous_totalSpaceMk (b : B) :
    @Continuous
      (AdjointBundle.Fiber (I := I) (torsor := torsor) b)
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor)))
      (AdjointBundle.fiberTopology (I := I) bundle b)
      (AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor))
      (@Bundle.TotalSpace.mk B E
        (AdjointBundle.Fiber (I := I) (torsor := torsor)) b) := by
  letI : TopologicalSpace (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := I) bundle b
  letI : TopologicalSpace
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
  let quotientTriv := AdjointBundle.modelBundleTrivialization (I := I) bundle
    (bundle.trivializationAt b)
  let coordinate := AdjointBundle.selectedFiberModelEquiv (I := I) bundle b
  let pair : AdjointBundle.Fiber (I := I) (torsor := torsor) b → B × E :=
    fun z => (b, coordinate z)
  have pairContinuous : Continuous pair :=
    continuous_const.prodMk continuous_induced_dom
  have pairMaps : Set.MapsTo pair Set.univ quotientTriv.target := by
    intro z hz
    exact quotientTriv.mem_target.mpr (bundle.mem_baseSet_trivializationAt b)
  have inverseContinuous : Continuous
      (fun z => quotientTriv.toOpenPartialHomeomorph.symm (pair z)) :=
    quotientTriv.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      pairContinuous (fun z => pairMaps (Set.mem_univ z))
  have inverse_eq : (fun z => quotientTriv.toOpenPartialHomeomorph.symm (pair z)) =
      fun z : AdjointBundle.Fiber (I := I) (torsor := torsor) b => z.1 := by
    funext z
    exact congrArg Subtype.val
      ((AdjointBundle.selectedFiberModelEquiv (I := I) bundle b).symm_apply_apply z)
  apply (continuous_induced_rng
    (f := AdjointBundle.totalSpaceToQuotient (I := I) (torsor := torsor))
    (g := @Bundle.TotalSpace.mk B E
      (AdjointBundle.Fiber (I := I) (torsor := torsor)) b)).mpr
  change Continuous (fun z : AdjointBundle.Fiber (I := I) (torsor := torsor) b => z.1)
  rw [← inverse_eq]
  exact inverseContinuous

/-- The inclusion of every dependent fiber induces exactly its selected-coordinate topology from the
preserved quotient-induced total-space topology. -/
theorem AdjointBundle.isInducing_totalSpaceMk (b : B) :
    letI : TopologicalSpace (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := I) bundle b
    letI : TopologicalSpace
        (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
      AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
    Topology.IsInducing (@Bundle.TotalSpace.mk B E
      (AdjointBundle.Fiber (I := I) (torsor := torsor)) b) := by
  letI : TopologicalSpace (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := I) bundle b
  letI : TopologicalSpace
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
  let e := AdjointBundle.dependentModelBundleTrivialization (I := I) bundle
    (bundle.trivializationAt b)
  let coordinate := AdjointBundle.selectedFiberModelEquiv (I := I) bundle b
  let pair : AdjointBundle.Fiber (I := I) (torsor := torsor) b → B × E :=
    fun z => (b, coordinate z)
  have pairContinuous : Continuous pair :=
    continuous_const.prodMk continuous_induced_dom
  have pairInducing : Topology.IsInducing pair := by
    apply Topology.IsInducing.of_comp pairContinuous continuous_snd
    simpa [pair, Function.comp_def] using
      (Topology.IsInducing.induced coordinate)
  have mkMaps : ∀ z : AdjointBundle.Fiber (I := I) (torsor := torsor) b,
      Bundle.TotalSpace.mk b z ∈ e.source := by
    intro z
    exact e.mem_source.mpr (bundle.mem_baseSet_trivializationAt b)
  have comp_eq : e ∘ (@Bundle.TotalSpace.mk B E
      (AdjointBundle.Fiber (I := I) (torsor := torsor)) b) = pair := by
    funext z
    apply Prod.ext
    · exact e.coe_fst' (bundle.mem_baseSet_trivializationAt b)
    · rfl
  have compInducing : Topology.IsInducing (e ∘ (@Bundle.TotalSpace.mk B E
      (AdjointBundle.Fiber (I := I) (torsor := torsor)) b)) := by
    rw [comp_eq]
    exact pairInducing
  have targetMaps : ∀ z, (e ∘ (@Bundle.TotalSpace.mk B E
      (AdjointBundle.Fiber (I := I) (torsor := torsor)) b)) z ∈ e.target := fun z =>
    e.toOpenPartialHomeomorph.map_source (mkMaps z)
  have compTargetInducing : Topology.IsInducing
      (Set.codRestrict (e ∘ (@Bundle.TotalSpace.mk B E
        (AdjointBundle.Fiber (I := I) (torsor := torsor)) b)) e.target targetMaps) :=
    compInducing.codRestrict targetMaps
  let restrictedMk := Set.codRestrict
    (@Bundle.TotalSpace.mk B E
      (AdjointBundle.Fiber (I := I) (torsor := torsor)) b) e.source mkMaps
  let chartHomeomorph := e.toOpenPartialHomeomorph.toHomeomorphSourceTarget
  have factorization : chartHomeomorph ∘ restrictedMk =
      Set.codRestrict (e ∘ (@Bundle.TotalSpace.mk B E
        (AdjointBundle.Fiber (I := I) (torsor := torsor)) b)) e.target targetMaps := by
    rfl
  have restrictedMkInducing : Topology.IsInducing restrictedMk :=
    chartHomeomorph.isInducing.of_comp_iff.mp (factorization ▸ compTargetInducing)
  exact Topology.IsInducing.of_codRestrict mkMaps restrictedMkInducing

/-- Named Mathlib fiber-bundle structure using the preserved topology and transported atlas. -/
@[reducible]
def AdjointBundle.dependentFiberBundle :
    @FiberBundle B E inferInstance inferInstance
      (AdjointBundle.Fiber (I := I) (torsor := torsor))
      (AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor))
      (fun b => AdjointBundle.fiberTopology (I := I) bundle b) := by
  letI : TopologicalSpace
      (Bundle.TotalSpace E (AdjointBundle.Fiber (I := I) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := I) (torsor := torsor)
  letI (b : B) : TopologicalSpace
      (AdjointBundle.Fiber (I := I) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := I) bundle b
  exact
    { totalSpaceMk_isInducing' :=
        AdjointBundle.isInducing_totalSpaceMk (I := I) bundle
      trivializationAtlas' := {e | ∃ chart ∈ bundle.trivializationAtlas,
        e = AdjointBundle.dependentModelBundleTrivialization (I := I) bundle chart}
      trivializationAt' := fun b =>
        AdjointBundle.dependentModelBundleTrivialization (I := I) bundle
          (bundle.trivializationAt b)
      mem_baseSet_trivializationAt' := bundle.mem_baseSet_trivializationAt
      trivialization_mem_atlas' := fun b =>
        ⟨bundle.trivializationAt b, bundle.trivializationAt_mem_atlas b, rfl⟩ }

end

end YangMills.Geometry
