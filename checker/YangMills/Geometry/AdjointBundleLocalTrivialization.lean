/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleLocalCoordinates
import YangMills.Mathematics.LieGroupAdjointRegularity

/-!
# Topological local trivializations of the adjoint bundle

The compact certificate-parameterized construction records the exact dependency on continuity of
the derivative-defined adjoint action. The generally derived canonical certificate then gives every
designated principal-bundle chart an open partial homeomorphism between the adjoint quotient over
its base set and `baseSet × g`, without model-supplied regularity data.

This closes the topological local-triviality layer only. It does not supply smooth vector-bundle
charts, sections, descended curvature, or fields.
-/

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff

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
    {bundle : TopologicalPrincipalBundleData torsor}
    (chart : PrincipalBundleLocalTrivialization torsor)

/-- Natural source of the associated local trivialization. -/
def AdjointBundle.localSource : Set (AdjointBundle (I := I) torsor) :=
  AdjointBundle.projection torsor ⁻¹' chart.baseSet

/-- Natural target of the associated local trivialization. -/
def AdjointBundle.localTarget : Set (B × GroupLieAlgebra I G) :=
  chart.baseSet ×ˢ (Set.univ : Set (GroupLieAlgebra I G))

/-- The associated local source is open. -/
theorem AdjointBundle.isOpen_localSource
    (bundle : TopologicalPrincipalBundleData torsor) :
    IsOpen (AdjointBundle.localSource (I := I) chart) :=
  chart.isOpen_baseSet.preimage (AdjointBundle.projection_continuous (I := I) bundle)

omit [IsTopologicalGroup G] [LieGroup I ∞ G] in
/-- The associated local target is open. -/
theorem AdjointBundle.isOpen_localTarget :
    IsOpen (AdjointBundle.localTarget (I := I) chart) :=
  chart.isOpen_baseSet.prod isOpen_univ

omit [IsTopologicalGroup G] in
/-- Local coordinates carry their natural source into their natural target. -/
theorem AdjointBundle.localCoordinate_mapsTo :
    Set.MapsTo (AdjointBundle.localCoordinate (I := I) chart)
      (AdjointBundle.localSource (I := I) chart)
      (AdjointBundle.localTarget (I := I) chart) := by
  intro z hz
  constructor
  · rw [AdjointBundle.localCoordinate_fst chart z hz]
    exact hz
  · exact Set.mem_univ _

omit [IsTopologicalGroup G] in
/-- The inverse local-coordinate map carries the natural target into the natural source. -/
theorem AdjointBundle.localCoordinateInverse_mapsTo :
    Set.MapsTo (AdjointBundle.localCoordinateInverse (I := I) chart)
      (AdjointBundle.localTarget (I := I) chart)
      (AdjointBundle.localSource (I := I) chart) := by
  intro z hz
  let p₀ : P := chart.toPartialHomeomorph.symm (z.1, (1 : G))
  have targetMem : (z.1, (1 : G)) ∈ chart.toPartialHomeomorph.target := by
    rw [chart.target_eq]
    exact ⟨hz.1, Set.mem_univ _⟩
  have p₀Mem : p₀ ∈ chart.toPartialHomeomorph.source :=
    chart.toPartialHomeomorph.map_target targetMem
  have chartP₀ : chart p₀ = (z.1, (1 : G)) :=
    chart.toPartialHomeomorph.right_inv targetMem
  have baseP₀ := chart.base_coordinate p₀ p₀Mem
  rw [chartP₀] at baseP₀
  change torsor.projection p₀ ∈ chart.baseSet
  rw [← baseP₀]
  exact hz.1

omit [IsTopologicalGroup G] in
/-- On the chart source, the representative coordinate is continuous whenever the intrinsic
parameter-dependent adjoint map has the explicitly isolated continuity certificate. -/
theorem adjointBundleChartRepresentative_continuousOn
    (adjointRegularity : YangMills.Mathematics.ContinuousLieGroupAdjointData
      (I := I) (G := G)) :
    ContinuousOn (adjointBundleChartRepresentative (I := I) chart)
      (Prod.fst ⁻¹' chart.toPartialHomeomorph.source) := by
  let source : Set (P × GroupLieAlgebra I G) :=
    Prod.fst ⁻¹' chart.toPartialHomeomorph.source
  have chartContinuous : ContinuousOn (fun z : P × GroupLieAlgebra I G => chart z.1) source :=
    chart.toPartialHomeomorph.continuousOn.comp continuous_fst.continuousOn
      (by intro z hz; exact hz)
  have baseContinuous : ContinuousOn
      (fun z : P × GroupLieAlgebra I G => torsor.projection z.1) source := by
    exact chartContinuous.fst.congr (by
      intro z hz
      exact (chart.base_coordinate z.1 hz).symm)
  have actionInputContinuous : ContinuousOn
      (fun z : P × GroupLieAlgebra I G => ((chart z.1).2, z.2)) source :=
    chartContinuous.snd.prodMk continuous_snd.continuousOn
  have fiberContinuous : ContinuousOn
      (fun z : P × GroupLieAlgebra I G =>
        YangMills.Mathematics.lieGroupAdjoint I (chart z.1).2 z.2) source :=
    adjointRegularity.action_continuous.continuousOn.comp actionInputContinuous
      (Set.mapsTo_univ _ _)
  exact (baseContinuous.prodMk fiberContinuous).congr (by
    intro z hz
    change z.1 ∈ chart.toPartialHomeomorph.source at hz
    simp [adjointBundleChartRepresentative, hz])

/-- The quotient local-coordinate map is continuous on its open source. -/
theorem AdjointBundle.localCoordinate_continuousOn
    (bundle : TopologicalPrincipalBundleData torsor)
    (adjointRegularity : YangMills.Mathematics.ContinuousLieGroupAdjointData
      (I := I) (G := G)) :
    ContinuousOn (AdjointBundle.localCoordinate (I := I) chart)
      (AdjointBundle.localSource (I := I) chart) := by
  rw [(AdjointBundle.mk_isQuotientMap (I := I) (torsor := torsor)).continuousOn_isOpen_iff
    (AdjointBundle.isOpen_localSource (I := I) chart bundle)]
  have preimage_eq :
      (fun z : P × GroupLieAlgebra I G => AdjointBundle.mk torsor z.1 z.2) ⁻¹'
          AdjointBundle.localSource (I := I) chart =
        Prod.fst ⁻¹' chart.toPartialHomeomorph.source := by
    ext z
    simp only [AdjointBundle.localSource, Set.mem_preimage]
    rw [AdjointBundle.projection_mk, chart.source_eq]
    rfl
  rw [preimage_eq]
  simpa [Function.comp_def, AdjointBundle.localCoordinate, AdjointBundle.mk] using
    (adjointBundleChartRepresentative_continuousOn (I := I) chart adjointRegularity)

omit [IsTopologicalGroup G] in
/-- The inverse local-coordinate map is continuous on its open target. -/
theorem AdjointBundle.localCoordinateInverse_continuousOn :
    ContinuousOn (AdjointBundle.localCoordinateInverse (I := I) chart)
      (AdjointBundle.localTarget (I := I) chart) := by
  let target := AdjointBundle.localTarget (I := I) chart
  have unitInput : ContinuousOn
      (fun z : B × GroupLieAlgebra I G => (z.1, (1 : G))) target :=
    continuous_fst.continuousOn.prodMk continuous_const.continuousOn
  have unitInputMaps : Set.MapsTo
      (fun z : B × GroupLieAlgebra I G => (z.1, (1 : G))) target
      chart.toPartialHomeomorph.target := by
    intro z hz
    rw [chart.target_eq]
    exact ⟨hz.1, Set.mem_univ _⟩
  have principalInverse : ContinuousOn
      (fun z : B × GroupLieAlgebra I G =>
        chart.toPartialHomeomorph.symm (z.1, (1 : G))) target :=
    chart.toPartialHomeomorph.continuousOn_symm.comp unitInput unitInputMaps
  have representative : ContinuousOn
      (fun z : B × GroupLieAlgebra I G =>
        (chart.toPartialHomeomorph.symm (z.1, (1 : G)), z.2)) target :=
    principalInverse.prodMk continuous_snd.continuousOn
  exact AdjointBundle.mk_continuous (I := I) (torsor := torsor) |>.continuousOn.comp
    representative (Set.mapsTo_univ _ _)

/-- Open partial homeomorphism induced from one principal-bundle chart. -/
def AdjointBundle.localTrivialization
    (bundle : TopologicalPrincipalBundleData torsor)
    (adjointRegularity : YangMills.Mathematics.ContinuousLieGroupAdjointData
      (I := I) (G := G)) :
    OpenPartialHomeomorph (AdjointBundle (I := I) torsor)
      (B × GroupLieAlgebra I G) where
  toPartialEquiv := {
    toFun := AdjointBundle.localCoordinate (I := I) chart
    invFun := AdjointBundle.localCoordinateInverse (I := I) chart
    source := AdjointBundle.localSource (I := I) chart
    target := AdjointBundle.localTarget (I := I) chart
    map_source' := AdjointBundle.localCoordinate_mapsTo chart
    map_target' := AdjointBundle.localCoordinateInverse_mapsTo chart
    left_inv' := fun z hz =>
      AdjointBundle.localCoordinateInverse_localCoordinate chart z hz
    right_inv' := fun z hz =>
      AdjointBundle.localCoordinate_localCoordinateInverse chart z hz.1
  }
  open_source := AdjointBundle.isOpen_localSource chart bundle
  open_target := AdjointBundle.isOpen_localTarget chart
  continuousOn_toFun := AdjointBundle.localCoordinate_continuousOn chart bundle adjointRegularity
  continuousOn_invFun := AdjointBundle.localCoordinateInverse_continuousOn chart

/-- Canonical topological local trivialization using the generally derived smooth adjoint
regularity. No regularity witness is required from a proposed model. -/
def AdjointBundle.canonicalLocalTrivialization
    (bundle : TopologicalPrincipalBundleData torsor) :
    OpenPartialHomeomorph (AdjointBundle (I := I) torsor)
      (B × GroupLieAlgebra I G) :=
  AdjointBundle.localTrivialization (I := I) chart bundle
    (YangMills.Mathematics.continuousLieGroupAdjointData (I := I) (G := G))

end

end YangMills.Geometry
