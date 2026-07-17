/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleTopology

/-!
# Local coordinates for the adjoint bundle

A principal-bundle chart with group coordinate `k` sends an adjoint-bundle representative `(p,X)`
to `(π(p), Ad(k)X)`. The inverse over the chart base sends `(b,X)` to the class of
`(chart⁻¹(b,1),X)`. This file proves these formulas are independent of representative and mutually
inverse on their natural base domains.

Only set-level local-coordinate laws are packaged here. Continuity, local homeomorphisms, smoothness,
and vector-bundle structure remain separate obligations.
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
    (chart : PrincipalBundleLocalTrivialization torsor)

/-- Representative-level local coordinate, extended by zero outside the chart source solely so it
can be quotiented as a total function. -/
def adjointBundleChartRepresentative (z : P × GroupLieAlgebra I G) :
    B × GroupLieAlgebra I G := by
  classical
  exact if z.1 ∈ chart.toPartialHomeomorph.source then
    (torsor.projection z.1,
      YangMills.Mathematics.lieGroupAdjoint I (chart z.1).2 z.2)
  else
    (torsor.projection z.1, 0)

omit [IsTopologicalGroup G] in
/-- The representative coordinate is constant on every defining diagonal orbit. -/
theorem adjointBundleChartRepresentative_invariant
    {x y : P × GroupLieAlgebra I G}
    (related : adjointBundleOrbitRelation torsor x y) :
    adjointBundleChartRepresentative (I := I) chart x =
      adjointBundleChartRepresentative (I := I) chart y := by
  obtain ⟨g, rfl⟩ := related
  by_cases hx : x.1 ∈ chart.toPartialHomeomorph.source
  · have hacted : torsor.rightAction x.1 g ∈ chart.toPartialHomeomorph.source :=
      chart.rightAction_mem_source hx g
    simp only [adjointBundleChartRepresentative, hx, hacted, if_true,
      adjointBundleRightAction]
    apply Prod.ext
    · exact (torsor.projection_rightAction x.1 g).symm
    · have coordinate := chart.rightAction_coordinate x.1 hx g
      have secondCoordinate := congrArg Prod.snd coordinate
      rw [secondCoordinate, YangMills.Mathematics.lieGroupAdjoint_mul]
      simp only [ContinuousLinearMap.comp_apply]
      rw [YangMills.Mathematics.lieGroupAdjoint_apply_inv]
  · have hacted : torsor.rightAction x.1 g ∉ chart.toPartialHomeomorph.source := by
      intro hsource
      have back := chart.rightAction_mem_source hsource g⁻¹
      rw [torsor.right_mul] at back
      exact hx (by simpa [torsor.right_one] using back)
    simp [adjointBundleChartRepresentative, hx, hacted, adjointBundleRightAction,
      torsor.projection_rightAction]

/-- Well-defined local-coordinate map on the adjoint quotient. -/
def AdjointBundle.localCoordinate : AdjointBundle (I := I) torsor →
    B × GroupLieAlgebra I G :=
  Quotient.lift (adjointBundleChartRepresentative (I := I) chart)
    (fun _ _ related => adjointBundleChartRepresentative_invariant (I := I) chart related)

omit [IsTopologicalGroup G] in
/-- On a representative lying over the chart base, the quotient coordinate has the expected
`Ad(k)` formula. -/
theorem AdjointBundle.localCoordinate_mk
    (p : P) (X : GroupLieAlgebra I G)
    (hp : p ∈ chart.toPartialHomeomorph.source) :
    AdjointBundle.localCoordinate (I := I) chart (AdjointBundle.mk torsor p X) =
      (torsor.projection p,
        YangMills.Mathematics.lieGroupAdjoint I (chart p).2 X) := by
  simp [AdjointBundle.localCoordinate, AdjointBundle.mk,
    adjointBundleChartRepresentative, hp]

/-- Inverse local-coordinate representative based at group coordinate `1`. -/
def AdjointBundle.localCoordinateInverse (z : B × GroupLieAlgebra I G) :
    AdjointBundle (I := I) torsor :=
  AdjointBundle.mk torsor
    (chart.toPartialHomeomorph.symm (z.1, 1)) z.2

omit [IsTopologicalGroup G] in
/-- The local coordinate map preserves the associated-bundle base on its natural source. -/
theorem AdjointBundle.localCoordinate_fst
    (z : AdjointBundle (I := I) torsor)
    (hz : AdjointBundle.projection torsor z ∈ chart.baseSet) :
    (AdjointBundle.localCoordinate (I := I) chart z).1 =
      AdjointBundle.projection torsor z := by
  induction z using Quotient.inductionOn with
  | _ representative =>
      rcases representative with ⟨p, X⟩
      have hp : p ∈ chart.toPartialHomeomorph.source := by
        rw [chart.source_eq]
        exact hz
      change (AdjointBundle.localCoordinate (I := I) chart
        (AdjointBundle.mk torsor p X)).1 =
          AdjointBundle.projection torsor (AdjointBundle.mk torsor p X)
      rw [AdjointBundle.localCoordinate_mk chart p X hp]
      rfl

omit [IsTopologicalGroup G] in
/-- Local coordinates followed by the inverse recover the same adjoint-bundle class. -/
theorem AdjointBundle.localCoordinateInverse_localCoordinate
    (z : AdjointBundle (I := I) torsor)
    (hz : AdjointBundle.projection torsor z ∈ chart.baseSet) :
    AdjointBundle.localCoordinateInverse (I := I) chart
        (AdjointBundle.localCoordinate (I := I) chart z) = z := by
  induction z using Quotient.inductionOn with
  | _ representative =>
      rcases representative with ⟨p, X⟩
      have hp : p ∈ chart.toPartialHomeomorph.source := by
        rw [chart.source_eq]
        exact hz
      change AdjointBundle.localCoordinateInverse (I := I) chart
        (AdjointBundle.localCoordinate (I := I) chart
          (AdjointBundle.mk torsor p X)) = AdjointBundle.mk torsor p X
      rw [AdjointBundle.localCoordinate_mk chart p X hp]
      let k : G := (chart p).2
      let p₀ : P := chart.toPartialHomeomorph.symm (torsor.projection p, 1)
      have target_mem : (torsor.projection p, 1) ∈ chart.toPartialHomeomorph.target := by
        rw [chart.target_eq]
        exact ⟨hz, Set.mem_univ _⟩
      have p₀_mem : p₀ ∈ chart.toPartialHomeomorph.source :=
        chart.toPartialHomeomorph.map_target target_mem
      have chart_p₀ : chart p₀ = (torsor.projection p, 1) := by
        exact chart.toPartialHomeomorph.right_inv target_mem
      have acted_mem := chart.rightAction_mem_source p₀_mem k
      have chart_acted := chart.rightAction_coordinate p₀ p₀_mem k
      rw [chart_p₀] at chart_acted
      simp only [one_mul] at chart_acted
      have chart_p : chart p = (torsor.projection p, k) := by
        apply Prod.ext
        · exact chart.base_coordinate p hp
        · rfl
      have acted_eq : torsor.rightAction p₀ k = p := by
        apply chart.toPartialHomeomorph.injOn acted_mem hp
        rw [chart_acted, chart_p]
      change AdjointBundle.mk torsor p₀
          (YangMills.Mathematics.lieGroupAdjoint I k X) =
        AdjointBundle.mk torsor p X
      rw [← acted_eq]
      have quotientEquality := (AdjointBundle.mk_rightAction torsor p₀
        (YangMills.Mathematics.lieGroupAdjoint I k X) k).symm
      rw [YangMills.Mathematics.lieGroupAdjoint_inv_apply] at quotientEquality
      exact quotientEquality

omit [IsTopologicalGroup G] in
/-- On `baseSet × g`, inverse local coordinates followed by local coordinates are the identity. -/
theorem AdjointBundle.localCoordinate_localCoordinateInverse
    (z : B × GroupLieAlgebra I G) (hz : z.1 ∈ chart.baseSet) :
    AdjointBundle.localCoordinate (I := I) chart
        (AdjointBundle.localCoordinateInverse (I := I) chart z) = z := by
  let p₀ : P := chart.toPartialHomeomorph.symm (z.1, 1)
  have target_mem : (z.1, 1) ∈ chart.toPartialHomeomorph.target := by
    rw [chart.target_eq]
    exact ⟨hz, Set.mem_univ _⟩
  have p₀_mem : p₀ ∈ chart.toPartialHomeomorph.source :=
    chart.toPartialHomeomorph.map_target target_mem
  have chart_p₀ : chart p₀ = (z.1, 1) :=
    chart.toPartialHomeomorph.right_inv target_mem
  change AdjointBundle.localCoordinate (I := I) chart
    (AdjointBundle.mk torsor p₀ z.2) = z
  rw [AdjointBundle.localCoordinate_mk chart p₀ z.2 p₀_mem]
  have base_p₀ := chart.base_coordinate p₀ p₀_mem
  rw [chart_p₀] at base_p₀
  change (torsor.projection p₀,
    YangMills.Mathematics.lieGroupAdjoint I (chart p₀).2 z.2) = z
  rw [chart_p₀, ← base_p₀]
  simp [YangMills.Mathematics.lieGroupAdjoint_one]

end

end YangMills.Geometry
