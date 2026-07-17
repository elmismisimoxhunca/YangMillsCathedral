/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleTrivialization
import YangMills.Geometry.SmoothPrincipalBundle

/-!
# Transition maps for adjoint-bundle quotient charts

This module identifies the exact change of fiber coordinates between two promoted adjoint-bundle
trivializations. The transition is derived from the already fixed quotient coordinates: over `b`, it
acts by the adjoint representation of the group component of the corresponding principal-bundle
transition at `(b, 1)`.

The formula is a prerequisite for a smooth fiberwise-linear atlas. No charted-space, manifold,
`FiberBundle`, or `VectorBundle` instance is installed here.
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
    (bundle : TopologicalPrincipalBundleData torsor)
    (first second : PrincipalBundleLocalTrivialization torsor)

/-- Natural coordinate domain for an associated transition. Membership depends only on the base
coordinate and says that the principal transition at group coordinate `1` is defined. -/
def adjointBundleOverlapDomain : Set (B × GroupLieAlgebra I G) :=
  {z | (z.1, (1 : G)) ∈ principalBundleOverlapDomain first second}

/-- Change of coordinates between two promoted adjoint-bundle trivializations. -/
def adjointBundleTransition (z : B × GroupLieAlgebra I G) :
    B × GroupLieAlgebra I G :=
  AdjointBundle.bundleTrivialization (I := I) bundle second
    ((AdjointBundle.bundleTrivialization (I := I) bundle first).toOpenPartialHomeomorph.symm z)

omit [IsTopologicalGroup G] [LieGroup I ∞ G] in
/-- The associated overlap domain is exactly the inverse image of the principal overlap domain under
`(b,X) ↦ (b,1)`. -/
theorem mem_adjointBundleOverlapDomain_iff (z : B × GroupLieAlgebra I G) :
    z ∈ adjointBundleOverlapDomain (I := I) first second ↔
      (z.1, (1 : G)) ∈ principalBundleOverlapDomain first second :=
  Iff.rfl

omit [IsTopologicalGroup G] [LieGroup I ∞ G] in
/-- The associated overlap domain is open. -/
theorem isOpen_adjointBundleOverlapDomain :
    IsOpen (adjointBundleOverlapDomain (I := I) first second) := by
  have unitInput : Continuous
      (fun z : B × GroupLieAlgebra I G => (z.1, (1 : G))) :=
    continuous_fst.prodMk continuous_const
  exact (isOpen_principalBundleOverlapDomain first second).preimage unitInput

/-- Exact associated transition formula. Its fiber operator is not a caller-selected map: it is the
adjoint action of the actual principal overlap coordinate in the correct order. -/
theorem adjointBundleTransition_eq
    (z : B × GroupLieAlgebra I G)
    (hz : z ∈ adjointBundleOverlapDomain (I := I) first second) :
    adjointBundleTransition (I := I) bundle first second z =
      (z.1, YangMills.Mathematics.lieGroupAdjoint I
        (principalBundleTransition first second (z.1, (1 : G))).2 z.2) := by
  let p₀ : P := first.toPartialHomeomorph.symm (z.1, (1 : G))
  have firstTarget : (z.1, (1 : G)) ∈ first.toPartialHomeomorph.target := hz.1
  have p₀FirstSource : p₀ ∈ first.toPartialHomeomorph.source :=
    first.toPartialHomeomorph.map_target firstTarget
  have p₀SecondSource : p₀ ∈ second.toPartialHomeomorph.source := hz.2
  have firstP₀ : first p₀ = (z.1, (1 : G)) :=
    first.toPartialHomeomorph.right_inv firstTarget
  have baseP₀ := first.base_coordinate p₀ p₀FirstSource
  rw [firstP₀] at baseP₀
  change AdjointBundle.localCoordinate (I := I) second
    (AdjointBundle.localCoordinateInverse (I := I) first z) = _
  change AdjointBundle.localCoordinate (I := I) second
    (AdjointBundle.mk torsor p₀ z.2) = _
  rw [AdjointBundle.localCoordinate_mk second p₀ z.2 p₀SecondSource]
  apply Prod.ext
  · exact baseP₀.symm
  · rfl

/-- The associated transition fixes the base coordinate. -/
theorem adjointBundleTransition_fst
    (z : B × GroupLieAlgebra I G)
    (hz : z ∈ adjointBundleOverlapDomain (I := I) first second) :
    (adjointBundleTransition (I := I) bundle first second z).1 = z.1 := by
  rw [adjointBundleTransition_eq (I := I) bundle first second z hz]

/-- Reversing the ordered associated transition recovers the original coordinate on the overlap.
This is proved through the exact quotient-coordinate inverse laws rather than by postulating an
unrelated inverse fiber operator. -/
theorem adjointBundleTransition_reverse
    (z : B × GroupLieAlgebra I G)
    (hz : z ∈ adjointBundleOverlapDomain (I := I) first second) :
    adjointBundleTransition (I := I) bundle second first
      (adjointBundleTransition (I := I) bundle first second z) = z := by
  let p₀ : P := first.toPartialHomeomorph.symm (z.1, (1 : G))
  let q : AdjointBundle (I := I) torsor :=
    AdjointBundle.localCoordinateInverse (I := I) first z
  change (z.1, (1 : G)) ∈ principalBundleOverlapDomain first second at hz
  have firstTarget : (z.1, (1 : G)) ∈ first.toPartialHomeomorph.target := hz.1
  have firstBase : z.1 ∈ first.baseSet := by
    rw [first.target_eq] at firstTarget
    exact firstTarget.1
  have p₀SecondSource : p₀ ∈ second.toPartialHomeomorph.source := hz.2
  have p₀SecondBase : torsor.projection p₀ ∈ second.baseSet := by
    rw [second.source_eq] at p₀SecondSource
    exact p₀SecondSource
  have qSecondBase : AdjointBundle.projection torsor q ∈ second.baseSet := by
    change AdjointBundle.projection torsor (AdjointBundle.mk torsor p₀ z.2) ∈ second.baseSet
    rw [AdjointBundle.projection_mk]
    exact p₀SecondBase
  change AdjointBundle.localCoordinate (I := I) first
    (AdjointBundle.localCoordinateInverse (I := I) second
      (AdjointBundle.localCoordinate (I := I) second q)) = z
  rw [AdjointBundle.localCoordinateInverse_localCoordinate second q qSecondBase]
  exact AdjointBundle.localCoordinate_localCoordinateInverse first z firstBase

/-- Every associated transition preserves the zero fiber vector. -/
theorem adjointBundleTransition_zero
    (b : B)
    (hb : (b, (0 : GroupLieAlgebra I G)) ∈
      adjointBundleOverlapDomain (I := I) first second) :
    adjointBundleTransition (I := I) bundle first second (b, 0) = (b, 0) := by
  rw [adjointBundleTransition_eq (I := I) bundle first second _ hb]
  simp

/-- The fiber part of every associated transition preserves addition. -/
theorem adjointBundleTransition_snd_add
    (b : B) (X Y : GroupLieAlgebra I G)
    (hX : (b, X) ∈ adjointBundleOverlapDomain (I := I) first second) :
    (adjointBundleTransition (I := I) bundle first second (b, X + Y)).2 =
      (adjointBundleTransition (I := I) bundle first second (b, X)).2 +
        (adjointBundleTransition (I := I) bundle first second (b, Y)).2 := by
  have hY : (b, Y) ∈ adjointBundleOverlapDomain (I := I) first second := hX
  have hXY : (b, X + Y) ∈ adjointBundleOverlapDomain (I := I) first second := hX
  rw [adjointBundleTransition_eq (I := I) bundle first second _ hXY,
    adjointBundleTransition_eq (I := I) bundle first second _ hX,
    adjointBundleTransition_eq (I := I) bundle first second _ hY]
  exact map_add _ _ _

/-- The fiber part of every associated transition preserves real scalar multiplication. -/
theorem adjointBundleTransition_snd_smul
    (b : B) (c : ℝ) (X : GroupLieAlgebra I G)
    (hX : (b, X) ∈ adjointBundleOverlapDomain (I := I) first second) :
    (adjointBundleTransition (I := I) bundle first second (b, c • X)).2 =
      c • (adjointBundleTransition (I := I) bundle first second (b, X)).2 := by
  have hcX : (b, c • X) ∈ adjointBundleOverlapDomain (I := I) first second := hX
  rw [adjointBundleTransition_eq (I := I) bundle first second _ hcX,
    adjointBundleTransition_eq (I := I) bundle first second _ hX]
  exact map_smul _ _ _

end

end YangMills.Geometry
