/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupAdjoint

/-!
# Positive invariant inner products on a gauge Lie algebra

Clay/Jaffe--Witten equation (1) requires only an invariant quadratic form, written `Tr`, on the Lie
algebra of the compact gauge group. This project strengthens that terse wording by choosing a real,
continuous, symmetric, positive-definite bilinear presentation suitable for a positive Euclidean
action density. Those four properties are explicit formalization requirements, not claims about the
literal wording of Clay equation (1). Hall Proposition 5.17 gives supporting evidence via the
standard averaging construction for finite-dimensional representations of compact matrix groups;
it does not establish existence for this file's generic manifold API. Invariance here is imposed
under the adjoint action of the actual
group `G`, so the carrier's global form is never replaced by a cover or a matrix realization.

The normalization is deliberately not fixed: positive rescaling gives another admissible pairing
and is absorbed physically into the coupling convention.  No integration, Hodge star, action,
connection, curvature, or Yang--Mills field is constructed here.
-/

namespace YangMills.Geometry

open scoped Manifold ContDiff

universe uE uH uG

noncomputable section

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]

/-- A continuous positive-definite real inner product on the tangent Lie algebra, invariant under
adjoint action by every element of the actual gauge group.

It is represented explicitly as a bilinear pairing rather than installed globally as an
`InnerProductSpace` instance; this permits different normalizations to coexist without typeclass
conflicts. -/
structure InvariantInnerProductData where
  /-- The continuous bilinear pairing. -/
  pairing :
    GroupLieAlgebra I G →L[ℝ]
      GroupLieAlgebra I G →L[ℝ] ℝ
  /-- Symmetry of the pairing. -/
  symmetric : ∀ X Y, pairing X Y = pairing Y X
  /-- Strict positivity on every nonzero Lie-algebra vector. -/
  positive : ∀ {X}, X ≠ 0 → 0 < pairing X X
  /-- Invariance under the adjoint action of the same group `G`. -/
  adjoint_invariant : ∀ g X Y,
    pairing (YangMills.Mathematics.lieGroupAdjoint I g X)
      (YangMills.Mathematics.lieGroupAdjoint I g Y) = pairing X Y

namespace InvariantInnerProductData

/-- The quadratic value associated with an invariant inner product. -/
def quadratic (inner : InvariantInnerProductData (I := I) (G := G)) (X : GroupLieAlgebra I G) : ℝ :=
  inner.pairing X X

/-- The quadratic value is nonnegative. -/
theorem quadratic_nonnegative (inner : InvariantInnerProductData (I := I) (G := G))
    (X : GroupLieAlgebra I G) : 0 ≤ inner.quadratic X := by
  by_cases hX : X = 0
  · simp [quadratic, hX]
  · exact (inner.positive hX).le

/-- Positive definiteness detects precisely the zero vector. -/
@[simp]
theorem quadratic_eq_zero_iff (inner : InvariantInnerProductData (I := I) (G := G))
    (X : GroupLieAlgebra I G) : inner.quadratic X = 0 ↔ X = 0 := by
  constructor
  · intro h
    by_contra hX
    exact (ne_of_gt (inner.positive hX)) h
  · rintro rfl
    simp [quadratic]

/-- The quadratic value itself is invariant under the adjoint action. -/
theorem quadratic_adjoint_invariant (inner : InvariantInnerProductData (I := I) (G := G))
    (g : G) (X : GroupLieAlgebra I G) :
    inner.quadratic (YangMills.Mathematics.lieGroupAdjoint I g X) = inner.quadratic X :=
  inner.adjoint_invariant g X X

/-- Positive rescaling changes normalization but preserves every defining property. -/
def positiveScale (inner : InvariantInnerProductData (I := I) (G := G)) (c : ℝ) (hc : 0 < c) :
    InvariantInnerProductData (I := I) (G := G) where
  pairing := c • inner.pairing
  symmetric X Y := by simp [inner.symmetric X Y]
  positive {X} hX := by
    simpa using mul_pos hc (inner.positive hX)
  adjoint_invariant g X Y := by
    simp [inner.adjoint_invariant g X Y]

@[simp]
theorem positiveScale_pairing (inner : InvariantInnerProductData (I := I) (G := G))
    (c : ℝ) (hc : 0 < c) (X Y : GroupLieAlgebra I G) :
    (inner.positiveScale c hc).pairing X Y = c * inner.pairing X Y := by
  rfl

end InvariantInnerProductData

end

end YangMills.Geometry
