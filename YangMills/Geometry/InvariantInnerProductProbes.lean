/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.InvariantInnerProduct

/-!
# Hostile probes for invariant Lie-algebra inner products

These probes reject degenerate, asymmetric, negative, and adjoint-noninvariant pairings while
checking that positive changes of normalization remain admissible.
-/

namespace YangMills.Geometry.Probes

open scoped Manifold ContDiff

universe uE uH uG

noncomputable section

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]

/-- A pairing that vanishes on a nonzero vector cannot be positive definite. -/
theorem degenerate_invariantInnerProduct_blocked
    (inner : InvariantInnerProductData (I := I) (G := G))
    (X : GroupLieAlgebra I G) (hX : X ≠ 0)
    (degenerate : inner.pairing X X = 0) : False :=
  (ne_of_gt (inner.positive hX)) degenerate

/-- Symmetry cannot be omitted or reversed at a chosen pair of vectors. -/
theorem asymmetric_invariantInnerProduct_blocked
    (inner : InvariantInnerProductData (I := I) (G := G))
    (X Y : GroupLieAlgebra I G)
    (asymmetric : inner.pairing X Y ≠ inner.pairing Y X) : False :=
  asymmetric (inner.symmetric X Y)

/-- A negative self-pairing cannot be hidden inside the certificate. -/
theorem negative_invariantInnerProduct_blocked
    (inner : InvariantInnerProductData (I := I) (G := G))
    (X : GroupLieAlgebra I G)
    (negative : inner.pairing X X < 0) : False :=
  (not_lt_of_ge (inner.quadratic_nonnegative X)) negative

/-- Invariance is tested using the adjoint action of the same explicit group carrier. -/
theorem adjoint_noninvariant_innerProduct_blocked
    (inner : InvariantInnerProductData (I := I) (G := G))
    (g : G) (X Y : GroupLieAlgebra I G)
    (mismatch : inner.pairing (YangMills.Mathematics.lieGroupAdjoint I g X)
      (YangMills.Mathematics.lieGroupAdjoint I g Y) ≠ inner.pairing X Y) : False :=
  mismatch (inner.adjoint_invariant g X Y)

/-- Positive normalization changes remain nondegenerate and adjoint invariant. -/
theorem positive_normalization_consistency
    (inner : InvariantInnerProductData (I := I) (G := G))
    (c : ℝ) (hc : 0 < c) (g : G) (X Y : GroupLieAlgebra I G) (hX : X ≠ 0) :
    0 < (inner.positiveScale c hc).pairing X X ∧
      (inner.positiveScale c hc).pairing
          (YangMills.Mathematics.lieGroupAdjoint I g X)
          (YangMills.Mathematics.lieGroupAdjoint I g Y) =
        (inner.positiveScale c hc).pairing X Y :=
  ⟨(inner.positiveScale c hc).positive hX,
    (inner.positiveScale c hc).adjoint_invariant g X Y⟩

end

end YangMills.Geometry.Probes
