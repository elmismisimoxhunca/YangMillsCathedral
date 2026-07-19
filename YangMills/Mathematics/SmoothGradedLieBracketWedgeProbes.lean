/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SmoothGradedLieBracketWedge

/-!
# Hostile probes for smooth graded Lie-bracket wedges

These probes lock smooth closure to the exact graded carrier, degree-one coherence with the earlier
smooth operation, rejection of unrelated smooth outputs, and the smooth one-with-two endpoint used
as infrastructure before Bianchi.
-/

namespace YangMills.Mathematics.SmoothGradedLieBracketWedge.Probes

open Set
open scoped Manifold ContDiff

universe uE uH uM uV uW

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [LieRing V] [LieAlgebra ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [ContinuousLieBracket V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]
    {coordinates : V ≃L[ℝ] W} [SmoothLieBracketCoordinates coordinates]

/-- Smooth inputs force smoothness of the exact pointwise graded wedge. -/
theorem exact_smooth_closure
    (n : ℕ) {alpha : ManifoldDifferentialForm I M V 1}
    {beta : ManifoldDifferentialForm I M V n}
    (alpha_smooth : alpha.IsSmooth coordinates)
    (beta_smooth : beta.IsSmooth coordinates) :
    (alpha.lieBracketWedgeOneMany n beta).IsSmooth coordinates :=
  alpha_smooth.lieBracketWedgeOneMany coordinates n beta_smooth

/-- Bundling smoothness cannot replace the pointwise graded carrier. -/
theorem exact_pointwise_carrier
    (n : ℕ) (alpha : SmoothManifoldDifferentialForm I M V coordinates 1)
    (beta : SmoothManifoldDifferentialForm I M V coordinates n) :
    (alpha.lieBracketWedgeOneMany coordinates n beta).toForm =
      alpha.toForm.lieBracketWedgeOneMany n beta.toForm :=
  rfl

/-- At degree one, the bundled carrier remains exactly the earlier smooth bracket wedge. -/
theorem exact_degree_one_smooth_coherence
    (alpha beta : SmoothManifoldDifferentialForm I M V coordinates 1) :
    (alpha.lieBracketWedgeOneMany coordinates 1 beta).toForm =
      (alpha.lieBracketWedgeOne coordinates beta).toForm :=
  SmoothManifoldDifferentialForm.lieBracketWedgeOneMany_one_toForm coordinates alpha beta

/-- A smooth form with a different pointwise carrier cannot replace the derived output. -/
theorem unrelated_smooth_output_blocked
    (n : ℕ) (alpha : SmoothManifoldDifferentialForm I M V coordinates 1)
    (beta : SmoothManifoldDifferentialForm I M V coordinates n)
    (other : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (hne : other.toForm ≠ alpha.toForm.lieBracketWedgeOneMany n beta.toForm) :
    other ≠ alpha.lieBracketWedgeOneMany coordinates n beta := by
  intro h
  apply hne
  rw [h]
  rfl

/-- In particular, the exact one-with-two three-form carrier is smooth. -/
theorem exact_smooth_one_with_two
    (alpha : SmoothManifoldDifferentialForm I M V coordinates 1)
    (beta : SmoothManifoldDifferentialForm I M V coordinates 2) :
    (alpha.toForm.lieBracketWedgeOneMany 2 beta.toForm).IsSmooth coordinates :=
  alpha.smooth.lieBracketWedgeOneMany coordinates 2 beta.smooth

/-- The smoothly bundled cubic self-bracket has the exact zero three-form carrier. -/
theorem exact_smooth_cubic_jacobi_cancellation
    (alpha : SmoothManifoldDifferentialForm I M V coordinates 1) :
    (SmoothManifoldDifferentialForm.lieBracketWedgeOneManySelfSelf
      coordinates alpha).toForm = 0 :=
  SmoothManifoldDifferentialForm.lieBracketWedgeOneManySelfSelf_toForm coordinates alpha

/-- A nonzero carrier cannot be substituted for the smooth cubic Jacobi cancellation. -/
theorem nonzero_smooth_cubic_self_bracket_blocked
    (alpha : SmoothManifoldDifferentialForm I M V coordinates 1)
    (hne : (SmoothManifoldDifferentialForm.lieBracketWedgeOneManySelfSelf
      coordinates alpha).toForm ≠ 0) : False :=
  hne (SmoothManifoldDifferentialForm.lieBracketWedgeOneManySelfSelf_toForm
    coordinates alpha)

/-- A smooth zero one-form gives the exact zero pointwise graded carrier. -/
theorem exact_smooth_zero_left
    (n : ℕ) (beta : SmoothManifoldDifferentialForm I M V coordinates n) :
    ((SmoothManifoldDifferentialForm.zero coordinates 1).lieBracketWedgeOneMany
      coordinates n beta).toForm = 0 := by
  rw [SmoothManifoldDifferentialForm.lieBracketWedgeOneMany_toForm]
  funext x
  exact ContinuousAlternatingMap.zero_lieBracketWedgeOneMany n (beta.toForm x)

end YangMills.Mathematics.SmoothGradedLieBracketWedge.Probes
