/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupSmoothBracket

/-!
# Probes for smooth Lie-bracket wedges

These probes enforce smoothness closure, coherence with the pointwise operation, the self-wedge
normalization, zero behavior, and integration with the actual finite-dimensional tangent bracket.
-/

namespace YangMills.Mathematics.Probes

open scoped Manifold ContDiff

universe uE uH uM uV uW uEG uHG uG

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [LieRing V] [LieAlgebra ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [ContinuousLieBracket V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]
    {coordinates : V ≃L[ℝ] W} [SmoothLieBracketCoordinates coordinates]

/-- Smooth one-forms cannot produce a bracket-wedge that fails smoothness. -/
theorem nonsmooth_lieBracketWedge_blocked
    (first second : SmoothManifoldDifferentialForm I M V coordinates 1)
    (nonsmooth : ¬(first.toForm.lieBracketWedgeOne second.toForm).IsSmooth coordinates) : False :=
  nonsmooth (first.smooth.lieBracketWedgeOne coordinates second.smooth)

/-- The bundled smooth operation preserves the exact pointwise bracket-wedge. -/
theorem smooth_lieBracketWedge_pointwise_coherent
    (first second : SmoothManifoldDifferentialForm I M V coordinates 1) :
    (SmoothManifoldDifferentialForm.lieBracketWedgeOne coordinates first second).toForm =
      first.toForm.lieBracketWedgeOne second.toForm :=
  rfl

/-- The smooth self-wedge cannot lose the factor-two normalization. -/
theorem wrong_smooth_selfWedge_normalization_blocked
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (x : M) (v : Fin 2 → TangentSpace I x)
    (mismatch :
      (SmoothManifoldDifferentialForm.lieBracketWedgeOne coordinates form form).toForm x v ≠
        (2 : ℝ) • ⁅form.toForm x (fun _ => v 0), form.toForm x (fun _ => v 1)⁆) : False :=
  mismatch (form.lieBracketWedgeOne_self_apply coordinates x v)

/-- The wedge of two smooth zero one-forms is the zero two-form. -/
theorem zero_smooth_lieBracketWedge_eq_zero :
    (SmoothManifoldDifferentialForm.lieBracketWedgeOne coordinates
      (SmoothManifoldDifferentialForm.zero (I := I) (M := M) (V := V) coordinates 1)
      (SmoothManifoldDifferentialForm.zero (I := I) (M := M) (V := V) coordinates 1)).toForm = 0 := by
  ext x v
  simp [SmoothManifoldDifferentialForm.lieBracketWedgeOne,
    SmoothManifoldDifferentialForm.zero]

/-- The project's usual finite-dimensional `C∞` Lie-group context reaches the smooth wedge API. -/
theorem cinfinity_groupLieAlgebra_smoothWedge_available
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [TopologicalSpace HG]
    {IG : ModelWithCorners ℝ EG HG}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
    [LieGroup IG ∞ G]
    (first second : SmoothManifoldDifferentialForm I M (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) 1) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      infer_instance
    Nonempty (SmoothManifoldDifferentialForm I M (GroupLieAlgebra IG G)
      (groupLieAlgebraModelEquiv IG) 2) := by
  letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  exact ⟨SmoothManifoldDifferentialForm.lieBracketWedgeOne
    (I := I) (M := M) (V := GroupLieAlgebra IG G)
    (groupLieAlgebraModelEquiv IG) first second⟩

end YangMills.Mathematics.Probes
