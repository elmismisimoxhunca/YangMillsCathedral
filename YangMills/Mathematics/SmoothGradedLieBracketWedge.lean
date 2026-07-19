/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.GradedLieBracketWedge
import YangMills.Mathematics.SmoothLieBracketWedge

/-!
# Smooth graded Lie-bracket wedges

This module proves that the continuous graded bracket wedge of a smooth one-form with a smooth
`n`-form is smooth. Each omitted-slot term is evaluated on the corresponding smooth tangent fields,
the bracket is taken in the exact normed value coordinates, and the finite signed sum is smooth.

The bundled construction does not alter the pointwise graded wedge. At degree one its carrier is
therefore exactly the previously constructed smooth two-form carrier. This is reusable
infrastructure only: no covariant exterior derivative or Bianchi identity is defined.
-/

namespace YangMills.Mathematics

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

namespace ManifoldDifferentialForm.IsSmooth

/-- The graded bracket wedge of a smooth one-form with a smooth `n`-form is smooth. -/
theorem lieBracketWedgeOneMany
    (coordinates : V ≃L[ℝ] W) [SmoothLieBracketCoordinates coordinates]
    (n : ℕ) {alpha : ManifoldDifferentialForm I M V 1}
    {beta : ManifoldDifferentialForm I M V n}
    (alpha_smooth : alpha.IsSmooth coordinates)
    (beta_smooth : beta.IsSmooth coordinates) :
    (alpha.lieBracketWedgeOneMany n beta).IsSmooth coordinates := by
  intro s fields fields_smooth
  have term_smooth : ∀ i : Fin (n + 1), ContMDiffOn I (modelWithCornersSelf ℝ W) ∞
      (fun x => (-1 : ℤ) ^ (i : ℕ) • coordinateLieBracket coordinates
        (coordinates (alpha x (fun _ => fields i x)),
          coordinates (beta x (fun j => fields (i.succAbove j) x)))) s := by
    intro i
    have alpha_i := alpha_smooth s (fun _ => fields i) (fun _ => fields_smooth i)
    have beta_without_i := beta_smooth s (fun j x => fields (i.succAbove j) x)
      (fun j => fields_smooth (i.succAbove j))
    have bracket_i :=
      (SmoothLieBracketCoordinates.smooth_bracket (coordinates := coordinates)).comp_contMDiffOn
        (alpha_i.prodMk beta_without_i)
    let scale : W →L[ℝ] W :=
      ((-1 : ℝ) ^ (i : ℕ)) • ContinuousLinearMap.id ℝ W
    have scaled_i := scale.contMDiff.comp_contMDiffOn bracket_i
    convert scaled_i using 1
    funext x
    simp [scale, coordinateLieBracket, Function.comp_def]
    rw [← Int.cast_smul_eq_zsmul ℝ]
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
  have sum_smooth := contMDiffOn_finsetSum (t := Finset.univ)
    (f := fun i : Fin (n + 1) => fun x =>
      (-1 : ℤ) ^ (i : ℕ) • coordinateLieBracket coordinates
        (coordinates (alpha x (fun _ => fields i x)),
          coordinates (beta x (fun j => fields (i.succAbove j) x))))
    (fun i hi => term_smooth i)
  convert sum_smooth using 1
  funext x
  rw [ManifoldDifferentialForm.lieBracketWedgeOneMany_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_zsmul]
  have hremove : i.removeNth (fun k => fields k x) =
      fun j => fields (i.succAbove j) x := rfl
  rw [hremove]
  simp [coordinateLieBracket]

end ManifoldDifferentialForm.IsSmooth

namespace SmoothManifoldDifferentialForm

/-- Bundle the exact pointwise graded bracket wedge with its derived smoothness. -/
noncomputable def lieBracketWedgeOneMany
    (coordinates : V ≃L[ℝ] W) [SmoothLieBracketCoordinates coordinates]
    (n : ℕ) (alpha : SmoothManifoldDifferentialForm I M V coordinates 1)
    (beta : SmoothManifoldDifferentialForm I M V coordinates n) :
    SmoothManifoldDifferentialForm I M V coordinates (n + 1) where
  toForm := alpha.toForm.lieBracketWedgeOneMany n beta.toForm
  smooth := alpha.smooth.lieBracketWedgeOneMany coordinates n beta.smooth

/-- Forgetting smoothness recovers exactly the pointwise graded bracket wedge. -/
@[simp]
theorem lieBracketWedgeOneMany_toForm
    (coordinates : V ≃L[ℝ] W) [SmoothLieBracketCoordinates coordinates]
    (n : ℕ) (alpha : SmoothManifoldDifferentialForm I M V coordinates 1)
    (beta : SmoothManifoldDifferentialForm I M V coordinates n) :
    (lieBracketWedgeOneMany coordinates n alpha beta).toForm =
      alpha.toForm.lieBracketWedgeOneMany n beta.toForm :=
  rfl

/-- At degree one, the new bundled operation has exactly the existing smooth bracket-wedge carrier. -/
theorem lieBracketWedgeOneMany_one_toForm
    (coordinates : V ≃L[ℝ] W) [SmoothLieBracketCoordinates coordinates]
    (alpha beta : SmoothManifoldDifferentialForm I M V coordinates 1) :
    (lieBracketWedgeOneMany coordinates 1 alpha beta).toForm =
      (lieBracketWedgeOne coordinates alpha beta).toForm := by
  funext x
  exact ContinuousAlternatingMap.lieBracketWedgeOneMany_one
    (alpha.toForm x) (beta.toForm x)

end SmoothManifoldDifferentialForm

end YangMills.Mathematics
