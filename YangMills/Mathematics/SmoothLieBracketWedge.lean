/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieBracketWedge
import YangMills.Mathematics.SmoothManifoldDifferentialForms

/-!
# Smooth Lie-bracket wedges

Joint continuity of a Lie bracket is enough to build a pointwise continuous alternating form, but
curvature requires a form that varies smoothly over the manifold. This module isolates smoothness
of the bracket in normed value coordinates and proves closure of smooth one-forms under the
bracket-wedge operation.
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

/-- The Lie bracket written in a chosen normed value model. -/
def coordinateLieBracket (coordinates : V ≃L[ℝ] W) : W × W → W :=
  fun pair => coordinates ⁅coordinates.symm pair.1, coordinates.symm pair.2⁆

/-- Smoothness of a topological Lie bracket in continuously linear normed value coordinates. -/
class SmoothLieBracketCoordinates (coordinates : V ≃L[ℝ] W) : Prop where
  /-- The coordinate bracket is a smooth map of two normed variables. -/
  smooth_bracket :
    ContMDiff ((modelWithCornersSelf ℝ W).prod (modelWithCornersSelf ℝ W))
      (modelWithCornersSelf ℝ W) ∞ (coordinateLieBracket coordinates)

namespace ManifoldDifferentialForm.IsSmooth

/-- The bracket-wedge of two smooth one-forms is a smooth two-form. -/
theorem lieBracketWedgeOne
    (coordinates : V ≃L[ℝ] W) [SmoothLieBracketCoordinates coordinates]
    {first second : ManifoldDifferentialForm I M V 1}
    (first_smooth : first.IsSmooth coordinates)
    (second_smooth : second.IsSmooth coordinates) :
    (first.lieBracketWedgeOne second).IsSmooth coordinates := by
  intro s fields fields_smooth
  have first0 := first_smooth s (fun _ => fields 0) (fun _ => fields_smooth 0)
  have first1 := first_smooth s (fun _ => fields 1) (fun _ => fields_smooth 1)
  have second0 := second_smooth s (fun _ => fields 0) (fun _ => fields_smooth 0)
  have second1 := second_smooth s (fun _ => fields 1) (fun _ => fields_smooth 1)
  have bracket01 :=
    (SmoothLieBracketCoordinates.smooth_bracket (coordinates := coordinates)).comp_contMDiffOn
      (first0.prodMk second1)
  have bracket10 :=
    (SmoothLieBracketCoordinates.smooth_bracket (coordinates := coordinates)).comp_contMDiffOn
      (first1.prodMk second0)
  simpa [ManifoldDifferentialForm.lieBracketWedgeOne_apply, coordinateLieBracket] using
    bracket01.sub bracket10

end ManifoldDifferentialForm.IsSmooth

namespace SmoothManifoldDifferentialForm

/-- Bundle the pointwise bracket-wedge together with the derived smoothness proof. -/
noncomputable def lieBracketWedgeOne
    (coordinates : V ≃L[ℝ] W) [SmoothLieBracketCoordinates coordinates]
    (first second : SmoothManifoldDifferentialForm I M V coordinates 1) :
    SmoothManifoldDifferentialForm I M V coordinates 2 where
  toForm := first.toForm.lieBracketWedgeOne second.toForm
  smooth := first.smooth.lieBracketWedgeOne coordinates second.smooth

/-- Bundling smoothness does not alter the pointwise bracket-wedge. -/
@[simp]
theorem lieBracketWedgeOne_toForm
    (coordinates : V ≃L[ℝ] W) [SmoothLieBracketCoordinates coordinates]
    (first second : SmoothManifoldDifferentialForm I M V coordinates 1) :
    (lieBracketWedgeOne coordinates first second).toForm =
      first.toForm.lieBracketWedgeOne second.toForm :=
  rfl

/-- The smooth self-wedge retains the factor-two curvature normalization. -/
theorem lieBracketWedgeOne_self_apply
    (coordinates : V ≃L[ℝ] W) [SmoothLieBracketCoordinates coordinates]
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    (lieBracketWedgeOne coordinates form form).toForm x v =
      (2 : ℝ) • ⁅form.toForm x (fun _ => v 0), form.toForm x (fun _ => v 1)⁆ :=
  ContinuousAlternatingMap.lieBracketWedgeOne_self_apply (form.toForm x) v

end SmoothManifoldDifferentialForm

end YangMills.Mathematics
