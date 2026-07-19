/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.NormedSpaceExteriorDerivative
import YangMills.Mathematics.ContinuousBilinearWedge
import Mathlib.Geometry.Manifold.VectorField.Pullback

/-!
# Normed-coordinate representations of manifold differential forms

A fixed-value manifold differential form can be pulled back to a normed model space using
Mathlib's manifold derivative and then transported through a continuous linear value-coordinate
equivalence. Two carriers are kept distinct:

* `normedCoordinateRawPullbackAlong` uses unrestricted `mfderiv` and is only a raw totalized carrier;
* `normedCoordinatePullbackWithinAlong` uses `mfderivWithin` on an explicit set.

The inverse extended-chart specialization uses the second carrier with `Set.range I`, exactly as
Mathlib's chart-vector-field pullback does. On the chart target this derivative is invertible, so the
transport cannot silently collapse at boundary or corner points.

The canonical within-set carrier preserves addition and scalar multiplication and transports the
intrinsic graded group Lie-bracket wedge to the coordinate wedge. Exterior-derivative naturality and
chart-target regularity remain separate work.
-/

namespace YangMills.Mathematics

open Set
open scoped Manifold ContDiff

universe uE uH uM uV uW uEG uHG uG

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M]

/-- Raw totalized coordinate pullback using unrestricted `mfderiv`. Meaningful use requires the
corresponding full differentiability hypotheses. -/
noncomputable def ManifoldDifferentialForm.normedCoordinateRawPullbackAlong
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : ManifoldDifferentialForm I M V k) (map : E → M) :
    NormedSpaceDifferentialForm E W k := fun x =>
  coordinates.toContinuousLinearMap.compContinuousAlternatingMap
    ((form (map x)).compContinuousLinearMap
      (mfderiv (modelWithCornersSelf ℝ E) I map x))

/-- Exact evaluation of the raw unrestricted pullback. -/
@[simp]
theorem ManifoldDifferentialForm.normedCoordinateRawPullbackAlong_apply
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : ManifoldDifferentialForm I M V k) (map : E → M)
    (x : E) (vectors : Fin k → E) :
    form.normedCoordinateRawPullbackAlong coordinates k map x vectors =
      coordinates (form (map x) (fun i =>
        mfderiv (modelWithCornersSelf ℝ E) I map x (vectors i))) :=
  rfl

/-- Canonical coordinate pullback within one explicit source set. -/
noncomputable def ManifoldDifferentialForm.normedCoordinatePullbackWithinAlong
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : ManifoldDifferentialForm I M V k) (map : E → M) (source : Set E) :
    NormedSpaceDifferentialForm E W k := fun x =>
  coordinates.toContinuousLinearMap.compContinuousAlternatingMap
    ((form (map x)).compContinuousLinearMap
      (mfderivWithin (modelWithCornersSelf ℝ E) I map source x))

/-- Exact evaluation of the within-set coordinate pullback. -/
@[simp]
theorem ManifoldDifferentialForm.normedCoordinatePullbackWithinAlong_apply
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : ManifoldDifferentialForm I M V k) (map : E → M) (source : Set E)
    (x : E) (vectors : Fin k → E) :
    form.normedCoordinatePullbackWithinAlong coordinates k map source x vectors =
      coordinates (form (map x) (fun i =>
        mfderivWithin (modelWithCornersSelf ℝ E) I map source x (vectors i))) :=
  rfl

/-- Extended-chart coordinates use the inverse-chart derivative within `range I`, not the
unrestricted derivative of its totalization. Geometric interpretation remains restricted to the
chart target. -/
noncomputable def ManifoldDifferentialForm.inExtChartAt
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : ManifoldDifferentialForm I M V k) (p : M) :
    NormedSpaceDifferentialForm E W k :=
  form.normedCoordinatePullbackWithinAlong coordinates k
    (extChartAt I p).symm (Set.range ⇑I)

/-- Exact evaluation of the corrected extended-chart representation. -/
@[simp]
theorem ManifoldDifferentialForm.inExtChartAt_apply
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : ManifoldDifferentialForm I M V k) (p : M)
    (x : E) (vectors : Fin k → E) :
    form.inExtChartAt coordinates k p x vectors =
      coordinates (form ((extChartAt I p).symm x) (fun i =>
        mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
          (Set.range ⇑I) x (vectors i))) :=
  rfl

/-- At the chart image of its center, the represented form evaluates at the original point with the
canonical within-range inverse-chart derivative. -/
theorem ManifoldDifferentialForm.inExtChartAt_center
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : ManifoldDifferentialForm I M V k) (p : M) (vectors : Fin k → E) :
    form.inExtChartAt coordinates k p ((extChartAt I p) p) vectors =
      coordinates (form p (fun i =>
        mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
          (Set.range ⇑I) ((extChartAt I p) p) (vectors i))) := by
  rw [ManifoldDifferentialForm.inExtChartAt_apply, extChartAt_to_inv]

/-- On the chart target, the corrected inverse-chart tangent transport is invertible. -/
theorem ManifoldDifferentialForm.inExtChartAt_tangentMap_isInvertible
    [IsManifold I 1 M] (p : M) (x : E) (mem_target : x ∈ (extChartAt I p).target) :
    (mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
      (Set.range ⇑I) x).IsInvertible :=
  isInvertible_mfderivWithin_extChartAt_symm mem_target

/-- In particular, tangent transport at the chart center is invertible and cannot be the zero map
unless the model tangent space is trivial. -/
theorem ManifoldDifferentialForm.inExtChartAt_center_tangentMap_isInvertible
    [IsManifold I 1 M] (p : M) :
    (mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
      (Set.range ⇑I) ((extChartAt I p) p)).IsInvertible :=
  isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target p)

/-- Within-set coordinate pullback preserves addition exactly. -/
@[simp]
theorem ManifoldDifferentialForm.normedCoordinatePullbackWithinAlong_add
    (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (first second : ManifoldDifferentialForm I M V k)
    (map : E → M) (source : Set E) :
    (first + second).normedCoordinatePullbackWithinAlong coordinates k map source =
      first.normedCoordinatePullbackWithinAlong coordinates k map source +
        second.normedCoordinatePullbackWithinAlong coordinates k map source := by
  funext x
  ext vectors
  simp [ManifoldDifferentialForm.normedCoordinatePullbackWithinAlong]

/-- Within-set coordinate pullback preserves real scalar multiplication exactly. -/
@[simp]
theorem ManifoldDifferentialForm.normedCoordinatePullbackWithinAlong_smul
    (coordinates : V ≃L[ℝ] W) (k : ℕ) (scalar : ℝ)
    (form : ManifoldDifferentialForm I M V k)
    (map : E → M) (source : Set E) :
    (scalar • form).normedCoordinatePullbackWithinAlong coordinates k map source =
      scalar • form.normedCoordinatePullbackWithinAlong coordinates k map source := by
  funext x
  ext vectors
  simp [ManifoldDifferentialForm.normedCoordinatePullbackWithinAlong]

set_option backward.isDefEq.respectTransparency false in
/-- Canonical group Lie-algebra coordinates carry the intrinsic graded bracket wedge through the
same within-set tangent transport to the exact continuous-bilinear coordinate wedge. -/
theorem ManifoldDifferentialForm.normedCoordinatePullbackWithinAlong_lieBracketWedgeOneMany
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
    [LieGroup IG (minSmoothness ℝ 3) G]
    (n : ℕ) (alpha : ManifoldDifferentialForm I M (GroupLieAlgebra IG G) 1)
    (beta : ManifoldDifferentialForm I M (GroupLieAlgebra IG G) n)
    (map : E → M) (source : Set E) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    (alpha.lieBracketWedgeOneMany n beta).normedCoordinatePullbackWithinAlong
        (groupLieAlgebraModelEquiv IG) (n + 1) map source =
      (fun x => ContinuousAlternatingMap.continuousBilinearWedgeOneMany
        (groupLieAlgebraCoordinateBracketCLM (I := IG) (G := G)) n
        (alpha.normedCoordinatePullbackWithinAlong
          (groupLieAlgebraModelEquiv IG) 1 map source x)
        (beta.normedCoordinatePullbackWithinAlong
          (groupLieAlgebraModelEquiv IG) n map source x)) := by
  funext x
  let tangentMap := mfderivWithin (modelWithCornersSelf ℝ E) I map source x
  let alphaAt : E [⋀^Fin 1]→L[ℝ] GroupLieAlgebra IG G :=
    (alpha (map x)).compContinuousLinearMap tangentMap
  let betaAt : E [⋀^Fin n]→L[ℝ] GroupLieAlgebra IG G :=
    (beta (map x)).compContinuousLinearMap tangentMap
  have coherence := groupLieAlgebraCoordinateBracket_wedge_coherence
    (I := IG) (G := G) n alphaAt betaAt
  convert coherence using 1 <;> ext vectors <;>
    simp [alphaAt, betaAt, tangentMap,
      ManifoldDifferentialForm.normedCoordinatePullbackWithinAlong,
      ManifoldDifferentialForm.lieBracketWedgeOneMany_apply,
      ContinuousAlternatingMap.lieBracketWedgeOneMany_apply,
      ContinuousAlternatingMap.continuousBilinearWedgeOneMany_apply]
  all_goals
    apply Finset.sum_congr rfl
    intro i hi
    congr 3

/-- Extended-chart specialization of canonical bracket-wedge coordinate coherence. -/
theorem ManifoldDifferentialForm.inExtChartAt_lieBracketWedgeOneMany
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
    {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
    [LieGroup IG (minSmoothness ℝ 3) G]
    (n : ℕ) (alpha : ManifoldDifferentialForm I M (GroupLieAlgebra IG G) 1)
    (beta : ManifoldDifferentialForm I M (GroupLieAlgebra IG G) n) (p : M) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    (alpha.lieBracketWedgeOneMany n beta).inExtChartAt
        (groupLieAlgebraModelEquiv IG) (n + 1) p =
      (fun x => ContinuousAlternatingMap.continuousBilinearWedgeOneMany
        (groupLieAlgebraCoordinateBracketCLM (I := IG) (G := G)) n
        (alpha.inExtChartAt (groupLieAlgebraModelEquiv IG) 1 p x)
        (beta.inExtChartAt (groupLieAlgebraModelEquiv IG) n p x)) := by
  exact alpha.normedCoordinatePullbackWithinAlong_lieBracketWedgeOneMany
    (IG := IG) (G := G) n beta (extChartAt I p).symm (Set.range ⇑I)

end YangMills.Mathematics
