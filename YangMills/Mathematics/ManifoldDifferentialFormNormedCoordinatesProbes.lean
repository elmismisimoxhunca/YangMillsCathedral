/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/
import YangMills.Mathematics.ManifoldDifferentialFormNormedCoordinates

/-! Hostile probes distinguish raw `mfderiv` transport from canonical within-range chart transport. -/
namespace YangMills.Mathematics.ManifoldDifferentialFormNormedCoordinates.Probes
open Set
open scoped Manifold ContDiff
universe uE uH uM uV uW uEG uHG uG
variable {E : Type uE} {H : Type uH}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M]
  {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M]

/-- The raw carrier explicitly uses unrestricted `mfderiv`. -/
theorem exact_raw_evaluation (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : ManifoldDifferentialForm I M V k) (map : E → M)
    (x : E) (vectors : Fin k → E) :
    form.normedCoordinateRawPullbackAlong coordinates k map x vectors =
      coordinates (form (map x) (fun i =>
        mfderiv (modelWithCornersSelf ℝ E) I map x (vectors i))) := rfl

/-- The canonical carrier retains the exact source set. -/
theorem exact_within_evaluation (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : ManifoldDifferentialForm I M V k) (map : E → M) (source : Set E)
    (x : E) (vectors : Fin k → E) :
    form.normedCoordinatePullbackWithinAlong coordinates k map source x vectors =
      coordinates (form (map x) (fun i =>
        mfderivWithin (modelWithCornersSelf ℝ E) I map source x (vectors i))) := rfl

/-- Inverse-chart coordinates use `mfderivWithin` on `range I`. -/
theorem exact_chart_evaluation (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : ManifoldDifferentialForm I M V k) (p : M)
    (x : E) (vectors : Fin k → E) :
    form.inExtChartAt coordinates k p x vectors =
      coordinates (form ((extChartAt I p).symm x) (fun i =>
        mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
          (Set.range ⇑I) x (vectors i))) := rfl

/-- The chart center recovers the point with the same within-range derivative. -/
theorem exact_chart_center (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : ManifoldDifferentialForm I M V k) (p : M) (vectors : Fin k → E) :
    form.inExtChartAt coordinates k p ((extChartAt I p) p) vectors =
      coordinates (form p (fun i =>
        mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
          (Set.range ⇑I) ((extChartAt I p) p) (vectors i))) :=
  form.inExtChartAt_center coordinates k p vectors

/-- Target-local tangent transport is invertible. -/
theorem exact_target_invertibility [IsManifold I 1 M]
    (p : M) (x : E) (hx : x ∈ (extChartAt I p).target) :
    (mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
      (Set.range ⇑I) x).IsInvertible :=
  ManifoldDifferentialForm.inExtChartAt_tangentMap_isInvertible p x hx

/-- Nontrivial center transport cannot silently collapse to zero. -/
theorem zero_center_transport_blocked [IsManifold I 1 M] [Nontrivial E] (p : M)
    (hzero : mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I p).symm
      (Set.range ⇑I) ((extChartAt I p) p) = 0) : False := by
  have hi := ManifoldDifferentialForm.inExtChartAt_center_tangentMap_isInvertible (I := I) p
  have hinj := hi.bijective.injective
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  apply hv
  apply hinj
  rw [hzero]
  rfl

/-- Within-set coordinate pullback preserves its exact algebra. -/
theorem exact_within_linearity (coordinates : V ≃L[ℝ] W) (k : ℕ) (r : ℝ)
    (a b : ManifoldDifferentialForm I M V k) (map : E → M) (source : Set E) :
    ((a + b).normedCoordinatePullbackWithinAlong coordinates k map source =
      a.normedCoordinatePullbackWithinAlong coordinates k map source +
      b.normedCoordinatePullbackWithinAlong coordinates k map source) ∧
    ((r • a).normedCoordinatePullbackWithinAlong coordinates k map source =
      r • a.normedCoordinatePullbackWithinAlong coordinates k map source) :=
  ⟨a.normedCoordinatePullbackWithinAlong_add coordinates k b map source,
   a.normedCoordinatePullbackWithinAlong_smul coordinates k r map source⟩

/-- A replacement for the exact within-set transport is rejected. -/
theorem malformed_transport_blocked (coordinates : V ≃L[ℝ] W) (k : ℕ)
    (form : ManifoldDifferentialForm I M V k) (map : E → M) (source : Set E)
    (x : E) (vectors : Fin k → E) (wrong : W)
    (hne : wrong ≠ coordinates (form (map x) (fun i =>
      mfderivWithin (modelWithCornersSelf ℝ E) I map source x (vectors i))))
    (h : form.normedCoordinatePullbackWithinAlong coordinates k map source x vectors = wrong) : False := by
  apply hne
  rw [← h]
  rfl

variable {EG : Type uEG} {HG : Type uHG}
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  [LieGroup IG (minSmoothness ℝ 3) G]

/-- Canonical within-set transport preserves the exact bracket wedge. -/
theorem exact_within_bracket_wedge (n : ℕ)
    (a : ManifoldDifferentialForm I M (GroupLieAlgebra IG G) 1)
    (b : ManifoldDifferentialForm I M (GroupLieAlgebra IG G) n)
    (map : E → M) (source : Set E) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    (a.lieBracketWedgeOneMany n b).normedCoordinatePullbackWithinAlong
        (groupLieAlgebraModelEquiv IG) (n + 1) map source =
      fun x => ContinuousAlternatingMap.continuousBilinearWedgeOneMany
        (groupLieAlgebraCoordinateBracketCLM (I := IG) (G := G)) n
        (a.normedCoordinatePullbackWithinAlong (groupLieAlgebraModelEquiv IG) 1 map source x)
        (b.normedCoordinatePullbackWithinAlong (groupLieAlgebraModelEquiv IG) n map source x) :=
  a.normedCoordinatePullbackWithinAlong_lieBracketWedgeOneMany
    (IG := IG) (G := G) n b map source

/-- Inverse extended-chart transport preserves the same exact bracket wedge. -/
theorem exact_chart_bracket_wedge (n : ℕ)
    (a : ManifoldDifferentialForm I M (GroupLieAlgebra IG G) 1)
    (b : ManifoldDifferentialForm I M (GroupLieAlgebra IG G) n) (p : M) :
    letI : CompleteSpace EG := FiniteDimensional.complete ℝ EG
    (a.lieBracketWedgeOneMany n b).inExtChartAt
        (groupLieAlgebraModelEquiv IG) (n + 1) p =
      fun x => ContinuousAlternatingMap.continuousBilinearWedgeOneMany
        (groupLieAlgebraCoordinateBracketCLM (I := IG) (G := G)) n
        (a.inExtChartAt (groupLieAlgebraModelEquiv IG) 1 p x)
        (b.inExtChartAt (groupLieAlgebraModelEquiv IG) n p x) :=
  a.inExtChartAt_lieBracketWedgeOneMany (IG := IG) (G := G) n b p

end YangMills.Mathematics.ManifoldDifferentialFormNormedCoordinates.Probes
