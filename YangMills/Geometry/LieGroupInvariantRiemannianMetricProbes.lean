/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.LieGroupInvariantRiemannianMetric

/-!
# Probes for the invariant Lie-group Riemannian metric

The probes pin the model-pairing identity, exact local Hom-bundle coordinates, smoothness, and every
field of the final Mathlib metric package. They reject replacement of the packaged pointwise form
but do not claim a Laplace--Beltrami comparison.
-/

namespace YangMills.Geometry.LieGroupInvariantRiemannianMetric.Probes

open scoped Manifold ContDiff Bundle
open Bundle

noncomputable section

universe uE uH uG

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]
    [FiniteDimensional ℝ E]
    {inner : InvariantInnerProductData (I := I) (G := G)}

omit [FiniteDimensional ℝ E] in
/-- The normed-model bridge retains the exact invariant pairing. -/
theorem exact_model_pairing (v w : E) :
    invariantPairingModel inner v w = inner.pairing v w :=
  rfl

omit [FiniteDimensional ℝ E] in
/-- The local polynomial is exactly the nested Hom-bundle coordinate form on the exact base set. -/
theorem exact_local_coordinate_reconciliation
    (center x : G) (hx : x ∈ (trivializationAt E (TangentSpace I) center).baseSet) :
    invariantMetricHomCoordinates inner center x =
      invariantMetricLocalCoordinateModel inner center x :=
  invariantMetricHomCoordinates_eq_localCoordinateModel inner center x hx

/-- Every center has the required smooth local metric coefficient model. -/
theorem exact_local_smoothness (center : G) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (invariantMetricLocalCoordinateModel inner center) center :=
  invariantMetricLocalCoordinateModel_smoothAt inner center

/-- The packaged metric uses the exact previous pointwise bilinear form. -/
theorem exact_packaged_inner
    (g : G) (v w : TangentSpace I g) :
    (lieGroupInvariantContMDiffRiemannianMetric inner).inner g v w =
      lieGroupInvariantMetricInner inner g v w :=
  rfl

/-- The packaged symmetry field is derived for the unchanged pointwise form. -/
theorem exact_packaged_symmetry
    (g : G) (v w : TangentSpace I g) :
    (lieGroupInvariantContMDiffRiemannianMetric inner).inner g v w =
      (lieGroupInvariantContMDiffRiemannianMetric inner).inner g w v :=
  (lieGroupInvariantContMDiffRiemannianMetric inner).symm g v w

/-- The packaged positivity field excludes every nonzero tangent vector from the zero square. -/
theorem exact_packaged_positive
    (g : G) (v : TangentSpace I g) (hv : v ≠ 0) :
    0 < (lieGroupInvariantContMDiffRiemannianMetric inner).inner g v v :=
  (lieGroupInvariantContMDiffRiemannianMetric inner).pos g v hv

/-- The exact packaged unit ellipsoid is von Neumann bounded. -/
theorem exact_packaged_unitEllipsoid_isVonNBounded (g : G) :
    Bornology.IsVonNBounded ℝ
      {v : TangentSpace I g |
        (lieGroupInvariantContMDiffRiemannianMetric inner).inner g v v < 1} :=
  (lieGroupInvariantContMDiffRiemannianMetric inner).isVonNBounded g

/-- The packaged dependent bilinear-form section has exact `C∞` smoothness. -/
theorem exact_packaged_section_smoothness :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun g => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) g
        ((lieGroupInvariantContMDiffRiemannianMetric inner).inner g)) :=
  (lieGroupInvariantContMDiffRiemannianMetric inner).contMDiff

/-- A disconnected pointwise form cannot replace the exact packaged metric when distinguished. -/
theorem unrelated_packaged_inner_blocked
    (g : G) (v w : TangentSpace I g) (wrong : ℝ)
    (different : wrong ≠ lieGroupInvariantMetricInner inner g v w)
    (claimed : (lieGroupInvariantContMDiffRiemannianMetric inner).inner g v w = wrong) : False := by
  apply different
  rw [← claimed]
  rfl

end

end YangMills.Geometry.LieGroupInvariantRiemannianMetric.Probes
