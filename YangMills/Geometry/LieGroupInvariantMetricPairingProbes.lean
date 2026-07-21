/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.LieGroupInvariantMetricPairing

/-!
# Hostile probes for the pointwise invariant group metric pairing

The probes expose exact Maurer--Cartan inversion, strict positivity, both translation conventions,
and bi-invariance. They reject a disconnected pointwise pairing but do not claim smooth
Riemannian-metric packaging.
-/

namespace YangMills.Geometry.LieGroupInvariantMetricPairing.Probes

open scoped Manifold ContDiff

noncomputable section

variable
    {E H G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [Group G] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]
    {inner : InvariantInnerProductData (I := I) (G := G)}

/-- Left Maurer--Cartan trivialization has the exact left-translation inverse. -/
theorem exact_trivialization_inverse
    (g : G) (v : TangentSpace I g) :
    mulInvariantVectorField (leftMaurerCartanApply g v) g = v :=
  mulInvariantVectorField_leftMaurerCartanApply g v

/-- The pointwise pairing uses the exact same invariant pairing and trivialization twice. -/
theorem exact_pointwise_pairing
    (g : G) (v w : TangentSpace I g) :
    lieGroupInvariantMetricInner inner g v w =
      inner.pairing (leftMaurerCartanApply g v) (leftMaurerCartanApply g w) :=
  rfl

/-- Every nonzero tangent vector has strictly positive pointwise square. -/
theorem exact_pointwise_positive
    (g : G) (v : TangentSpace I g) (hv : v ≠ 0) :
    0 < lieGroupInvariantMetricInner inner g v v :=
  lieGroupInvariantMetricInner_positive inner g v hv

/-- Fixed left translation leaves the Maurer--Cartan coefficient unchanged. -/
theorem exact_left_translation_coefficient
    (a g : G) (v : TangentSpace I g) :
    leftMaurerCartanApply (a * g) (lieGroupLeftTranslationDifferential a g v) =
      leftMaurerCartanApply g v :=
  leftMaurerCartanApply_leftTranslationDifferential a g v

/-- Fixed right translation uses exactly the inverse adjoint action. -/
theorem exact_right_translation_coefficient
    (g h : G) (v : TangentSpace I g) :
    leftMaurerCartanApply (g * h) (lieGroupRightTranslationDifferential h g v) =
      YangMills.Mathematics.lieGroupAdjoint I h⁻¹ (leftMaurerCartanApply g v) :=
  leftMaurerCartanApply_rightTranslationDifferential g h v

/-- The transported pairing is exactly left invariant. -/
theorem exact_left_invariance
    (a g : G) (v w : TangentSpace I g) :
    lieGroupInvariantMetricInner inner (a * g)
      (lieGroupLeftTranslationDifferential a g v)
      (lieGroupLeftTranslationDifferential a g w) =
    lieGroupInvariantMetricInner inner g v w :=
  lieGroupInvariantMetricInner_left_invariant inner a g v w

/-- Adjoint invariance makes the same pairing exactly right invariant. -/
theorem exact_right_invariance
    (g h : G) (v w : TangentSpace I g) :
    lieGroupInvariantMetricInner inner (g * h)
      (lieGroupRightTranslationDifferential h g v)
      (lieGroupRightTranslationDifferential h g w) =
    lieGroupInvariantMetricInner inner g v w :=
  lieGroupInvariantMetricInner_right_invariant inner g h v w

/-- A changed scalar cannot replace the exact pointwise pairing when it is distinguishable. -/
theorem changed_pointwise_pairing_blocked
    (g : G) (v w : TangentSpace I g) (wrong : ℝ)
    (different : wrong ≠
      inner.pairing (leftMaurerCartanApply g v) (leftMaurerCartanApply g w))
    (claimed : lieGroupInvariantMetricInner inner g v w = wrong) : False := by
  apply different
  rw [← claimed]
  rfl

end

end YangMills.Geometry.LieGroupInvariantMetricPairing.Probes
