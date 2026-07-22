/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.EuclideanHalfSpaceNormalLinearMap

/-!
# Hostile probes for linear transport of half-space outward directions
-/

namespace YangMills.Mathematics.EuclideanHalfSpaceNormalLinearMap.Probes

noncomputable section

/-- The output normal coordinate is forced by the input coordinate and the image of the
 distinguished inward normal; no unrelated output coordinate may be substituted. -/
theorem exact_normal_coordinate_formula
    {n m : ℕ} [NeZero n] [NeZero m]
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (mapsTangent : ∀ w, w 0 = 0 → (L w) 0 = 0)
    (v : EuclideanSpace ℝ (Fin n)) :
    (L v) 0 = v 0 * (L (EuclideanSpace.single 0 1)) 0 :=
  ContinuousLinearMap.euclideanHalfSpace_zeroCoordinate_apply L mapsTangent v

/-- A claimed nonnegative image of a strict outward vector contradicts exact positive-normal
transport. -/
theorem nonnegative_outward_image_blocked
    {n m : ℕ} [NeZero n] [NeZero m]
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (mapsTangent : ∀ w, w 0 = 0 → (L w) 0 = 0)
    (normal_pos : 0 < (L (EuclideanSpace.single 0 1)) 0)
    {v : EuclideanSpace ℝ (Fin n)} (outward : v 0 < 0)
    (wrongSign : 0 ≤ (L v) 0) : False :=
  (not_lt_of_ge wrongSign)
    (ContinuousLinearMap.euclideanHalfSpace_zeroCoordinate_neg
      L mapsTangent normal_pos outward)

/-- A surjective tangent-hyperplane-preserving map with nonnegative normal multiplier cannot have
zero normal multiplier. -/
theorem zero_normal_multiplier_blocked
    {n m : ℕ} [NeZero n] [NeZero m]
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (mapsTangent : ∀ w, w 0 = 0 → (L w) 0 = 0)
    (normal_nonneg : 0 ≤ (L (EuclideanSpace.single 0 1)) 0)
    (surjective : Function.Surjective L)
    (wrongZero : (L (EuclideanSpace.single 0 1)) 0 = 0) : False :=
  (ne_of_gt (ContinuousLinearMap.euclideanHalfSpace_normal_pos_of_surjective
    L mapsTangent normal_nonneg surjective)) wrongZero

/-- Nonnegative normal transport plus surjectivity suffices to preserve strict outwardness. -/
theorem exact_surjective_outward_transport
    {n m : ℕ} [NeZero n] [NeZero m]
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (mapsTangent : ∀ w, w 0 = 0 → (L w) 0 = 0)
    (normal_nonneg : 0 ≤ (L (EuclideanSpace.single 0 1)) 0)
    (surjective : Function.Surjective L)
    {v : EuclideanSpace ℝ (Fin n)} (outward : v 0 < 0) :
    (L v) 0 < 0 :=
  ContinuousLinearMap.euclideanHalfSpace_zeroCoordinate_neg_of_surjective
    L mapsTangent normal_nonneg surjective outward

/-- Under the corresponding hypotheses in both directions, an exact linear equivalence preserves
and reflects—not merely preserves—the outward sign. -/
theorem exact_outward_sign_equivalence
    {n m : ℕ} [NeZero n] [NeZero m]
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (mapsTangent : ∀ w, w 0 = 0 → (L w) 0 = 0)
    (normal_pos : 0 < (L (EuclideanSpace.single 0 1)) 0)
    (symm_mapsTangent : ∀ w, w 0 = 0 → (L.symm w) 0 = 0)
    (symm_normal_pos : 0 < (L.symm (EuclideanSpace.single 0 1)) 0)
    {v : EuclideanSpace ℝ (Fin n)} :
    (L v) 0 < 0 ↔ v 0 < 0 :=
  ContinuousLinearEquiv.euclideanHalfSpace_zeroCoordinate_neg_iff L mapsTangent normal_pos
    symm_mapsTangent symm_normal_pos

/-- The same exact hypotheses preserve and reflect the full two-sided outward-ray predicate, not
only a disconnected scalar inequality. -/
theorem exact_outward_ray_equivalence
    {n m : ℕ} [NeZero n] [NeZero m]
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (mapsTangent : ∀ w, w 0 = 0 → (L w) 0 = 0)
    (normal_pos : 0 < (L (EuclideanSpace.single 0 1)) 0)
    (symm_mapsTangent : ∀ w, w 0 = 0 → (L.symm w) 0 = 0)
    (symm_normal_pos : 0 < (L.symm (EuclideanSpace.single 0 1)) 0)
    {x : EuclideanSpace ℝ (Fin n)} {y : EuclideanSpace ℝ (Fin m)}
    (x_boundary : x 0 = 0) (y_boundary : y 0 = 0)
    {v : EuclideanSpace ℝ (Fin n)} :
    IsEuclideanHalfSpaceOutwardRayAt y (L v) ↔
      IsEuclideanHalfSpaceOutwardRayAt x v :=
  ContinuousLinearEquiv.isEuclideanHalfSpaceOutwardRayAt_iff L mapsTangent normal_pos
    symm_mapsTangent symm_normal_pos x_boundary y_boundary

/-- Replacing the exact normal multiplier by a different scalar is detected whenever the input has
nonzero normal coordinate. -/
theorem changed_normal_multiplier_blocked
    {n m : ℕ} [NeZero n] [NeZero m]
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (mapsTangent : ∀ w, w 0 = 0 → (L w) 0 = 0)
    (v : EuclideanSpace ℝ (Fin n)) (changed : ℝ)
    (input_nonzero : v 0 ≠ 0)
    (multiplier_changed : changed ≠ (L (EuclideanSpace.single 0 1)) 0)
    (claimed : (L v) 0 = v 0 * changed) : False := by
  have exact := ContinuousLinearMap.euclideanHalfSpace_zeroCoordinate_apply L mapsTangent v
  apply multiplier_changed
  apply (mul_left_cancel₀ input_nonzero)
  rw [← exact, claimed]

end

end YangMills.Mathematics.EuclideanHalfSpaceNormalLinearMap.Probes
