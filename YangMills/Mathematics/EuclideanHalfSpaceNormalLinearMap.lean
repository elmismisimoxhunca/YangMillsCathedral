/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.EuclideanHalfSpaceOutwardRay

/-!
# Linear transport of Euclidean half-space outward directions

A linear map that preserves the boundary tangent hyperplane and carries the distinguished inward
normal to a vector with strictly positive zeroth coordinate carries every strict outward direction
to a strict outward direction. The equivalence form isolates the linear algebra required of the
derivative of a manifold-with-boundary chart transition.
-/

namespace YangMills.Mathematics

open scoped Manifold

noncomputable section

/-- If a linear map preserves the boundary tangent hyperplane, its output normal coordinate is
the input normal coordinate times the image of the distinguished inward normal. -/
theorem ContinuousLinearMap.euclideanHalfSpace_zeroCoordinate_apply
    {n m : ℕ} [NeZero n] [NeZero m]
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (mapsTangent : ∀ w, w 0 = 0 → (L w) 0 = 0)
    (v : EuclideanSpace ℝ (Fin n)) :
    (L v) 0 = v 0 * (L (EuclideanSpace.single 0 1)) 0 := by
  let normal : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single 0 1
  let tangent := v - v 0 • normal
  have normal_zero : normal 0 = 1 := by
    simp [normal, EuclideanSpace.single]
  have tangent_zero : tangent 0 = 0 := by
    simp [tangent, normal_zero]
  have decomposition : v = tangent + v 0 • normal := by
    simp [tangent]
  calc
    (L v) 0 = (L (tangent + v 0 • normal)) 0 := by rw [← decomposition]
    _ = v 0 * (L normal) 0 := by
      simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        mapsTangent tangent tangent_zero, zero_add]
    _ = v 0 * (L (EuclideanSpace.single 0 1)) 0 := rfl

/-- Surjectivity upgrades a nonnegative normal multiplier to strict positivity when the boundary
tangent hyperplane is preserved. -/
theorem ContinuousLinearMap.euclideanHalfSpace_normal_pos_of_surjective
    {n m : ℕ} [NeZero n] [NeZero m]
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (mapsTangent : ∀ w, w 0 = 0 → (L w) 0 = 0)
    (normal_nonneg : 0 ≤ (L (EuclideanSpace.single 0 1)) 0)
    (surjective : Function.Surjective L) :
    0 < (L (EuclideanSpace.single 0 1)) 0 := by
  apply lt_of_le_of_ne normal_nonneg
  intro normal_zero
  obtain ⟨v, hv⟩ := surjective (EuclideanSpace.single 0 1)
  have formula :=
    ContinuousLinearMap.euclideanHalfSpace_zeroCoordinate_apply L mapsTangent v
  rw [← normal_zero, mul_zero] at formula
  have target_coordinate : (L v) 0 = 1 := by
    rw [hv]
    simp [EuclideanSpace.single]
  linarith

/-- A linear map preserving the boundary tangent hyperplane and carrying the inward normal to a
strictly inward vector carries every outward vector to an outward vector. -/
theorem ContinuousLinearMap.euclideanHalfSpace_zeroCoordinate_neg
    {n m : ℕ} [NeZero n] [NeZero m]
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (mapsTangent : ∀ w, w 0 = 0 → (L w) 0 = 0)
    (normal_pos : 0 < (L (EuclideanSpace.single 0 1)) 0)
    {v : EuclideanSpace ℝ (Fin n)} (outward : v 0 < 0) :
    (L v) 0 < 0 := by
  rw [ContinuousLinearMap.euclideanHalfSpace_zeroCoordinate_apply L mapsTangent]
  exact mul_neg_of_neg_of_pos outward normal_pos

/-- Tangent-hyperplane preservation, nonnegative inward-normal transport, and surjectivity already
force every strict outward direction to remain strict outward. -/
theorem ContinuousLinearMap.euclideanHalfSpace_zeroCoordinate_neg_of_surjective
    {n m : ℕ} [NeZero n] [NeZero m]
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (mapsTangent : ∀ w, w 0 = 0 → (L w) 0 = 0)
    (normal_nonneg : 0 ≤ (L (EuclideanSpace.single 0 1)) 0)
    (surjective : Function.Surjective L)
    {v : EuclideanSpace ℝ (Fin n)} (outward : v 0 < 0) :
    (L v) 0 < 0 :=
  ContinuousLinearMap.euclideanHalfSpace_zeroCoordinate_neg L mapsTangent
    (ContinuousLinearMap.euclideanHalfSpace_normal_pos_of_surjective L mapsTangent
      normal_nonneg surjective) outward

/-- A boundary-hyperplane-preserving linear equivalence with positive inward-normal action in both
directions preserves and reflects the strict outward half-space sign. -/
theorem ContinuousLinearEquiv.euclideanHalfSpace_zeroCoordinate_neg_iff
    {n m : ℕ} [NeZero n] [NeZero m]
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (mapsTangent : ∀ w, w 0 = 0 → (L w) 0 = 0)
    (normal_pos : 0 < (L (EuclideanSpace.single 0 1)) 0)
    (symm_mapsTangent : ∀ w, w 0 = 0 → (L.symm w) 0 = 0)
    (symm_normal_pos : 0 < (L.symm (EuclideanSpace.single 0 1)) 0)
    {v : EuclideanSpace ℝ (Fin n)} :
    (L v) 0 < 0 ↔ v 0 < 0 := by
  constructor
  · intro outward
    have transported := ContinuousLinearMap.euclideanHalfSpace_zeroCoordinate_neg
      L.symm.toContinuousLinearMap symm_mapsTangent symm_normal_pos outward
    simpa using transported
  · exact ContinuousLinearMap.euclideanHalfSpace_zeroCoordinate_neg
      L.toContinuousLinearMap mapsTangent normal_pos

/-- Under the same derivative-level hypotheses, a linear equivalence preserves and reflects the
exact two-sided half-space outward-ray predicate at boundary coordinates. -/
theorem ContinuousLinearEquiv.isEuclideanHalfSpaceOutwardRayAt_iff
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
      IsEuclideanHalfSpaceOutwardRayAt x v := by
  rw [YangMills.Mathematics.isEuclideanHalfSpaceOutwardRayAt_iff y_boundary,
    YangMills.Mathematics.isEuclideanHalfSpaceOutwardRayAt_iff x_boundary]
  exact ContinuousLinearEquiv.euclideanHalfSpace_zeroCoordinate_neg_iff L mapsTangent normal_pos
    symm_mapsTangent symm_normal_pos

end

end YangMills.Mathematics
