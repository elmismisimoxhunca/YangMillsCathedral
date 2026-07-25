/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.FiniteConfigurationSchwartzTensor
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Consecutive differences and an anchor coordinate

Reusable finite-dimensional infrastructure identifies an `(n+1)`-point configuration with its `n`
consecutive differences and final anchor point. The inverse is constructed by reverse induction,
then promoted to a continuous linear equivalence. Pulling a Schwartz tensor through this equivalence
produces the exact test needed to compare translation-invariant full correlators with relative-
coordinate distributions.
-/

open scoped SchwartzMap

namespace YangMills.Mathematics

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Reconstruct points backwards from consecutive differences and the final anchor. -/
def reconstructFromConsecutiveDifferences
    {n : ℕ} (ξ : Fin n → E) (anchor : E) : Fin (n + 1) → E :=
  fun i => Fin.reverseInduction anchor (fun k next => ξ k + next) i

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] theorem reconstructFromConsecutiveDifferences_last
    {n : ℕ} (ξ : Fin n → E) (anchor : E) :
    reconstructFromConsecutiveDifferences E ξ anchor (Fin.last n) = anchor := by
  simp [reconstructFromConsecutiveDifferences]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
@[simp] theorem reconstructFromConsecutiveDifferences_castSucc
    {n : ℕ} (ξ : Fin n → E) (anchor : E) (i : Fin n) :
    reconstructFromConsecutiveDifferences E ξ anchor i.castSucc =
      ξ i + reconstructFromConsecutiveDifferences E ξ anchor i.succ := by
  simp [reconstructFromConsecutiveDifferences]

/-- Linear equivalence from points to consecutive differences plus the final anchor. -/
def consecutiveDifferenceAnchorLinearEquiv (n : ℕ) :
    (Fin (n + 1) → E) ≃ₗ[ℝ] ((Fin n → E) × E) where
  toFun x := (fun i => x i.castSucc - x i.succ, x (Fin.last n))
  invFun p := reconstructFromConsecutiveDifferences E p.1 p.2
  left_inv x := by
    ext i
    induction i using Fin.reverseInduction with
    | last => simp
    | cast i ih =>
        change reconstructFromConsecutiveDifferences E
          (fun k => x k.castSucc - x k.succ) (x (Fin.last n)) i.castSucc = _
        rw [reconstructFromConsecutiveDifferences_castSucc]
        change reconstructFromConsecutiveDifferences E
          (fun k => x k.castSucc - x k.succ) (x (Fin.last n)) i.succ = x i.succ at ih
        rw [ih]
        abel
  right_inv p := by
    apply Prod.ext
    · funext i
      change reconstructFromConsecutiveDifferences E p.1 p.2 i.castSucc -
        reconstructFromConsecutiveDifferences E p.1 p.2 i.succ = p.1 i
      rw [reconstructFromConsecutiveDifferences_castSucc]
      abel
    · change reconstructFromConsecutiveDifferences E p.1 p.2 (Fin.last n) = p.2
      exact reconstructFromConsecutiveDifferences_last E p.1 p.2
  map_add' x y := by
    apply Prod.ext
    · funext i
      simp
      abel
    · simp
  map_smul' c x := by
    apply Prod.ext
    · funext i
      simp [smul_sub]
    · simp

/-- The finite-dimensional difference/anchor equivalence is continuous linear. -/
noncomputable def consecutiveDifferenceAnchorContinuousLinearEquiv (n : ℕ) :
    (Fin (n + 1) → E) ≃L[ℝ] ((Fin n → E) × E) :=
  (consecutiveDifferenceAnchorLinearEquiv E n).toContinuousLinearEquiv

/-- Exact evaluation of the difference block. -/
@[simp] theorem consecutiveDifferenceAnchorContinuousLinearEquiv_fst_apply
    (n : ℕ) (x : Fin (n + 1) → E) (i : Fin n) :
    (consecutiveDifferenceAnchorContinuousLinearEquiv E n x).1 i =
      x i.castSucc - x i.succ :=
  rfl

/-- Exact evaluation of the anchor coordinate. -/
@[simp] theorem consecutiveDifferenceAnchorContinuousLinearEquiv_snd_apply
    (n : ℕ) (x : Fin (n + 1) → E) :
    (consecutiveDifferenceAnchorContinuousLinearEquiv E n x).2 = x (Fin.last n) :=
  rfl

/-- Lift a relative-coordinate Schwartz test and an anchor test to the full point configuration. -/
noncomputable def relativeAnchorSchwartzLift
    {n : ℕ} (relative : 𝓢(Fin n → E, ℂ)) (anchor : 𝓢(E, ℂ)) :
    𝓢(Fin (n + 1) → E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (consecutiveDifferenceAnchorContinuousLinearEquiv E n)
    (scalarSchwartzTensorProduct relative anchor)

/-- The lifted test is exactly the relative test on consecutive differences times the final-anchor
test. -/
@[simp] theorem relativeAnchorSchwartzLift_apply
    {n : ℕ} (relative : 𝓢(Fin n → E, ℂ)) (anchor : 𝓢(E, ℂ))
    (x : Fin (n + 1) → E) :
    relativeAnchorSchwartzLift E relative anchor x =
      relative (fun i => x i.castSucc - x i.succ) * anchor (x (Fin.last n)) :=
  rfl

end YangMills.Mathematics
