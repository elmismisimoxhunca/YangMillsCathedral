/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.EuclideanHalfSpaceNormalLinearMap
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Boundary derivatives of locally half-space-valued maps

If a differentiable map is locally valued in a Euclidean half-space and its base point maps to the
boundary, the target normal coordinate has a local minimum. Tangent-cone Fermat theorems then force
bidirectional source tangent directions into the target boundary hyperplane and give a nonnegative
normal derivative on every one-sided source tangent direction.

This is the nonlinear calculus step needed before applying the strict linear transport results for
manifold-with-boundary coordinate changes. Strict positivity still requires invertibility together
with enough bidirectional tangent directions.
-/

namespace YangMills.Mathematics

open Set Filter
open scoped Topology

noncomputable section

/-- Local preservation of the target half-space at a boundary image makes its normal coordinate a
local minimum. -/
theorem euclideanHalfSpace_normalCoordinate_isLocalMinOn
    {n m : ℕ} [NeZero n] [NeZero m]
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    (output_boundary : (f x) 0 = 0)
    (maps_halfSpace : ∀ᶠ z in 𝓝[s] x, 0 ≤ (f z) 0) :
    IsLocalMinOn (fun z => (f z) 0) s x := by
  filter_upwards [maps_halfSpace] with z hz
  simpa [output_boundary] using hz

/-- The within derivative of a locally half-space-valued map at a boundary image sends every
bidirectional source tangent-cone vector to the target boundary tangent hyperplane. -/
theorem HasFDerivWithinAt.euclideanHalfSpace_mapsTangent
    {n m : ℕ} [NeZero n] [NeZero m]
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin n))} {x w : EuclideanSpace ℝ (Fin n)}
    (hf : HasFDerivWithinAt f f' s x)
    (output_boundary : (f x) 0 = 0)
    (maps_halfSpace : ∀ᶠ z in 𝓝[s] x, 0 ≤ (f z) 0)
    (tangent : w ∈ posTangentConeAt s x) (neg_tangent : -w ∈ posTangentConeAt s x) :
    (f' w) 0 = 0 := by
  let proj : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin m => ℝ) 0
  have hcomp : HasFDerivWithinAt (fun z => (f z) 0) (proj.comp f') s x := by
    simpa [proj, Function.comp_def] using proj.hasFDerivAt.comp_hasFDerivWithinAt x hf
  have hmin := euclideanHalfSpace_normalCoordinate_isLocalMinOn output_boundary maps_halfSpace
  have zero := hmin.hasFDerivWithinAt_eq_zero hcomp tangent neg_tangent
  simpa [proj] using zero

/-- Every one-sided source tangent-cone vector has nonnegative target normal derivative. -/
theorem HasFDerivWithinAt.euclideanHalfSpace_normal_nonneg
    {n m : ℕ} [NeZero n] [NeZero m]
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin n))} {x w : EuclideanSpace ℝ (Fin n)}
    (hf : HasFDerivWithinAt f f' s x)
    (output_boundary : (f x) 0 = 0)
    (maps_halfSpace : ∀ᶠ z in 𝓝[s] x, 0 ≤ (f z) 0)
    (inward : w ∈ posTangentConeAt s x) :
    0 ≤ (f' w) 0 := by
  let proj : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin m => ℝ) 0
  have hcomp : HasFDerivWithinAt (fun z => (f z) 0) (proj.comp f') s x := by
    simpa [proj, Function.comp_def] using proj.hasFDerivAt.comp_hasFDerivWithinAt x hf
  have hmin := euclideanHalfSpace_normalCoordinate_isLocalMinOn output_boundary maps_halfSpace
  have nonneg := hmin.hasFDerivWithinAt_nonneg hcomp inward
  simpa [proj] using nonneg

end

end YangMills.Mathematics
