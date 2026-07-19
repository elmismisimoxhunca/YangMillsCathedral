/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Acceptance interface for completed complex projective tensor products

Mathlib currently has no general completed locally convex projective tensor product. This module
isolates the missing reusable mathematics as a typed acceptance interface rather than an arbitrary
proposition. The two factors must be Hausdorff real-locally-convex topological complex modules. A
candidate carrier must additionally be complete for an additive-compatible uniformity, receive a
jointly continuous bilinear pure-tensor map, have dense pure-tensor span, retain every pair of
nonzero factors, and supply extensions for jointly continuous bilinear maps into same-universe
complete Hausdorff locally convex targets. Uniqueness is derived from density and continuity.

The interface constructs no tensor product and introduces no axiom. Future concrete constructions
must supply every field.
-/

namespace YangMills.Mathematics

noncomputable section

universe u

/-- Data certifying that `T` is a completed complex projective tensor product of `E` and `F`.
All three carriers live in one universe, which suffices for the source-facing applications while
keeping the universal target genuinely polymorphic within that universe. -/
structure CompletedComplexProjectiveTensorProductData
    (E F T : Type u)
    [TopologicalSpace E] [AddCommGroup E] [Module ℂ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℂ F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [LocallyConvexSpace ℝ F] [T2Space F]
    [UniformSpace T] [AddCommGroup T] [Module ℂ T]
    [IsUniformAddGroup T] [IsTopologicalAddGroup T] [ContinuousSMul ℂ T]
    [LocallyConvexSpace ℝ T] [T2Space T] [CompleteSpace T] where
  /-- Algebraic bilinear pure-tensor map. -/
  pure : E →ₗ[ℂ] F →ₗ[ℂ] T
  /-- Projective continuity requires genuine joint continuity, not merely separate continuity. -/
  pure_joint_continuous : Continuous (fun p : E × F => pure p.1 p.2)
  /-- Finite linear combinations of pure tensors are dense in the completed carrier. -/
  dense_pure_span : Dense
    ((Submodule.span ℂ (Set.range (fun p : E × F => pure p.1 p.2)) : Submodule ℂ T) : Set T)
  /-- No pair of nonzero factors may collapse to the zero pure tensor. -/
  pure_ne_zero : ∀ (e : E) (f : F), e ≠ 0 → f ≠ 0 → pure e f ≠ 0
  /-- Every jointly continuous bilinear map into a complete Hausdorff locally convex target extends
  continuously linearly from the completion. -/
  lift : ∀ {G : Type u} [UniformSpace G] [AddCommGroup G] [Module ℂ G]
    [IsUniformAddGroup G] [IsTopologicalAddGroup G] [ContinuousSMul ℂ G]
    [LocallyConvexSpace ℝ G] [T2Space G] [CompleteSpace G],
    (b : E →ₗ[ℂ] F →ₗ[ℂ] G) →
      Continuous (fun p : E × F => b p.1 p.2) → T →L[ℂ] G
  /-- The extension agrees exactly on every pure tensor. -/
  lift_pure : ∀ {G : Type u} [UniformSpace G] [AddCommGroup G] [Module ℂ G]
    [IsUniformAddGroup G] [IsTopologicalAddGroup G] [ContinuousSMul ℂ G]
    [LocallyConvexSpace ℝ G] [T2Space G] [CompleteSpace G]
    (b : E →ₗ[ℂ] F →ₗ[ℂ] G) (hb : Continuous (fun p : E × F => b p.1 p.2))
    (e : E) (f : F), lift b hb (pure e f) = b e f

namespace CompletedComplexProjectiveTensorProductData

variable {E F T : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℂ E]
variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E] [T2Space E]
variable [TopologicalSpace F] [AddCommGroup F] [Module ℂ F]
variable [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [LocallyConvexSpace ℝ F] [T2Space F]
variable [UniformSpace T] [AddCommGroup T] [Module ℂ T]
variable [IsUniformAddGroup T] [IsTopologicalAddGroup T] [ContinuousSMul ℂ T]
variable [LocallyConvexSpace ℝ T] [T2Space T] [CompleteSpace T]

/-- Pure tensors vanish when the left factor vanishes. -/
@[simp]
theorem pure_zero_left (D : CompletedComplexProjectiveTensorProductData E F T) (f : F) :
    D.pure 0 f = 0 := by
  rw [map_zero]
  exact LinearMap.zero_apply f

/-- Pure tensors vanish when the right factor vanishes. -/
@[simp]
theorem pure_zero_right (D : CompletedComplexProjectiveTensorProductData E F T) (e : E) :
    D.pure e 0 = 0 := by
  exact map_zero (D.pure e)

/-- The certified noncollapse law forces the completed carrier to be nontrivial whenever both
factors exhibit nonzero elements. -/
theorem nontrivial_of_nonzero_factors
    (D : CompletedComplexProjectiveTensorProductData E F T)
    (e : E) (f : F) (he : e ≠ 0) (hf : f ≠ 0) : Nontrivial T := by
  exact ⟨⟨D.pure e f, 0, D.pure_ne_zero e f he hf⟩⟩

/-- Agreement on pure tensors uniquely determines a continuous-linear extension. This is derived
from dense pure span and target Hausdorffness rather than supplied as an independent field. -/
theorem lift_unique
    (D : CompletedComplexProjectiveTensorProductData E F T)
    {G : Type u} [UniformSpace G] [AddCommGroup G] [Module ℂ G]
    [IsUniformAddGroup G] [IsTopologicalAddGroup G] [ContinuousSMul ℂ G]
    [LocallyConvexSpace ℝ G] [T2Space G] [CompleteSpace G]
    (b : E →ₗ[ℂ] F →ₗ[ℂ] G)
    (hb : Continuous (fun p : E × F => b p.1 p.2))
    (L : T →L[ℂ] G) (hL : ∀ e f, L (D.pure e f) = b e f) :
    L = D.lift b hb := by
  apply ContinuousLinearMap.ext
  intro x
  have hpure : Set.EqOn L (D.lift b hb)
      (Set.range (fun p : E × F => D.pure p.1 p.2)) := by
    rintro _ ⟨⟨e, f⟩, rfl⟩
    rw [hL e f, D.lift_pure b hb e f]
  have hclosure := ContinuousLinearMap.eqOn_closure_span hpure
  exact hclosure (by
    rw [D.dense_pure_span.closure_eq]
    exact Set.mem_univ x)

end CompletedComplexProjectiveTensorProductData

end

end YangMills.Mathematics
