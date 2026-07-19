/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.CompletedProjectiveTensorProduct

/-!
# Hostile probes for completed projective tensor-product data

The probes reject one-factor, zero-pure, nondense, and nonunique completion surrogates. No concrete
completed tensor product is constructed.
-/

namespace YangMills.Mathematics.CompletedProjectiveTensorProduct.Probes

noncomputable section

universe u

variable {E F T : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℂ E]
variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E] [T2Space E]
variable [TopologicalSpace F] [AddCommGroup F] [Module ℂ F]
variable [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [LocallyConvexSpace ℝ F] [T2Space F]
variable [UniformSpace T] [AddCommGroup T] [Module ℂ T]
variable [IsUniformAddGroup T] [IsTopologicalAddGroup T] [ContinuousSMul ℂ T]
variable [LocallyConvexSpace ℝ T] [T2Space T] [CompleteSpace T]

/-- Each factor remains algebraically active, while either zero factor kills the pure tensor. -/
theorem exact_two_factor_laws
    (D : CompletedComplexProjectiveTensorProductData E F T)
    (e : E) (f : F) (he : e ≠ 0) (hf : f ≠ 0) :
    D.pure e f ≠ 0 ∧ D.pure 0 f = 0 ∧ D.pure e 0 = 0 :=
  ⟨D.pure_ne_zero e f he hf, D.pure_zero_left f, D.pure_zero_right e⟩

/-- The completed carrier cannot contain a disconnected complement invisible to pure tensors. -/
theorem exact_dense_pure_span
    (D : CompletedComplexProjectiveTensorProductData E F T) :
    Dense ((Submodule.span ℂ
      (Set.range (fun p : E × F => D.pure p.1 p.2)) : Submodule ℂ T) : Set T) :=
  D.dense_pure_span

/-- Every supplied lift agrees with the original bilinear map on both factors. -/
theorem exact_lift_on_pure
    (D : CompletedComplexProjectiveTensorProductData E F T)
    {G : Type u} [UniformSpace G] [AddCommGroup G] [Module ℂ G]
    [IsUniformAddGroup G] [IsTopologicalAddGroup G] [ContinuousSMul ℂ G]
    [LocallyConvexSpace ℝ G] [T2Space G] [CompleteSpace G]
    (b : E →ₗ[ℂ] F →ₗ[ℂ] G)
    (hb : Continuous (fun p : E × F => b p.1 p.2))
    (e : E) (f : F) :
    D.lift b hb (D.pure e f) = b e f :=
  D.lift_pure b hb e f

/-- A purported second extension agreeing on pure tensors must equal the certified lift. -/
theorem disconnected_extension_blocked
    (D : CompletedComplexProjectiveTensorProductData E F T)
    {G : Type u} [UniformSpace G] [AddCommGroup G] [Module ℂ G]
    [IsUniformAddGroup G] [IsTopologicalAddGroup G] [ContinuousSMul ℂ G]
    [LocallyConvexSpace ℝ G] [T2Space G] [CompleteSpace G]
    (b : E →ₗ[ℂ] F →ₗ[ℂ] G)
    (hb : Continuous (fun p : E × F => b p.1 p.2))
    (L : T →L[ℂ] G) (hL : ∀ e f, L (D.pure e f) = b e f) :
    L = D.lift b hb :=
  D.lift_unique b hb L hL

/-- Extending the certified pure-tensor map back to its own complete carrier gives exactly the
identity; no projection onto a proper completed summand is allowed. -/
theorem pure_self_lift_eq_id
    (D : CompletedComplexProjectiveTensorProductData E F T) :
    D.lift D.pure D.pure_joint_continuous = ContinuousLinearMap.id ℂ T := by
  symm
  exact D.lift_unique D.pure D.pure_joint_continuous
    (ContinuousLinearMap.id ℂ T) (fun _ _ => rfl)

end

end YangMills.Mathematics.CompletedProjectiveTensorProduct.Probes
