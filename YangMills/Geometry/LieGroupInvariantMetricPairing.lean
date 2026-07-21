/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionAffineGaugeTransformation
import YangMills.Geometry.InvariantInnerProduct

/-!
# Pointwise bi-invariant metric pairing on a Lie group

The left Maurer--Cartan trivialization transports each tangent fiber back to the identity tangent
Lie algebra. Composing both arguments of the exact invariant inner product with that trivialization
constructs a pointwise continuous bilinear pairing. Its symmetry and strict positivity are derived,
and translation naturality proves left and right invariance; right invariance uses the exact
`Ad(h⁻¹)` convention and the stored adjoint invariance of the same pairing.

This is the algebraic/pointwise part of the invariant-pairing-to-manifold-metric bridge. It does not
yet prove the dependent bilinear-form section smooth or its unit ellipsoids von Neumann bounded, so
it does not construct a Mathlib `ContMDiffRiemannianMetric` or identify a Laplace--Beltrami operator.
-/

namespace YangMills.Geometry

open Function
open scoped Manifold ContDiff

universe uE uH uG

noncomputable section

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]

/-- Differential of fixed left translation, with exact dependent tangent endpoints. -/
def lieGroupLeftTranslationDifferential (a g : G) :
    TangentSpace I g →L[ℝ] TangentSpace I (a * g) :=
  mfderiv I I (lieGroupLeftTranslation a) g

/-- Differential of fixed right translation, with exact dependent tangent endpoints. -/
def lieGroupRightTranslationDifferential (h g : G) :
    TangentSpace I g →L[ℝ] TangentSpace I (g * h) :=
  mfderiv I I (fun x : G => x * h) g

/-- Left translation by `g` is the pointwise inverse of left Maurer--Cartan trivialization. -/
@[simp]
theorem mulInvariantVectorField_leftMaurerCartanApply
    (g : G) (v : TangentSpace I g) :
    mulInvariantVectorField (leftMaurerCartanApply g v) g = v := by
  let forward : G → G := fun y => g * y
  let backward : G → G := fun y => g⁻¹ * y
  have hcomp := mfderiv_comp (I := I) (I' := I) (I'' := I)
    (f := backward) (g := forward) g
    ((lieGroupLeftTranslation_smooth (IG := I) g).mdifferentiableAt (by simp))
    ((lieGroupLeftTranslation_smooth (IG := I) g⁻¹).mdifferentiableAt (by simp))
  have hfun : forward ∘ backward = id := by
    funext y
    simp [backward, forward]
  rw [hfun, mfderiv_id] at hcomp
  have happ := congrArg (fun L => L v) hcomp
  change v = mfderiv I I forward (backward g)
    (mfderiv I I backward g v) at happ
  change mfderiv I I forward 1 (mfderiv I I backward g v) = v
  rw [show backward g = 1 by simp [backward]] at happ
  exact happ.symm

/-- Left Maurer--Cartan trivialization is injective on every exact tangent fiber. -/
theorem leftMaurerCartanApply_injective (g : G) :
    Function.Injective (leftMaurerCartanApply (IG := I) (G := G) g) := by
  intro v w equality
  rw [← mulInvariantVectorField_leftMaurerCartanApply g v,
    ← mulInvariantVectorField_leftMaurerCartanApply g w, equality]

/-- Pointwise continuous bilinear pairing obtained from the exact invariant pairing by left
Maurer--Cartan trivialization. -/
noncomputable def lieGroupInvariantMetricInner
    (inner : InvariantInnerProductData (I := I) (G := G)) (g : G) :
    TangentSpace I g →L[ℝ] TangentSpace I g →L[ℝ] ℝ :=
  let trivialization := mfderiv I I (lieGroupLeftTranslation g⁻¹) g
  (ContinuousLinearMap.precomp ℝ trivialization).comp
    (inner.pairing.comp trivialization)

@[simp]
theorem lieGroupInvariantMetricInner_apply
    (inner : InvariantInnerProductData (I := I) (G := G))
    (g : G) (v w : TangentSpace I g) :
    lieGroupInvariantMetricInner inner g v w =
      inner.pairing (leftMaurerCartanApply g v) (leftMaurerCartanApply g w) :=
  rfl

/-- The transported pointwise pairing is symmetric. -/
theorem lieGroupInvariantMetricInner_symmetric
    (inner : InvariantInnerProductData (I := I) (G := G))
    (g : G) (v w : TangentSpace I g) :
    lieGroupInvariantMetricInner inner g v w =
      lieGroupInvariantMetricInner inner g w v := by
  simp only [lieGroupInvariantMetricInner_apply]
  exact inner.symmetric _ _

/-- The transported pointwise pairing is strictly positive on every nonzero tangent vector. -/
theorem lieGroupInvariantMetricInner_positive
    (inner : InvariantInnerProductData (I := I) (G := G))
    (g : G) (v : TangentSpace I g) (hv : v ≠ 0) :
    0 < lieGroupInvariantMetricInner inner g v v := by
  rw [lieGroupInvariantMetricInner_apply]
  apply inner.positive
  intro hzero
  apply hv
  rw [← mulInvariantVectorField_leftMaurerCartanApply g v, hzero]
  exact map_zero _

/-- Left Maurer--Cartan trivialization is unchanged by fixed left translation. -/
@[simp]
theorem leftMaurerCartanApply_leftTranslationDifferential
    (a g : G) (v : TangentSpace I g) :
    leftMaurerCartanApply (a * g) (lieGroupLeftTranslationDifferential a g v) =
      leftMaurerCartanApply g v := by
  let forward : G → G := lieGroupLeftTranslation a
  let targetBackward : G → G := lieGroupLeftTranslation (a * g)⁻¹
  let sourceBackward : G → G := lieGroupLeftTranslation g⁻¹
  have hcomp := mfderiv_comp (I := I) (I' := I) (I'' := I)
    (f := forward) (g := targetBackward) g
    ((lieGroupLeftTranslation_smooth (IG := I) (a * g)⁻¹).mdifferentiableAt (by simp))
    ((lieGroupLeftTranslation_smooth (IG := I) a).mdifferentiableAt (by simp))
  have hfun : targetBackward ∘ forward = sourceBackward := by
    funext x
    simp [targetBackward, forward, sourceBackward, lieGroupLeftTranslation]
  rw [hfun] at hcomp
  have happ := congrArg (fun L => L v) hcomp
  change mfderiv I I sourceBackward g v =
    mfderiv I I targetBackward (forward g) (mfderiv I I forward g v) at happ
  change leftMaurerCartanApply g v =
    leftMaurerCartanApply (a * g) (lieGroupLeftTranslationDifferential a g v) at happ
  simpa [forward, lieGroupLeftTranslation] using happ.symm

/-- Under fixed right translation, left Maurer--Cartan coefficients transform by `Ad(h⁻¹)`. -/
@[simp]
theorem leftMaurerCartanApply_rightTranslationDifferential
    (g h : G) (v : TangentSpace I g) :
    leftMaurerCartanApply (g * h) (lieGroupRightTranslationDifferential h g v) =
      YangMills.Mathematics.lieGroupAdjoint I h⁻¹ (leftMaurerCartanApply g v) := by
  let right : G → G := fun x => x * h
  let targetBackward : G → G := lieGroupLeftTranslation (g * h)⁻¹
  let sourceBackward : G → G := lieGroupLeftTranslation g⁻¹
  let conjugation : G → G := YangMills.Mathematics.lieGroupConjugation h⁻¹
  have hleftChain := mfderiv_comp (I := I) (I' := I) (I'' := I)
    (f := right) (g := targetBackward) g
    ((lieGroupLeftTranslation_smooth (IG := I) (g * h)⁻¹).mdifferentiableAt (by simp))
    ((contMDiff_mul_right (I := I) (n := ∞) (a := h)).mdifferentiableAt (by simp))
  have hrightChain := mfderiv_comp (I := I) (I' := I) (I'' := I)
    (f := sourceBackward) (g := conjugation) g
    ((YangMills.Mathematics.lieGroupConjugation_smooth I h⁻¹).mdifferentiableAt (by simp))
    ((lieGroupLeftTranslation_smooth (IG := I) g⁻¹).mdifferentiableAt (by simp))
  have hsource : sourceBackward g = 1 := by
    simp [sourceBackward, lieGroupLeftTranslation]
  rw [hsource] at hrightChain
  have hfun : targetBackward ∘ right = conjugation ∘ sourceBackward := by
    funext x
    simp [targetBackward, right, conjugation, sourceBackward, lieGroupLeftTranslation,
      YangMills.Mathematics.lieGroupConjugation]
    group
  rw [hfun] at hleftChain
  rw [hrightChain] at hleftChain
  have happ := congrArg (fun L => L v) hleftChain
  change leftMaurerCartanApply (g * h) (lieGroupRightTranslationDifferential h g v) =
    YangMills.Mathematics.lieGroupAdjoint I h⁻¹ (leftMaurerCartanApply g v)
  convert happ.symm using 1
  · simp [sourceBackward, conjugation, lieGroupLeftTranslation,
      YangMills.Mathematics.lieGroupConjugation]
  · rfl
  · rfl

/-- The pointwise pairing is invariant under every fixed left translation. -/
theorem lieGroupInvariantMetricInner_left_invariant
    (inner : InvariantInnerProductData (I := I) (G := G))
    (a g : G) (v w : TangentSpace I g) :
    lieGroupInvariantMetricInner inner (a * g)
      (lieGroupLeftTranslationDifferential a g v)
      (lieGroupLeftTranslationDifferential a g w) =
    lieGroupInvariantMetricInner inner g v w := by
  simp

/-- Adjoint invariance upgrades the pointwise pairing to right invariance. -/
theorem lieGroupInvariantMetricInner_right_invariant
    (inner : InvariantInnerProductData (I := I) (G := G))
    (g h : G) (v w : TangentSpace I g) :
    lieGroupInvariantMetricInner inner (g * h)
      (lieGroupRightTranslationDifferential h g v)
      (lieGroupRightTranslationDifferential h g w) =
    lieGroupInvariantMetricInner inner g v w := by
  simp only [lieGroupInvariantMetricInner_apply,
    leftMaurerCartanApply_rightTranslationDifferential]
  exact inner.adjoint_invariant h⁻¹ _ _

end

end YangMills.Geometry
