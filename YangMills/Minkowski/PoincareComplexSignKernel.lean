/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.PoincareTargetTopologicalGroup

/-!
# Deriving the `{±1}` kernel of an exact Poincaré double cover

Streater–Wightman printed p. 12, equations (1-14)–(1-15), states that the homogeneous matrix map
identifies exactly `A` and `-A`; printed p. 14, equation (1-23), defines the corresponding
inhomogeneous multiplication.

This module constructs the literal complex-unit subgroup `{1,-1}`. It then derives, rather than
stores, a multiplicative equivalence between that group and the exact kernel of the already selected
homomorphic two-sheet cover. Kernel centrality is also derived from order two. This remains abstract
group theory: no `SL(2,ℂ)` matrix carrier or matrix labeling of every sheet is constructed.
-/

namespace YangMills.Minkowski

noncomputable section

/-- The literal subgroup `{1,-1}` of the complex unit group. -/
def complexSignSubgroup : Subgroup ℂˣ where
  carrier := {z | z = 1 ∨ z = -1}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> simp
  inv_mem' := by
    rintro a (rfl | rfl) <;> simp

/-- Concrete complex signs as a group, not an abstract two-element indexing type. -/
abbrev ComplexSign := complexSignSubgroup

@[simp] theorem complexSign_mem_iff (z : ℂˣ) :
    z ∈ complexSignSubgroup ↔ z = 1 ∨ z = -1 :=
  Iff.rfl

/-- The negative complex sign is an actual member of the concrete subgroup. -/
def negativeComplexSign : ComplexSign := ⟨-1, Or.inr rfl⟩

@[simp] theorem negativeComplexSign_coe :
    ((negativeComplexSign : ComplexSign) : ℂˣ) = -1 :=
  rfl

@[simp] theorem negativeComplexSign_mul_self :
    negativeComplexSign * negativeComplexSign = 1 := by
  apply Subtype.ext
  norm_num

/-- The two concrete complex signs are distinct. -/
theorem negativeComplexSign_ne_one : negativeComplexSign ≠ 1 := by
  intro equality
  have unitsEquality : (-1 : ℂˣ) = 1 := congrArg Subtype.val equality
  have complexEquality : (-1 : ℂ) = 1 := congrArg Units.val unitsEquality
  norm_num at complexEquality

/-- Every group of cardinality two is multiplicatively equivalent to the literal complex signs. -/
noncomputable def mulEquivComplexSignOfNatCardTwo
    {K : Type*} [Group K] (card_eq_two : Nat.card K = 2) : K ≃* ComplexSign := by
  classical
  have unique_nonidentity : ∃! k : K, k ≠ 1 :=
    (Nat.card_eq_two_iff' (1 : K)).mp card_eq_two
  let negative : K := unique_nonidentity.choose
  have negative_ne_one : negative ≠ 1 := unique_nonidentity.choose_spec.1
  have eq_negative {k : K} (hk : k ≠ 1) : k = negative :=
    unique_nonidentity.unique hk negative_ne_one
  have negative_mul_self : negative * negative = 1 := by
    by_contra not_one
    have equals_negative : negative * negative = negative := eq_negative not_one
    have negative_eq_one : negative = 1 := by
      apply mul_right_cancel (b := negative)
      simpa using equals_negative
    exact negative_ne_one negative_eq_one
  let toSign : K → ComplexSign := fun k => if k = 1 then 1 else negativeComplexSign
  have toSign_mul (a b : K) : toSign (a * b) = toSign a * toSign b := by
    by_cases ha : a = 1
    · subst a
      simp [toSign]
    by_cases hb : b = 1
    · subst b
      simp [toSign]
    have a_eq : a = negative := eq_negative ha
    have b_eq : b = negative := eq_negative hb
    subst a
    subst b
    simp [toSign, negative_ne_one, negative_mul_self]
  let hom : K →* ComplexSign := MonoidHom.mk' toSign toSign_mul
  apply MulEquiv.ofBijective hom
  constructor
  · intro a b equality
    by_cases ha : a = 1
    · subst a
      by_cases hb : b = 1
      · exact hb.symm
      · have signs_equal : (1 : ℂˣ) = -1 := by
          simpa [hom, toSign, hb] using congrArg Subtype.val equality
        have impossible : (1 : ℂ) = -1 := congrArg Units.val signs_equal
        norm_num at impossible
    · by_cases hb : b = 1
      · subst b
        have signs_equal : (-1 : ℂˣ) = 1 := by
          simpa [hom, toSign, ha] using congrArg Subtype.val equality
        have impossible : (-1 : ℂ) = 1 := congrArg Units.val signs_equal
        norm_num at impossible
      · exact (eq_negative ha).trans (eq_negative hb).symm
  · intro sign
    rcases sign.property with positive | negativeSign
    · refine ⟨1, ?_⟩
      apply Subtype.ext
      simp [hom, toSign, positive]
    · refine ⟨negative, ?_⟩
      apply Subtype.ext
      simp [hom, toSign, negative_ne_one, negativeSign]

/-- Kernel of the exact projection under the supplied named affine target group law. -/
noncomputable def properOrthochronousPoincareProjectionKernel
    (d : EuclideanDimension)
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (cover : ProperOrthochronousPoincareDoubleCoverData d G) : Subgroup G := by
  letI : Group (ProperOrthochronousPoincareTransformation d) := targetGroup.group
  exact (targetGroup.projectionMonoidHom cover).ker

/-- The homomorphism kernel is equivalent to the identity fiber used by the double-cover datum. -/
noncomputable def projectionKernelEquivIdentityFiber
    (d : EuclideanDimension)
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (cover : ProperOrthochronousPoincareDoubleCoverData d G) :
    properOrthochronousPoincareProjectionKernel d targetGroup cover ≃
      (cover.projection ⁻¹'
        ({ProperOrthochronousPoincareTransformation.identity d} : Set _)) where
  toFun k := by
    refine ⟨k, ?_⟩
    change cover.projection k = ProperOrthochronousPoincareTransformation.identity d
    have property := k.property
    change cover.projection k = @One.one _ targetGroup.group.toOne at property
    simpa [targetGroup.one_eq_identity] using property
  invFun k := by
    refine ⟨k, ?_⟩
    change cover.projection k = @One.one _ targetGroup.group.toOne
    have property : cover.projection k =
        ProperOrthochronousPoincareTransformation.identity d := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using k.property
    simpa [targetGroup.one_eq_identity] using property
  left_inv _ := rfl
  right_inv _ := rfl

/-- The exact projection kernel has cardinality two, derived from the exact identity fiber. -/
theorem projectionKernel_natCard_eq_two
    (d : EuclideanDimension)
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (cover : ProperOrthochronousPoincareDoubleCoverData d G) :
    Nat.card (properOrthochronousPoincareProjectionKernel d targetGroup cover) = 2 := by
  rw [Nat.card_congr (projectionKernelEquivIdentityFiber d targetGroup cover)]
  rw [Nat.card_congr
    (cover.fiberEquivFinTwo (ProperOrthochronousPoincareTransformation.identity d))]
  exact Nat.card_fin 2

/-- The exact projection kernel is multiplicatively the literal complex sign group. This is derived
from the existing two-sheet homomorphic cover, not added as a redundant acceptance field. -/
noncomputable def projectionKernelMulEquivComplexSign
    (d : EuclideanDimension)
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (cover : ProperOrthochronousPoincareDoubleCoverData d G) :
    properOrthochronousPoincareProjectionKernel d targetGroup cover ≃* ComplexSign :=
  mulEquivComplexSignOfNatCardTwo
    (projectionKernel_natCard_eq_two d targetGroup cover)

/-- Every element of the exact order-two projection kernel is central in the lift group. -/
theorem projectionKernel_central
    (d : EuclideanDimension)
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (cover : ProperOrthochronousPoincareDoubleCoverData d G)
    (k : properOrthochronousPoincareProjectionKernel d targetGroup cover) (g : G) :
    (k : G) * g = g * (k : G) := by
  letI : Group (ProperOrthochronousPoincareTransformation d) := targetGroup.group
  let K := properOrthochronousPoincareProjectionKernel d targetGroup cover
  let conjugate : K :=
    ⟨g * (k : G) * g⁻¹, by
      change targetGroup.projectionMonoidHom cover (g * (k : G) * g⁻¹) = 1
      have kernelProperty := k.property
      change targetGroup.projectionMonoidHom cover (k : G) = 1 at kernelProperty
      rw [map_mul, map_mul, map_inv, kernelProperty]
      simp⟩
  -- Conjugation preserves the unique nonidentity kernel element; the identity case is immediate.
  by_cases hk : (k : G) = 1
  · simp [hk]
  have conjugate_ne_one : conjugate ≠ 1 := by
    intro equality
    have valueEquality : g * (k : G) * g⁻¹ = 1 := congrArg Subtype.val equality
    have recovered := congrArg (fun x : G => g⁻¹ * x * g) valueEquality
    have : (k : G) = 1 := by
      simpa [mul_assoc] using recovered
    exact hk this
  have conjugate_eq_k : conjugate = k := by
    have unique_nonidentity : ∃! x : K, x ≠ 1 :=
      (Nat.card_eq_two_iff' (1 : K)).mp
        (projectionKernel_natCard_eq_two d targetGroup cover)
    have k_ne_one : k ≠ 1 := by
      intro equality
      exact hk (congrArg Subtype.val equality)
    exact unique_nonidentity.unique conjugate_ne_one k_ne_one
  have valueConjugate : g * (k : G) * g⁻¹ = (k : G) :=
    congrArg Subtype.val conjugate_eq_k
  symm
  calc
    g * (k : G) = (g * (k : G) * g⁻¹) * g := by simp
    _ = (k : G) * g := by rw [valueConjugate]

/-- The exact lift-kernel element corresponding to the negative complex sign. -/
noncomputable def negativeProjectionKernelElement
    (d : EuclideanDimension)
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (cover : ProperOrthochronousPoincareDoubleCoverData d G) :
    properOrthochronousPoincareProjectionKernel d targetGroup cover :=
  (projectionKernelMulEquivComplexSign d targetGroup cover).symm negativeComplexSign

/-- The negative kernel element projects to the exact affine identity. -/
theorem negativeProjectionKernelElement_mem_kernel
    (d : EuclideanDimension)
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (cover : ProperOrthochronousPoincareDoubleCoverData d G) :
    cover.projection (negativeProjectionKernelElement d targetGroup cover : G) =
      ProperOrthochronousPoincareTransformation.identity d := by
  have property := (negativeProjectionKernelElement d targetGroup cover).property
  change cover.projection (negativeProjectionKernelElement d targetGroup cover : G) =
    @One.one _ targetGroup.group.toOne at property
  simpa [targetGroup.one_eq_identity] using property

/-- The negative kernel element is not the lift-group identity. -/
theorem negativeProjectionKernelElement_ne_one
    (d : EuclideanDimension)
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (cover : ProperOrthochronousPoincareDoubleCoverData d G) :
    negativeProjectionKernelElement d targetGroup cover ≠ 1 := by
  intro equality
  have mapped := congrArg (projectionKernelMulEquivComplexSign d targetGroup cover) equality
  have signEquality : negativeComplexSign = 1 := by
    simpa [negativeProjectionKernelElement] using mapped
  exact negativeComplexSign_ne_one signEquality

/-- Multiplying any lift by the derived negative kernel element stays over the same affine target. -/
theorem projection_mul_negativeKernelElement
    (d : EuclideanDimension)
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (cover : ProperOrthochronousPoincareDoubleCoverData d G) (g : G) :
    cover.projection
        (g * (negativeProjectionKernelElement d targetGroup cover : G)) =
      cover.projection g := by
  letI : Group (ProperOrthochronousPoincareTransformation d) := targetGroup.group
  change targetGroup.projectionMonoidHom cover
      (g * (negativeProjectionKernelElement d targetGroup cover : G)) =
    targetGroup.projectionMonoidHom cover g
  rw [map_mul]
  have kernelProperty := (negativeProjectionKernelElement d targetGroup cover).property
  change targetGroup.projectionMonoidHom cover
      (negativeProjectionKernelElement d targetGroup cover : G) = 1 at kernelProperty
  rw [kernelProperty, mul_one]

/-- The negative-sign partner of every lift is genuinely distinct. -/
theorem mul_negativeKernelElement_ne
    (d : EuclideanDimension)
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (cover : ProperOrthochronousPoincareDoubleCoverData d G) (g : G) :
    g * (negativeProjectionKernelElement d targetGroup cover : G) ≠ g := by
  intro equality
  have kernelOne : (negativeProjectionKernelElement d targetGroup cover : G) = 1 := by
    apply mul_left_cancel (a := g)
    simpa using equality
  exact negativeProjectionKernelElement_ne_one d targetGroup cover
    (Subtype.ext kernelOne)

/-- Relative to any selected lift `g`, every lift over the same affine target is exactly `g` or its
negative-sign partner. This labels a fiber only after choosing `g`; it is not a global matrix-sheet
labeling. -/
theorem eq_or_eq_mul_negativeKernelElement_of_projection_eq
    (d : EuclideanDimension)
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (cover : ProperOrthochronousPoincareDoubleCoverData d G)
    {g h : G} (projection_eq : cover.projection h = cover.projection g) :
    h = g ∨ h = g * (negativeProjectionKernelElement d targetGroup cover : G) := by
  letI : Group (ProperOrthochronousPoincareTransformation d) := targetGroup.group
  let quotient : properOrthochronousPoincareProjectionKernel d targetGroup cover :=
    ⟨g⁻¹ * h, by
      change targetGroup.projectionMonoidHom cover (g⁻¹ * h) = 1
      rw [map_mul, map_inv]
      change (cover.projection g)⁻¹ * cover.projection h = 1
      rw [projection_eq]
      simp⟩
  let signs := projectionKernelMulEquivComplexSign d targetGroup cover
  rcases (signs quotient).property with positive | negative
  · left
    have signs_eq_one : signs quotient = 1 := by
      apply Subtype.ext
      exact positive
    have quotient_eq_one : quotient = 1 := signs.injective (by simpa using signs_eq_one)
    have value_eq : g⁻¹ * h = 1 := congrArg Subtype.val quotient_eq_one
    calc
      h = g * (g⁻¹ * h) := by simp
      _ = g := by rw [value_eq, mul_one]
  · right
    have signs_eq_negative : signs quotient = negativeComplexSign := by
      apply Subtype.ext
      exact negative
    have negative_image :
        signs (negativeProjectionKernelElement d targetGroup cover) =
          negativeComplexSign := by
      simp [signs, negativeProjectionKernelElement]
    have quotient_eq_negative :
        quotient = negativeProjectionKernelElement d targetGroup cover :=
      signs.injective (signs_eq_negative.trans negative_image.symm)
    have value_eq : g⁻¹ * h =
        (negativeProjectionKernelElement d targetGroup cover : G) :=
      congrArg Subtype.val quotient_eq_negative
    calc
      h = g * (g⁻¹ * h) := by simp
      _ = g * (negativeProjectionKernelElement d targetGroup cover : G) := by rw [value_eq]

end

end YangMills.Minkowski
