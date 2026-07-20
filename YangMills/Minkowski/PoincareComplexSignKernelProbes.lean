/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.PoincareComplexSignKernel

/-!
# Hostile probes for the derived Poincaré `{±1}` kernel

These probes derive literal-sign structure and centrality from the exact homomorphic two-sheet
cover. No extra kernel witness, cover, or matrix realization is supplied.
-/

namespace YangMills.Minkowski.PoincareComplexSignKernel.Probes

noncomputable section

/-- The concrete sign carrier contains exactly complex-unit `1` or `-1`. -/
theorem exact_complex_sign_carrier (z : ComplexSign) :
    (z : ℂˣ) = 1 ∨ (z : ℂˣ) = -1 :=
  z.property

/-- Its negative sign is definitionally `-1` and differs from its identity. -/
theorem exact_negative_complex_sign :
    ((negativeComplexSign : ComplexSign) : ℂˣ) = -1 ∧ negativeComplexSign ≠ 1 :=
  ⟨rfl, negativeComplexSign_ne_one⟩

variable
    {d : EuclideanDimension}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (targetGroup : ProperOrthochronousPoincareTargetGroupData d)
    (cover : ProperOrthochronousPoincareDoubleCoverData d G)

/-- The exact projection kernel has two elements because it is the identity fiber. -/
theorem exact_kernel_cardinality :
    Nat.card (properOrthochronousPoincareProjectionKernel d targetGroup cover) = 2 :=
  projectionKernel_natCard_eq_two d targetGroup cover

/-- The exact group-theoretic kernel, not an arbitrary fiber, is derived equivalent to signs. -/
theorem exact_kernel_equiv :
    Nonempty (properOrthochronousPoincareProjectionKernel d targetGroup cover ≃* ComplexSign) :=
  ⟨projectionKernelMulEquivComplexSign d targetGroup cover⟩

/-- The derived negative sign selects a nonidentity lift of the exact affine identity. -/
theorem exact_negative_kernel_element :
    cover.projection (negativeProjectionKernelElement d targetGroup cover : G) =
        ProperOrthochronousPoincareTransformation.identity d ∧
      negativeProjectionKernelElement d targetGroup cover ≠ 1 :=
  ⟨negativeProjectionKernelElement_mem_kernel d targetGroup cover,
    negativeProjectionKernelElement_ne_one d targetGroup cover⟩

/-- Every kernel element is centrally forced by the exact order-two homomorphic cover. -/
theorem exact_whole_kernel_central
    (k : properOrthochronousPoincareProjectionKernel d targetGroup cover) (g : G) :
    (k : G) * g = g * (k : G) :=
  projectionKernel_central d targetGroup cover k g

end

end YangMills.Minkowski.PoincareComplexSignKernel.Probes
