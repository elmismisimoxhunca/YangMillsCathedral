/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactMatrixRepresentationTensorProduct

/-!
# Hostile probes for finite matrix tensor products
-/

namespace YangMills
namespace Mathematics
namespace CompactMatrixRepresentationTensorProduct
namespace Probes

open scoped MonoidAlgebra

noncomputable section

universe uG

variable {G : Type uG} [Group G]

/-- Literal product-basis coordinates have the exact coefficient-product formula. -/
theorem exact_kronecker_coefficient
    {n m : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (g : G) (i j : Fin n) (k l : Fin m) :
    matrixRepresentationKroneckerTensor ρ σ g (i, k) (j, l) =
      ρ g i j * σ g k l :=
  matrixRepresentationKroneckerTensor_apply ρ σ g i j k l

/-- Flattened coordinates retain exactly the same coefficient product. -/
theorem exact_flattened_tensor_coefficient
    {n m : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (g : G) (i j : Fin n) (k l : Fin m) :
    matrixRepresentationTensorProduct ρ σ g (finProdEquivFinMul n m (i, k))
        (finProdEquivFinMul n m (j, l)) =
      ρ g i j * σ g k l :=
  matrixRepresentationTensorProduct_apply ρ σ g i j k l

/-- Flattening uses the literal standard row-major index rather than an opaque finite choice. -/
theorem exact_standard_flattening_value
    (n m : ℕ) (i : Fin n) (k : Fin m) :
    (finProdEquivFinMul n m (i, k)).val = k.val + m * i.val :=
  finProdEquivFinMul_apply_val n m i k

/-- Hostile coordinate probe: changing the exact product formula is contradictory. -/
theorem changed_tensor_coefficient_blocked
    {n m : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (g : G) (i j : Fin n) (k l : Fin m)
    (changed : matrixRepresentationTensorProduct ρ σ g
        (finProdEquivFinMul n m (i, k)) (finProdEquivFinMul n m (j, l)) ≠
      ρ g i j * σ g k l) : False :=
  changed (matrixRepresentationTensorProduct_apply ρ σ g i j k l)

/-- Exact multiplication probe: tensor matrices compose in the original group order. -/
theorem exact_tensor_multiplication
    {n m : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ) (g h : G) :
    matrixRepresentationTensorProduct ρ σ (g * h) =
      matrixRepresentationTensorProduct ρ σ g *
        matrixRepresentationTensorProduct ρ σ h := by
  rw [map_mul]

variable [TopologicalSpace G]

/-- Continuity is derived from the two unchanged input representations. -/
theorem exact_tensor_continuity
    {n m : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ) (hσ : Continuous σ) :
    Continuous (matrixRepresentationTensorProduct ρ σ) :=
  continuous_matrixRepresentationTensorProduct ρ hρ σ hσ

/-- Dimension zero is retained without a positivity premise. -/
theorem zero_left_dimension_tensor_continuous
    {m : ℕ} (ρ₀ : G →* Matrix (Fin 0) (Fin 0) ℂ) (hρ₀ : Continuous ρ₀)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ) (hσ : Continuous σ) :
    Continuous (matrixRepresentationTensorProduct ρ₀ σ) :=
  continuous_matrixRepresentationTensorProduct ρ₀ hρ₀ σ hσ

/-- A zero right factor is supported independently of the left-zero probe. -/
theorem zero_right_dimension_tensor_continuous
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (σ₀ : G →* Matrix (Fin 0) (Fin 0) ℂ) (hσ₀ : Continuous σ₀) :
    Continuous (matrixRepresentationTensorProduct ρ σ₀) :=
  continuous_matrixRepresentationTensorProduct ρ hρ σ₀ hσ₀

omit [TopologicalSpace G] in
/-- Exact coordinate unitarity survives both Kronecker product and flattening. -/
theorem exact_tensor_unitary
    {n m : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (unitaryσ : ∀ g, star (σ g) * σ g = 1) (g : G) :
    star (matrixRepresentationTensorProduct ρ σ g) *
      matrixRepresentationTensorProduct ρ σ g = 1 :=
  matrixRepresentationTensorProduct_unitary ρ unitaryρ σ unitaryσ g

omit [TopologicalSpace G] in
/-- Hostile unitary probe: tensoring cannot silently lose the exact unitary equation. -/
theorem failed_tensor_unitary_blocked
    {n m : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (unitaryσ : ∀ g, star (σ g) * σ g = 1) (g : G)
    (failed : star (matrixRepresentationTensorProduct ρ σ g) *
      matrixRepresentationTensorProduct ρ σ g ≠ 1) : False :=
  failed (matrixRepresentationTensorProduct_unitary ρ unitaryρ σ unitaryσ g)

variable [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

/-- Compact complete reducibility applies directly to the flattened tensor representation. -/
theorem exact_tensor_semisimple
    {n m : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ) (hσ : Continuous σ) :
    Representation.IsSemisimpleRepresentation
      (matrixRepresentation (matrixRepresentationTensorProduct ρ σ)) :=
  compactRepresentation_isSemisimple
    (matrixRepresentationTensorProduct ρ σ)
    (continuous_matrixRepresentationTensorProduct ρ hρ σ hσ)

/-- The selected finite simple decomposition of the tensor representation has explicit unitary
coordinates for every summand. -/
theorem tensor_has_finite_simple_unitaryCoordinate_decomposition
    {n m : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ) (hσ : Continuous σ) :
    ∃ (summandCount : ℕ)
      (summands : Fin summandCount → Submodule ℂ[G]
        (matrixRepresentation (matrixRepresentationTensorProduct ρ σ)).asModule)
      (_ : (matrixRepresentation (matrixRepresentationTensorProduct ρ σ)).asModule ≃ₗ[ℂ[G]]
        Π₀ index : Fin summandCount, summands index),
      ∀ index, ∃ unitaryRepresentative :
          ContinuousUnitaryIrreducibleMatrixRepresentation G,
        Nonempty (Representation.Equiv
          (Representation.ofModule (k := ℂ) (G := G) (summands index))
          (matrixRepresentation unitaryRepresentative.representation)) :=
  compactRepresentation_exists_finite_simple_unitaryCoordinate_decomposition
    (matrixRepresentationTensorProduct ρ σ)
    (continuous_matrixRepresentationTensorProduct ρ hρ σ hσ)

end

end Probes
end CompactMatrixRepresentationTensorProduct
end Mathematics
end YangMills
