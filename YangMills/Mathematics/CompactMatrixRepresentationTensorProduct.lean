/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import YangMills.Mathematics.CompactRepresentationSimpleSummandCoordinates

/-!
# Tensor products of finite matrix representations

The Kronecker product of two matrix representations is their tensor-product representation in the
product basis. This file constructs that representation, reindexes its product coordinates by
`Fin (n * m)`, and proves the exact coefficient formula

`(ρ ⊗ σ)(g)_{(i,k),(j,l)} = ρ(g)_{i,j} σ(g)_{k,l}`.

Continuity and coordinate unitarity are preserved. Together with compact complete reducibility,
this is the algebraic input needed to show that products of irreducible matrix coefficients lie in
finite sums of irreducible coefficient blocks. This is the concrete product-basis matrix model; an
equivalence with Mathlib's abstract `TensorProduct` carrier is not constructed here. No
point-separation or Peter–Weyl density theorem is asserted.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

/-- The Kronecker tensor product representation in the literal product index. -/
def matrixRepresentationKroneckerTensor
    {G : Type uG} [Group G] {n m : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ) :
    G →* Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ where
  toFun g := Matrix.kronecker (ρ g) (σ g)
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul]
    exact Matrix.mul_kronecker_mul (ρ g) (ρ h) (σ g) (σ h)

/-- Every product-index tensor coefficient is exactly the product of the two original
coefficients. -/
@[simp]
theorem matrixRepresentationKroneckerTensor_apply
    {G : Type uG} [Group G] {n m : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (g : G) (i j : Fin n) (k l : Fin m) :
    matrixRepresentationKroneckerTensor ρ σ g (i, k) (j, l) =
      ρ g i j * σ g k l := by
  rfl

/-- Continuity of both input representations gives continuity of the product-index tensor
representation. -/
theorem continuous_matrixRepresentationKroneckerTensor
    {G : Type uG} [Group G] [TopologicalSpace G] {n m : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ) (hσ : Continuous σ) :
    Continuous (matrixRepresentationKroneckerTensor ρ σ) := by
  change Continuous (fun g (i : Fin n × Fin m) (j : Fin n × Fin m) =>
    ρ g i.1 j.1 * σ g i.2 j.2)
  rw [continuous_pi_iff]
  intro i
  rw [continuous_pi_iff]
  intro j
  fun_prop

/-- The Kronecker tensor product of coordinate-unitary representations is coordinate-unitary. -/
theorem matrixRepresentationKroneckerTensor_unitary
    {G : Type uG} [Group G] {n m : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (unitaryσ : ∀ g, star (σ g) * σ g = 1)
    (g : G) :
    star (matrixRepresentationKroneckerTensor ρ σ g) *
      matrixRepresentationKroneckerTensor ρ σ g = 1 := by
  change star (Matrix.kronecker (ρ g) (σ g)) *
    Matrix.kronecker (ρ g) (σ g) = 1
  rw [Matrix.star_eq_conjTranspose]
  change (Matrix.kroneckerMap (fun x y : ℂ => x * y) (ρ g) (σ g)).conjTranspose *
    Matrix.kroneckerMap (fun x y : ℂ => x * y) (ρ g) (σ g) = 1
  rw [Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul]
  rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose,
    unitaryρ g, unitaryσ g, Matrix.one_kronecker_one]

/-- The standard explicit finite equivalence used to flatten product coordinates. It sends
`(i, k)` to the row-major value `k + m * i`. -/
def finProdEquivFinMul (n m : ℕ) : Fin n × Fin m ≃ Fin (n * m) :=
  @finProdFinEquiv n m

/-- The flattening map has the literal standard row-major value `k + m * i`. -/
@[simp]
theorem finProdEquivFinMul_apply_val (n m : ℕ) (i : Fin n) (k : Fin m) :
    (finProdEquivFinMul n m (i, k)).val = k.val + m * i.val :=
  rfl

/-- The tensor-product representation flattened into `Fin (n * m)` coordinates. -/
noncomputable def matrixRepresentationTensorProduct
    {G : Type uG} [Group G] {n m : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ) :
    G →* Matrix (Fin (n * m)) (Fin (n * m)) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ (finProdEquivFinMul n m)).toMonoidHom.comp
    (matrixRepresentationKroneckerTensor ρ σ)

/-- Flattening preserves the exact product coefficient at the flattened pair indices. -/
@[simp]
theorem matrixRepresentationTensorProduct_apply
    {G : Type uG} [Group G] {n m : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (g : G) (i j : Fin n) (k l : Fin m) :
    matrixRepresentationTensorProduct ρ σ g (finProdEquivFinMul n m (i, k))
        (finProdEquivFinMul n m (j, l)) =
      ρ g i j * σ g k l := by
  simp [matrixRepresentationTensorProduct, Matrix.reindex_apply,
    matrixRepresentationKroneckerTensor]

/-- Reindexing both square-matrix coordinates commutes with matrix star. -/
theorem star_reindexAlgEquiv
    {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (equivalence : a ≃ b) (A : Matrix a a ℂ) :
    star ((Matrix.reindexAlgEquiv ℂ ℂ equivalence) A) =
      (Matrix.reindexAlgEquiv ℂ ℂ equivalence) (star A) := by
  ext i j
  simp [Matrix.star_eq_conjTranspose, Matrix.reindex_apply,
    Matrix.conjTranspose_apply]

/-- The flattened tensor product retains the exact coordinate-unitary equation. -/
theorem matrixRepresentationTensorProduct_unitary
    {G : Type uG} [Group G] {n m : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (unitaryσ : ∀ g, star (σ g) * σ g = 1)
    (g : G) :
    star (matrixRepresentationTensorProduct ρ σ g) *
      matrixRepresentationTensorProduct ρ σ g = 1 := by
  unfold matrixRepresentationTensorProduct
  change star ((Matrix.reindexAlgEquiv ℂ ℂ (finProdEquivFinMul n m))
      (matrixRepresentationKroneckerTensor ρ σ g)) *
    (Matrix.reindexAlgEquiv ℂ ℂ (finProdEquivFinMul n m))
      (matrixRepresentationKroneckerTensor ρ σ g) = 1
  rw [star_reindexAlgEquiv, ← map_mul]
  rw [matrixRepresentationKroneckerTensor_unitary ρ unitaryρ σ unitaryσ g, map_one]

/-- Flattening preserves continuity of the tensor-product representation. -/
theorem continuous_matrixRepresentationTensorProduct
    {G : Type uG} [Group G] [TopologicalSpace G] {n m : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (σ : G →* Matrix (Fin m) (Fin m) ℂ) (hσ : Continuous σ) :
    Continuous (matrixRepresentationTensorProduct ρ σ) := by
  change Continuous (fun g (i j : Fin (n * m)) =>
    ρ g ((finProdEquivFinMul n m).symm i).1
        ((finProdEquivFinMul n m).symm j).1 *
      σ g ((finProdEquivFinMul n m).symm i).2
        ((finProdEquivFinMul n m).symm j).2)
  rw [continuous_pi_iff]
  intro i
  rw [continuous_pi_iff]
  intro j
  fun_prop

end

end Mathematics
end YangMills
