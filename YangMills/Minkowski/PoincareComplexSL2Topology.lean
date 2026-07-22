/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.Topology.Algebra.Group.Basic
import YangMills.Minkowski.PoincareComplexSignSL2

/-!
# The matrix topology on homogeneous `SL(2, ℂ)`

This file equips the already constructed concrete matrix carrier
`Matrix.SpecialLinearGroup (Fin 2) ℂ` with the topology induced by its exact matrix inclusion and
proves that it is a Hausdorff topological group. Mathlib's matrix special linear group currently has
no topology instance, so this is separately packaged general infrastructure.

Inversion is continuous because the special-linear inverse is the polynomial adjugate. Nothing here
constructs the Lorentz projection, an inhomogeneous Poincaré cover, or a Yang–Mills theory.
-/

open Matrix

namespace YangMills
namespace Minkowski

/-- The exact matrix-subspace topology on homogeneous `SL(2, ℂ)`. -/
noncomputable instance complexSpecialLinearTwoTopologicalSpace :
    TopologicalSpace ComplexSpecialLinearTwo :=
  TopologicalSpace.induced
    (fun A : ComplexSpecialLinearTwo => (A : Matrix (Fin 2) (Fin 2) ℂ)) inferInstance

/-- Matrix multiplication restricts continuously to homogeneous `SL(2, ℂ)`. -/
instance complexSpecialLinearTwoContinuousMul : ContinuousMul ComplexSpecialLinearTwo where
  continuous_mul := by
    rw [continuous_induced_rng]
    change Continuous (fun pair : ComplexSpecialLinearTwo × ComplexSpecialLinearTwo =>
      (pair.1.1 * pair.2.1 : Matrix (Fin 2) (Fin 2) ℂ))
    fun_prop

/-- Matrix adjugation makes inversion continuous on homogeneous `SL(2, ℂ)`. -/
instance complexSpecialLinearTwoContinuousInv : ContinuousInv ComplexSpecialLinearTwo where
  continuous_inv := by
    rw [continuous_induced_rng]
    change Continuous (fun A : ComplexSpecialLinearTwo => Matrix.adjugate A.1)
    fun_prop

/-- Homogeneous matrix `SL(2, ℂ)` is a topological group for its exact matrix topology. -/
instance complexSpecialLinearTwoIsTopologicalGroup :
    IsTopologicalGroup ComplexSpecialLinearTwo where

/-- The exact matrix inclusion of homogeneous `SL(2, ℂ)` is a topological embedding. -/
theorem complexSpecialLinearTwo_coe_isEmbedding :
    Topology.IsEmbedding
      (fun A : ComplexSpecialLinearTwo => (A : Matrix (Fin 2) (Fin 2) ℂ)) :=
  ⟨Topology.IsInducing.induced _, Subtype.coe_injective⟩

/-- The induced matrix topology on homogeneous `SL(2, ℂ)` is Hausdorff. -/
noncomputable instance complexSpecialLinearTwoT2Space : T2Space ComplexSpecialLinearTwo :=
  complexSpecialLinearTwo_coe_isEmbedding.t2Space

/-- Every element of the exact matrix-sign subgroup commutes with every homogeneous matrix. -/
theorem complexSignSL2Subgroup_central
    (signMatrix : complexSignSL2Subgroup) (A : ComplexSpecialLinearTwo) :
    signMatrix.1 * A = A * signMatrix.1 := by
  obtain ⟨sign, equality⟩ := signMatrix.2
  rw [← equality]
  exact complexSignToSL2_central sign A

end Minkowski
end YangMills
