/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.SmoothLieGroupScalarFunctionLinear

/-!
# Smoothness reduction for right-invariant scalar Laplacians

This file isolates one regularity input: differentiating a smooth scalar function along a fixed
right-invariant vector field again gives a smooth scalar function. From that field it constructs
smooth first derivatives, smooth iterated derivatives, finite-basis smooth Laplacians, and a
continuous-function realization of the pairing Laplacian.

The one-step regularity interface is then inhabited from the existing smooth right-invariant vector
field and Mathlib's tangent-map calculus. A definitional bridge from the legacy raw `mfderiv` formula
to `mvfderiv` proves linearity and constructs the canonical pairing-Laplacian linear map. The file
does not prove graph density, a heat-quotient bound, generator closure, or comparison with the
Laplace–Beltrami operator.
-/

namespace YangMills
namespace Mathematics

open scoped Manifold ContDiff BigOperators

noncomputable section

universe uE uG

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

/-- Regularity interface saying that every smooth scalar test remains smooth after one right-
invariant directional derivative. It is canonically inhabited immediately below. -/
structure RightInvariantScalarDerivativeSmoothnessData where
  derivative_contMDiff :
    ∀ (f : SmoothLieGroupScalarFunction (E := E) (G := G))
      (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G),
      ContMDiff (modelWithCornersSelf ℝ E) 𝓘(ℝ, ℝ) ∞
        (fun g => rightInvariantScalarDerivative f Y g)

/-- Canonical one-step derivative smoothness, constructed from the smooth right-invariant vector
field, the smooth tangent map of `f`, and the model-space tangent-fiber projection. -/
noncomputable def rightInvariantScalarDerivativeSmoothnessData :
    RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G) where
  derivative_contMDiff f Y := by
    have hfield :=
      contMDiff_mulRightInvariantVectorField (modelWithCornersSelf ℝ E) Y
    have htangent := f.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)
    have hsnd := contMDiff_snd_tangentBundle_modelSpace (n := ∞) ℝ 𝓘(ℝ, ℝ)
    exact hsnd.comp (htangent.comp hfield)

namespace RightInvariantScalarDerivativeSmoothnessData

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- The legacy raw `mfderiv` presentation is definitionally the exterior derivative specialized to
its right-invariant vector. This bridge exposes Mathlib's linear derivative API. -/
theorem rightInvariantScalarDerivative_eq_mvfderiv
    (f : G → ℝ) (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantScalarDerivative f Y g =
      mvfderiv (modelWithCornersSelf ℝ E) f g
        (mulRightInvariantVectorField (modelWithCornersSelf ℝ E) Y g) :=
  rfl

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Right-invariant scalar differentiation is additive on smooth inputs. -/
theorem rightInvariantScalarDerivative_add
    (f h : SmoothLieGroupScalarFunction (E := E) (G := G))
    (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantScalarDerivative (f + h) Y g =
      rightInvariantScalarDerivative f Y g + rightInvariantScalarDerivative h Y g := by
  rw [rightInvariantScalarDerivative_eq_mvfderiv,
    rightInvariantScalarDerivative_eq_mvfderiv,
    rightInvariantScalarDerivative_eq_mvfderiv]
  change (mvfderiv (modelWithCornersSelf ℝ E) (f.toFun + h.toFun) g) _ = _
  rw [mvfderiv_add (f.contMDiff.mdifferentiableAt (by simp))
    (h.contMDiff.mdifferentiableAt (by simp))]
  rfl

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Right-invariant scalar differentiation commutes with real scalar multiplication on smooth
inputs. -/
theorem rightInvariantScalarDerivative_smul
    (c : ℝ) (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantScalarDerivative (c • f) Y g =
      c * rightInvariantScalarDerivative f Y g := by
  rw [rightInvariantScalarDerivative_eq_mvfderiv,
    rightInvariantScalarDerivative_eq_mvfderiv]
  change (mvfderiv (modelWithCornersSelf ℝ E) ((fun _ : G => c) * f.toFun) g) _ = _
  rw [mvfderiv_mul (I := modelWithCornersSelf ℝ E) (x := g)
    (f := fun _ : G => c) (g := f.toFun) mdifferentiableAt_const
    (f.contMDiff.mdifferentiableAt (by simp)), mvfderiv_const]
  simp

/-- One right-invariant derivative packaged back into the smooth scalar carrier. -/
def smoothDerivative
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    SmoothLieGroupScalarFunction (E := E) (G := G) :=
  ⟨fun g => rightInvariantScalarDerivative f Y g,
    regularity.derivative_contMDiff f Y⟩

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem smoothDerivative_apply
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    regularity.smoothDerivative f Y g = rightInvariantScalarDerivative f Y g :=
  rfl

/-- Two iterated right-invariant derivatives packaged as a smooth scalar function. -/
def smoothSecondDerivative
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (X Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) :
    SmoothLieGroupScalarFunction (E := E) (G := G) :=
  regularity.smoothDerivative (regularity.smoothDerivative f Y) X

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem smoothSecondDerivative_apply
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (X Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    regularity.smoothSecondDerivative f X Y g =
      rightInvariantScalarSecondDerivative f X Y g :=
  rfl

/-- A finite basis sum of second derivatives, now carrying an actual smoothness proof. -/
def smoothLaplacianInBasis
    {rank : ℕ}
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (basis : Module.Basis (Fin rank) ℝ
      (GroupLieAlgebra (modelWithCornersSelf ℝ E) G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) :
    SmoothLieGroupScalarFunction (E := E) (G := G) :=
  ∑ a, regularity.smoothSecondDerivative f (basis a) (basis a)

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem smoothLaplacianInBasis_apply
    {rank : ℕ}
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (basis : Module.Basis (Fin rank) ℝ
      (GroupLieAlgebra (modelWithCornersSelf ℝ E) G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    regularity.smoothLaplacianInBasis basis f g =
      rightInvariantScalarLaplacianInBasis basis f g := by
  unfold smoothLaplacianInBasis rightInvariantScalarLaplacianInBasis
  rw [SmoothLieGroupScalarFunction.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro a ha
  rfl

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Under the one-step smoothness field, the iterated derivative is additive in its smooth input. -/
theorem rightInvariantScalarSecondDerivative_add
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f h : SmoothLieGroupScalarFunction (E := E) (G := G))
    (X Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantScalarSecondDerivative (f + h) X Y g =
      rightInvariantScalarSecondDerivative f X Y g +
        rightInvariantScalarSecondDerivative h X Y g := by
  calc
    _ = rightInvariantScalarDerivative (regularity.smoothDerivative (f + h) Y) X g := rfl
    _ = rightInvariantScalarDerivative
        (regularity.smoothDerivative f Y + regularity.smoothDerivative h Y) X g := by
      congr 2
      ext q
      exact rightInvariantScalarDerivative_add f h Y q
    _ = _ := rightInvariantScalarDerivative_add _ _ X g

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Under the one-step smoothness field, the iterated derivative commutes with real scalar
multiplication. -/
theorem rightInvariantScalarSecondDerivative_smul
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (c : ℝ) (f : SmoothLieGroupScalarFunction (E := E) (G := G))
    (X Y : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) (g : G) :
    rightInvariantScalarSecondDerivative (c • f) X Y g =
      c * rightInvariantScalarSecondDerivative f X Y g := by
  calc
    _ = rightInvariantScalarDerivative (regularity.smoothDerivative (c • f) Y) X g := rfl
    _ = rightInvariantScalarDerivative (c • regularity.smoothDerivative f Y) X g := by
      congr 2
      ext q
      exact rightInvariantScalarDerivative_smul c f Y q
    _ = _ := rightInvariantScalarDerivative_smul c _ X g

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Every finite-basis Laplacian is additive under the one-step derivative smoothness field. -/
theorem rightInvariantScalarLaplacianInBasis_add
    {rank : ℕ}
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (basis : Module.Basis (Fin rank) ℝ
      (GroupLieAlgebra (modelWithCornersSelf ℝ E) G))
    (f h : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    rightInvariantScalarLaplacianInBasis basis (f + h) g =
      rightInvariantScalarLaplacianInBasis basis f g +
        rightInvariantScalarLaplacianInBasis basis h g := by
  unfold rightInvariantScalarLaplacianInBasis
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  exact regularity.rightInvariantScalarSecondDerivative_add f h (basis a) (basis a) g

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Every finite-basis Laplacian commutes with real scalar multiplication under the one-step
smoothness field. -/
theorem rightInvariantScalarLaplacianInBasis_smul
    {rank : ℕ}
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (basis : Module.Basis (Fin rank) ℝ
      (GroupLieAlgebra (modelWithCornersSelf ℝ E) G))
    (c : ℝ) (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    rightInvariantScalarLaplacianInBasis basis (c • f) g =
      c * rightInvariantScalarLaplacianInBasis basis f g := by
  unfold rightInvariantScalarLaplacianInBasis
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact regularity.rightInvariantScalarSecondDerivative_smul c f (basis a) (basis a) g

/-- The selected pairing Laplacian packaged as a smooth scalar function. -/
def smoothPairingLaplacian
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (laplacianData : RightInvariantPairingLaplacianData inner)
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) :
    SmoothLieGroupScalarFunction (E := E) (G := G) :=
  regularity.smoothLaplacianInBasis laplacianData.orthonormalBasis.basis f

@[simp]
theorem smoothPairingLaplacian_apply
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (laplacianData : RightInvariantPairingLaplacianData inner)
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    regularity.smoothPairingLaplacian laplacianData f g =
      laplacianData.laplacian f g :=
  regularity.smoothLaplacianInBasis_apply laplacianData.orthonormalBasis.basis f g

/-- The selected pairing Laplacian is additive under the one-step derivative smoothness field. -/
theorem pairingLaplacian_add
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (laplacianData : RightInvariantPairingLaplacianData inner)
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f h : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    laplacianData.laplacian (f + h) g =
      laplacianData.laplacian f g + laplacianData.laplacian h g := by
  unfold RightInvariantPairingLaplacianData.laplacian
  exact regularity.rightInvariantScalarLaplacianInBasis_add
    laplacianData.orthonormalBasis.basis f h g

/-- The selected pairing Laplacian commutes with real scalar multiplication under the one-step
derivative smoothness field. -/
theorem pairingLaplacian_smul
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (laplacianData : RightInvariantPairingLaplacianData inner)
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (c : ℝ) (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    laplacianData.laplacian (c • f) g = c * laplacianData.laplacian f g := by
  unfold RightInvariantPairingLaplacianData.laplacian
  exact regularity.rightInvariantScalarLaplacianInBasis_smul
    laplacianData.orthonormalBasis.basis c f g

/-- Continuous ambient realization of the pairing Laplacian, derived from the one-step smoothness
field. The subsequent declaration bundles it as a linear map. -/
noncomputable def pairingLaplacianContinuousMap
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (laplacianData : RightInvariantPairingLaplacianData inner)
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) : C(G, ℝ) :=
  smoothLieGroupScalarToContinuousLinearMap
    (regularity.smoothPairingLaplacian laplacianData f)

@[simp]
theorem pairingLaplacianContinuousMap_apply
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (laplacianData : RightInvariantPairingLaplacianData inner)
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    regularity.pairingLaplacianContinuousMap laplacianData f g =
      laplacianData.laplacian f g :=
  regularity.smoothPairingLaplacian_apply laplacianData f g

/-- The pairing Laplacian as the algebraic linear map from the smooth proper domain into the
continuous ambient carrier required by graph-core closure. -/
noncomputable def pairingLaplacianLinearMap
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (laplacianData : RightInvariantPairingLaplacianData inner)
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G)) :
    SmoothLieGroupScalarFunction (E := E) (G := G) →ₗ[ℝ] C(G, ℝ) where
  toFun := regularity.pairingLaplacianContinuousMap laplacianData
  map_add' f h := by
    ext g
    simp only [ContinuousMap.coe_add, Pi.add_apply]
    rw [regularity.pairingLaplacianContinuousMap_apply,
      regularity.pairingLaplacianContinuousMap_apply,
      regularity.pairingLaplacianContinuousMap_apply]
    exact regularity.pairingLaplacian_add laplacianData f h g
  map_smul' c f := by
    ext g
    simp only [ContinuousMap.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [regularity.pairingLaplacianContinuousMap_apply,
      regularity.pairingLaplacianContinuousMap_apply]
    exact regularity.pairingLaplacian_smul laplacianData c f g

@[simp]
theorem pairingLaplacianLinearMap_apply
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (laplacianData : RightInvariantPairingLaplacianData inner)
    (regularity : RightInvariantScalarDerivativeSmoothnessData (E := E) (G := G))
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    regularity.pairingLaplacianLinearMap laplacianData f g =
      laplacianData.laplacian f g :=
  regularity.pairingLaplacianContinuousMap_apply laplacianData f g

end RightInvariantScalarDerivativeSmoothnessData

/-- Canonical pairing-Laplacian linear map; callers need not supply a derivative-regularity witness. -/
noncomputable def rightInvariantPairingLaplacianLinearMap
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (laplacianData : RightInvariantPairingLaplacianData inner) :
    SmoothLieGroupScalarFunction (E := E) (G := G) →ₗ[ℝ] C(G, ℝ) :=
  rightInvariantScalarDerivativeSmoothnessData.pairingLaplacianLinearMap laplacianData

@[simp]
theorem rightInvariantPairingLaplacianLinearMap_apply
    {inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    (laplacianData : RightInvariantPairingLaplacianData inner)
    (f : SmoothLieGroupScalarFunction (E := E) (G := G)) (g : G) :
    rightInvariantPairingLaplacianLinearMap laplacianData f g =
      laplacianData.laplacian f g :=
  rightInvariantScalarDerivativeSmoothnessData.pairingLaplacianLinearMap_apply
    laplacianData f g

end

end Mathematics
end YangMills
