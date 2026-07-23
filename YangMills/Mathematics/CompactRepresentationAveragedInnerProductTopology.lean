/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactRepresentationAveragedInnerProductCore
import YangMills.Mathematics.PositiveBilinearUnitEllipsoid

/-!
# Topology induced by the Haar-averaged inner product

The normalized-Haar average is already packaged as a positive `InnerProductSpace.Core` on finite
complex coordinate vectors. This file proves that its induced norm topology is exactly the original
coordinate topology.

The real part of the averaged Hermitian pairing is first packaged as a continuous real bilinear map
in the existing norm. Finite-dimensional positive-ellipsoid coercivity then gives complex von
Neumann boundedness of its exact quadratic unit set. These are precisely the hypotheses of
Mathlib's `InnerProductSpace.Core.topology_eq` theorem.

No global norm or inner-product instance is replaced, and no orthonormal basis, unitarizing matrix,
or Peter–Weyl conclusion is constructed here.
-/

namespace YangMills
namespace Mathematics

open Bornology

noncomputable section

universe uG

/-- The real part of the Haar-averaged Hermitian pairing, bundled as a continuous real bilinear map
for the original finite coordinate norm. -/
noncomputable def compactRepresentationAveragedRealPairing
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ := by
  let core := compactRepresentationAveragedInnerProductCore ρ hρ
  letI : InnerProductSpace.Core ℂ (Fin n → ℂ) := core
  letI : Inner ℂ (Fin n → ℂ) := core.toCore.toInner
  let innerLinear (first : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℝ] ℝ :=
    { toFun := fun second => (compactRepresentationAveragedPairing ρ first second).re
      map_add' := by
        intro second third
        change (inner ℂ first (second + third)).re =
          (inner ℂ first second).re + (inner ℂ first third).re
        rw [InnerProductSpace.Core.inner_add_right]
        rfl
      map_smul' := by
        intro scalar second
        change (inner ℂ first ((scalar : ℂ) • second)).re =
          scalar • (inner ℂ first second).re
        rw [InnerProductSpace.Core.inner_smul_right]
        simp }
  let innerContinuous (first : Fin n → ℂ) : (Fin n → ℂ) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (innerLinear first)
  let outerLinear : (Fin n → ℂ) →ₗ[ℝ] ((Fin n → ℂ) →L[ℝ] ℝ) :=
    { toFun := innerContinuous
      map_add' := by
        intro first second
        ext third
        change (inner ℂ (first + second) third).re =
          (inner ℂ first third).re + (inner ℂ second third).re
        rw [InnerProductSpace.Core.inner_add_left]
        rfl
      map_smul' := by
        intro scalar first
        ext second
        change (inner ℂ ((scalar : ℂ) • first) second).re =
          scalar • (inner ℂ first second).re
        rw [InnerProductSpace.Core.inner_smul_left]
        simp }
  exact LinearMap.toContinuousLinearMap outerLinear

/-- The bundled real bilinear map evaluates to the real part of the unchanged averaged pairing. -/
@[simp]
theorem compactRepresentationAveragedRealPairing_apply
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (first second : Fin n → ℂ) :
    compactRepresentationAveragedRealPairing ρ hρ first second =
      (compactRepresentationAveragedPairing ρ first second).re := by
  rfl

/-- The exact quadratic unit ellipsoid of the averaged pairing is von Neumann bounded over `ℂ` in
the original coordinate norm. The proof first obtains real boundedness from finite-dimensional
coercivity and then transports the same norm bound to complex scalars. -/
theorem compactRepresentationAveraged_unitEllipsoid_isVonNBounded
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    IsVonNBounded ℂ {vector : Fin n → ℂ |
      (compactRepresentationAveragedPairing ρ vector vector).re < 1} := by
  have positive : ∀ vector : Fin n → ℂ, vector ≠ 0 →
      0 < compactRepresentationAveragedRealPairing ρ hρ vector vector := by
    intro vector vector_ne
    rw [compactRepresentationAveragedRealPairing_apply,
      compactRepresentationAveragedPairing_self_re ρ hρ]
    exact compactRepresentationAveragedNormSq_pos ρ hρ vector vector_ne
  have realBounded : IsVonNBounded ℝ {vector : Fin n → ℂ |
      compactRepresentationAveragedRealPairing ρ hρ vector vector < 1} :=
    positiveBilinear_unitEllipsoid_isVonNBounded
      (compactRepresentationAveragedRealPairing ρ hρ) positive
  rw [show {vector : Fin n → ℂ |
        (compactRepresentationAveragedPairing ρ vector vector).re < 1} =
      {vector : Fin n → ℂ |
        compactRepresentationAveragedRealPairing ρ hρ vector vector < 1} by
    ext vector
    simp only [Set.mem_setOf_eq, compactRepresentationAveragedRealPairing_apply]]
  obtain ⟨bound, normBound⟩ :=
    (NormedSpace.isVonNBounded_iff' ℝ).mp realBounded
  exact (NormedSpace.isVonNBounded_iff' ℂ).2 ⟨bound, normBound⟩

/-- The diagonal of the exact averaged inner-product core is continuous at zero in the original
coordinate topology. -/
theorem compactRepresentationAveragedInnerProductCore_diagonal_continuousAt
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    ContinuousAt (fun vector : Fin n → ℂ =>
      (compactRepresentationAveragedInnerProductCore ρ hρ).inner vector vector) 0 := by
  let core := compactRepresentationAveragedInnerProductCore ρ hρ
  letI : InnerProductSpace.Core ℂ (Fin n → ℂ) := core
  letI : Inner ℂ (Fin n → ℂ) := core.toCore.toInner
  have realDiagonalContinuous : Continuous (fun vector : Fin n → ℂ =>
      compactRepresentationAveragedRealPairing ρ hρ vector vector) :=
    ((compactRepresentationAveragedRealPairing ρ hρ).continuous.comp continuous_id).clm_apply
      continuous_id
  have complexDiagonalContinuous : Continuous (fun vector : Fin n → ℂ =>
      ((compactRepresentationAveragedRealPairing ρ hρ vector vector : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp realDiagonalContinuous
  have diagonalEq : (fun vector : Fin n → ℂ => core.inner vector vector) =
      fun vector => ((compactRepresentationAveragedRealPairing ρ hρ vector vector : ℝ) : ℂ) := by
    funext vector
    rw [compactRepresentationAveragedRealPairing_apply]
    change inner ℂ vector vector = ((inner ℂ vector vector).re : ℂ)
    exact (InnerProductSpace.Core.ofReal_normSq_eq_inner_self vector).symm
  change ContinuousAt (fun vector : Fin n → ℂ => core.inner vector vector) 0
  rw [diagonalEq]
  exact complexDiagonalContinuous.continuousAt

/-- The original coordinate topology is exactly the norm topology induced by the normalized-Haar
averaged inner-product core. This includes the zero-dimensional coordinate space and installs no
global structure. -/
theorem compactRepresentationAveragedInnerProductCore_topology_eq
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    (inferInstance : TopologicalSpace (Fin n → ℂ)) =
      (@InnerProductSpace.Core.toNormedAddCommGroup ℂ (Fin n → ℂ) _ _ _
        (compactRepresentationAveragedInnerProductCore ρ hρ)).toMetricSpace.toUniformSpace.toTopologicalSpace := by
  let core := compactRepresentationAveragedInnerProductCore ρ hρ
  letI : InnerProductSpace.Core ℂ (Fin n → ℂ) := core
  letI : Inner ℂ (Fin n → ℂ) := core.toCore.toInner
  have bounded : IsVonNBounded ℂ {vector : Fin n → ℂ |
      (core.inner vector vector).re < 1} := by
    change IsVonNBounded ℂ {vector : Fin n → ℂ |
      (compactRepresentationAveragedPairing ρ vector vector).re < 1}
    exact compactRepresentationAveraged_unitEllipsoid_isVonNBounded ρ hρ
  exact InnerProductSpace.Core.topology_eq
    (compactRepresentationAveragedInnerProductCore_diagonal_continuousAt ρ hρ) bounded

end

end Mathematics
end YangMills
