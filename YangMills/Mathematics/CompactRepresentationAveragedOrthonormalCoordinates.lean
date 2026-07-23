/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import YangMills.Mathematics.CompactRepresentationAveragedNormedRealization

/-!
# Orthonormal coordinates for the Haar-averaged realization

The topology-compatible Haar-averaged inner-product realization is finite dimensional. This file
chooses Mathlib's standard noncomputable orthonormal basis, reindexes it by the original `Fin n`
coordinate size, and constructs the resulting ordinary complex-linear coordinate equivalence.

The equivalence sends every chosen basis vector to the corresponding exact Kronecker coordinate and
identifies the Haar-averaged pairing with the standard coordinate Hermitian pairing. This is the
basis-selection part of compact-representation unitarization. Conjugating the representation and
proving the resulting matrices unitary remain separate.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

/-- A selected orthonormal basis for the exact averaged inner-product realization, reindexed by the
original matrix coordinate type `Fin n`. -/
noncomputable def compactRepresentationAveragedOrthonormalBasis
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    @OrthonormalBasis (Fin n) ℂ _ (Fin n → ℂ)
      (compactRepresentationAveragedNormedAddCommGroup ρ hρ)
      (compactRepresentationAveragedInnerProductSpace ρ hρ) _ := by
  letI : NormedAddCommGroup (Fin n → ℂ) :=
    compactRepresentationAveragedNormedAddCommGroup ρ hρ
  letI : @NormedSpace ℂ (Fin n → ℂ) _
      (compactRepresentationAveragedNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup :=
    compactRepresentationAveragedNormedSpace ρ hρ
  letI : @InnerProductSpace ℂ (Fin n → ℂ) _
      (compactRepresentationAveragedNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup :=
    compactRepresentationAveragedInnerProductSpace ρ hρ
  exact (stdOrthonormalBasis ℂ (Fin n → ℂ)).reindex
    (finCongr (Module.finrank_fin_fun ℂ))

/-- The ordinary algebraic basis underlying the selected averaged orthonormal basis. -/
noncomputable def compactRepresentationAveragedBasis
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    Module.Basis (Fin n) ℂ (Fin n → ℂ) :=
  @OrthonormalBasis.toBasis (Fin n) ℂ _ (Fin n → ℂ)
    (compactRepresentationAveragedNormedAddCommGroup ρ hρ)
    (compactRepresentationAveragedInnerProductSpace ρ hρ) _
    (compactRepresentationAveragedOrthonormalBasis ρ hρ)

/-- The explicit complex-linear coordinate equivalence determined by the selected averaged
orthonormal basis. Its codomain is the original function-shaped coordinate carrier. -/
noncomputable def compactRepresentationUnitarizingLinearEquiv
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  (compactRepresentationAveragedBasis ρ hρ).repr.trans
    (Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin n))

/-- The unitarizing coordinate equivalence sends each selected orthonormal basis vector to the exact
Kronecker coordinate vector. -/
@[simp]
theorem compactRepresentationUnitarizingLinearEquiv_apply_basis
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (index : Fin n) :
    compactRepresentationUnitarizingLinearEquiv ρ hρ
        (compactRepresentationAveragedOrthonormalBasis ρ hρ index) =
      Pi.single index 1 := by
  change (Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin n))
    ((compactRepresentationAveragedBasis ρ hρ).repr
      ((compactRepresentationAveragedBasis ρ hρ) index)) = Pi.single index 1
  rw [(compactRepresentationAveragedBasis ρ hρ).repr_self]
  exact Finsupp.linearEquivFunOnFinite_single ℂ ℂ (Fin n) index 1

/-- The selected coordinate equivalence is genuinely unitarizing at the pairing level: the standard
coordinate Hermitian pairing of coordinate images is exactly the original Haar-averaged pairing. -/
theorem compactRepresentationUnitarizingLinearEquiv_pairing
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (first second : Fin n → ℂ) :
    coordinateHermitianPairing
        (compactRepresentationUnitarizingLinearEquiv ρ hρ first)
        (compactRepresentationUnitarizingLinearEquiv ρ hρ second) =
      compactRepresentationAveragedPairing ρ first second := by
  letI : NormedAddCommGroup (Fin n → ℂ) :=
    compactRepresentationAveragedNormedAddCommGroup ρ hρ
  letI : @NormedSpace ℂ (Fin n → ℂ) _
      (compactRepresentationAveragedNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup :=
    compactRepresentationAveragedNormedSpace ρ hρ
  letI : @InnerProductSpace ℂ (Fin n → ℂ) _
      (compactRepresentationAveragedNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup :=
    compactRepresentationAveragedInnerProductSpace ρ hρ
  rw [← compactRepresentationAveragedInnerProductSpace_inner ρ hρ]
  have sumIdentity := OrthonormalBasis.sum_inner_mul_inner
    (compactRepresentationAveragedOrthonormalBasis ρ hρ) first second
  unfold coordinateHermitianPairing
  rw [← sumIdentity]
  apply Finset.sum_congr rfl
  intro index _
  change star ((compactRepresentationAveragedOrthonormalBasis ρ hρ).repr first index) *
      (compactRepresentationAveragedOrthonormalBasis ρ hρ).repr second index =
    inner ℂ first (compactRepresentationAveragedOrthonormalBasis ρ hρ index) *
      inner ℂ (compactRepresentationAveragedOrthonormalBasis ρ hρ index) second
  rw [(compactRepresentationAveragedOrthonormalBasis ρ hρ).repr_apply_apply,
    (compactRepresentationAveragedOrthonormalBasis ρ hρ).repr_apply_apply]
  change star (compactRepresentationAveragedPairing ρ
      (compactRepresentationAveragedOrthonormalBasis ρ hρ index) first) *
      compactRepresentationAveragedPairing ρ
        (compactRepresentationAveragedOrthonormalBasis ρ hρ index) second =
    compactRepresentationAveragedPairing ρ first
        (compactRepresentationAveragedOrthonormalBasis ρ hρ index) *
      compactRepresentationAveragedPairing ρ
        (compactRepresentationAveragedOrthonormalBasis ρ hρ index) second
  rw [compactRepresentationAveragedPairing_conj_symm ρ first
    (compactRepresentationAveragedOrthonormalBasis ρ hρ index)]

end

end Mathematics
end YangMills
