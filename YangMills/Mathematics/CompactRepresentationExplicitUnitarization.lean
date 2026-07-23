/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactRepresentationAveragedOrthonormalCoordinates

/-!
# Explicit finite-coordinate unitarization by Haar averaging

This file completes the finite-dimensional coordinate unitarization argument. The original
representation is conjugated through the exact averaged-orthonormal coordinate equivalence. The
result is packaged as a genuine continuous matrix representation with formula

`σ(g) = U ρ(g) U⁻¹`.

The selected `U` is also bundled as a Mathlib `Representation.Equiv`. Transport of the averaged
pairing proves that `σ(g)` preserves the standard coordinate Hermitian pairing. A reusable
column/Kronecker argument then derives the literal matrix equation

`star (σ(g)) * σ(g) = 1`.

This is finite-coordinate compact-representation mathematics. It does not assert irreducible-dual
exhaustion, countability, Peter–Weyl density, or Fourier-series convergence.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

/-- The representation on standard coordinates obtained by conjugating the original linear action
through the selected averaged-orthonormal coordinate equivalence. -/
noncomputable def compactRepresentationConjugatedLinearRepresentation
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    Representation ℂ G (Fin n → ℂ) where
  toFun g := (compactRepresentationUnitarizingLinearEquiv ρ hρ).conj
    (matrixRepresentation ρ g)
  map_one' := by
    ext vector
    simp [LinearEquiv.conj_apply]
  map_mul' g h := by
    ext vector
    simp [LinearEquiv.conj_apply]

/-- The explicitly unitarized matrix representation in standard `Fin n` coordinates. -/
noncomputable def compactRepresentationUnitarizedRepresentation
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    G →* Matrix (Fin n) (Fin n) ℂ :=
  (LinearMap.toMatrixAlgEquiv' :
    Module.End ℂ (Fin n → ℂ) ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ).toMonoidHom.comp
      (compactRepresentationConjugatedLinearRepresentation ρ hρ)

/-- The resulting matrix is exactly `U ρ(g) U⁻¹`, with orientation fixed by the selected coordinate
map from the averaged realization to standard coordinates. -/
theorem compactRepresentationUnitarizedRepresentation_eq_conjugation
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (g : G) :
    compactRepresentationUnitarizedRepresentation ρ hρ g =
      LinearMap.toMatrix'
          (compactRepresentationUnitarizingLinearEquiv ρ hρ).toLinearMap *
        ρ g * LinearMap.toMatrix'
          (compactRepresentationUnitarizingLinearEquiv ρ hρ).symm.toLinearMap := by
  change LinearMap.toMatrix' (((compactRepresentationUnitarizingLinearEquiv ρ hρ).toLinearMap.comp
    (matrixRepresentation ρ g)).comp
      (compactRepresentationUnitarizingLinearEquiv ρ hρ).symm.toLinearMap) = _
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
    matrixRepresentation_apply, LinearMap.toMatrix'_toLin']

/-- The explicitly unitarized matrix representation is continuous. -/
theorem continuous_compactRepresentationUnitarizedRepresentation
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    Continuous (compactRepresentationUnitarizedRepresentation ρ hρ) := by
  rw [show (compactRepresentationUnitarizedRepresentation ρ hρ :
      G → Matrix (Fin n) (Fin n) ℂ) = fun g =>
      LinearMap.toMatrix'
          (compactRepresentationUnitarizingLinearEquiv ρ hρ).toLinearMap *
        ρ g * LinearMap.toMatrix'
          (compactRepresentationUnitarizingLinearEquiv ρ hρ).symm.toLinearMap by
    funext g
    exact compactRepresentationUnitarizedRepresentation_eq_conjugation ρ hρ g]
  exact (continuous_const.mul hρ).mul continuous_const

/-- Exact action formula for the explicitly unitarized matrix representation. -/
@[simp]
theorem compactRepresentationUnitarizedRepresentation_action
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (g : G) (vector : Fin n → ℂ) :
    Matrix.mulVec (compactRepresentationUnitarizedRepresentation ρ hρ g) vector =
      compactRepresentationUnitarizingLinearEquiv ρ hρ
        (Matrix.mulVec (ρ g)
          ((compactRepresentationUnitarizingLinearEquiv ρ hρ).symm vector)) := by
  unfold compactRepresentationUnitarizedRepresentation
  change Matrix.toLin' (LinearMap.toMatrix' _) vector = _
  rw [Matrix.toLin'_toMatrix']
  rfl

/-- Every explicitly unitarized matrix preserves the standard coordinate Hermitian pairing. -/
theorem compactRepresentationUnitarizedRepresentation_pairing
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (g : G) (first second : Fin n → ℂ) :
    coordinateHermitianPairing
        (Matrix.mulVec (compactRepresentationUnitarizedRepresentation ρ hρ g) first)
        (Matrix.mulVec (compactRepresentationUnitarizedRepresentation ρ hρ g) second) =
      coordinateHermitianPairing first second := by
  rw [compactRepresentationUnitarizedRepresentation_action,
    compactRepresentationUnitarizedRepresentation_action,
    compactRepresentationUnitarizingLinearEquiv_pairing,
    compactRepresentationAveragedPairing_invariant]
  rw [← compactRepresentationUnitarizingLinearEquiv_pairing ρ hρ]
  simp

/-- A square complex matrix preserving the standard coordinate Hermitian pairing satisfies the
exact one-sided unitary equation `star M * M = 1`. -/
theorem matrix_star_mul_self_eq_one_of_pairing_preserving
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (pairingPreserving : ∀ first second : Fin n → ℂ,
      coordinateHermitianPairing (Matrix.mulVec M first) (Matrix.mulVec M second) =
        coordinateHermitianPairing first second) :
    star M * M = 1 := by
  ext row column
  have entryPairing := pairingPreserving (Pi.single row 1) (Pi.single column 1)
  have singlePairing :
      coordinateHermitianPairing (Pi.single row 1) (Pi.single column 1) =
        if row = column then 1 else 0 := by
    unfold coordinateHermitianPairing
    rw [Finset.sum_eq_single row]
    · by_cases indices : row = column
      · subst column
        simp
      · simp [indices]
    · intro index _ index_ne
      simp [Pi.single_apply, Ne.symm index_ne]
    · simp
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one, singlePairing] at entryPairing
  unfold coordinateHermitianPairing at entryPairing
  simp only [Matrix.col_apply] at entryPairing
  rw [Matrix.star_eq_conjTranspose]
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply] using entryPairing

/-- The selected averaged-orthonormal coordinate map is an exact Mathlib equivalence between the
original representation and the explicitly unitarized representation. -/
noncomputable def compactRepresentationUnitarizingRepresentationEquiv
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    Representation.Equiv (matrixRepresentation ρ)
      (matrixRepresentation (compactRepresentationUnitarizedRepresentation ρ hρ)) :=
  Representation.Equiv.mk (compactRepresentationUnitarizingLinearEquiv ρ hρ) (fun g => by
    apply LinearMap.ext
    intro vector
    change compactRepresentationUnitarizingLinearEquiv ρ hρ
        (Matrix.mulVec (ρ g) vector) =
      Matrix.mulVec (compactRepresentationUnitarizedRepresentation ρ hρ g)
        (compactRepresentationUnitarizingLinearEquiv ρ hρ vector)
    rw [compactRepresentationUnitarizedRepresentation_action]
    simp)

/-- The explicitly conjugated representation satisfies the literal standard-coordinate unitary
matrix equation at every group element. -/
theorem compactRepresentationUnitarizedRepresentation_unitary
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (g : G) :
    star (compactRepresentationUnitarizedRepresentation ρ hρ g) *
      compactRepresentationUnitarizedRepresentation ρ hρ g = 1 :=
  matrix_star_mul_self_eq_one_of_pairing_preserving _
    (compactRepresentationUnitarizedRepresentation_pairing ρ hρ g)

end

end Mathematics
end YangMills
