/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.JointTranslationSpectrum

/-!
# Hostile probes for physical joint translation spectrum

These probes lock one normalized strongly countably-additive PVM to the exact translation
representation, expose the forward-cone support and vacuum-line projection, and ensure the mass-gap
predicate excludes actual nonzero subgap momenta rather than an unrelated Hamiltonian surrogate.
No spectral datum or positive threshold is constructed.
-/

namespace YangMills.Minkowski.JointTranslationSpectrum.Probes

/-- Zero translation has the trivial momentum character. -/
@[simp] theorem translation_character_zero
    (d : EuclideanDimension) (p : Spacetime d) :
    minkowskiTranslationCharacter d p 0 = 1 := by
  simp [minkowskiTranslationCharacter, minkowskiMomentumPairing]

/-- Zero momentum has the trivial translation character. -/
@[simp] theorem zero_momentum_character
    (d : EuclideanDimension) (a : Spacetime d) :
    minkowskiTranslationCharacter d 0 a = 1 := by
  simp [minkowskiTranslationCharacter, minkowskiMomentumPairing]

/-- Every selected translation character has unit norm. -/
theorem translation_character_norm
    (d : EuclideanDimension) (p a : Spacetime d) :
    ‖minkowskiTranslationCharacter d p a‖ = 1 := by
  rw [minkowskiTranslationCharacter, Complex.norm_exp]
  simp

/-- Zero momentum belongs to the closed future cone. -/
theorem zero_mem_closed_forward_cone (d : EuclideanDimension) :
    (0 : Spacetime d) ∈ closedForwardMomentumCone d := by
  simp [closedForwardMomentumCone]

/-- The selected future time basis momentum belongs to the closed future cone. -/
theorem time_basis_mem_closed_forward_cone (d : EuclideanDimension) :
    d.basisVector d.timeIndex ∈ closedForwardMomentumCone d := by
  constructor
  · simp [EuclideanDimension.basisVector, EuclideanDimension.timeIndex]
  · rw [d.minkowskiQuadraticForm_time_basisVector]
    norm_num

/-- Negative time orientation is rejected by the future cone. -/
theorem negative_time_basis_not_mem_closed_forward_cone (d : EuclideanDimension) :
    -d.basisVector d.timeIndex ∉ closedForwardMomentumCone d := by
  intro h
  have htime := h.1
  simp [EuclideanDimension.basisVector, EuclideanDimension.timeIndex] at htime
  norm_num at htime

variable
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Empty-set projection is exactly zero. -/
theorem exact_empty_projection (E : ProjectionValuedMeasureData X H) :
    E.projection ∅ = 0 :=
  E.projection_empty

/-- Whole-space projection is exactly the identity on every Hilbert vector. -/
theorem exact_univ_projection_apply
    (E : ProjectionValuedMeasureData X H) (ψ : H) :
    E.projection Set.univ ψ = ψ := by
  rw [E.projection_univ]
  exact one_apply_eq_self ψ

/-- Measurable projections are genuine idempotents. -/
theorem exact_projection_idempotent
    (E : ProjectionValuedMeasureData X H) (s : Set X) (hs : MeasurableSet s) :
    E.projection s * E.projection s = E.projection s :=
  E.projection_idempotent s hs

/-- Measurable projections are self-adjoint. -/
theorem exact_projection_selfAdjoint
    (E : ProjectionValuedMeasureData X H) (s : Set X) (hs : MeasurableSet s) :
    (E.projection s).adjoint = E.projection s :=
  E.projection_selfAdjoint s hs

/-- Projection multiplication is exact measurable intersection. -/
theorem exact_projection_intersection
    (E : ProjectionValuedMeasureData X H) (s t : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    E.projection s * E.projection t = E.projection (s ∩ t) :=
  E.projection_mul s t hs ht

/-- Strong countable additivity acts on the selected Hilbert vector, not merely on scalar masses. -/
theorem exact_strong_countable_additivity
    (E : ProjectionValuedMeasureData X H) (s : ℕ → Set X)
    (hs : ∀ n, MeasurableSet (s n))
    (hdisjoint : Pairwise (fun i j => Disjoint (s i) (s j))) (ψ : H) :
    Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, E.projection (s n) ψ)
      Filter.atTop (nhds (E.projection (⋃ n, s n) ψ)) :=
  E.projection_iUnion_strongly s hs hdisjoint ψ

variable
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {Hphys : Type*} [NormedAddCommGroup Hphys] [InnerProductSpace ℂ Hphys]
    [CompleteSpace Hphys] [TopologicalSpace.SeparableSpace Hphys]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift Hphys}

/-- The diagonal scalar measure is exactly coherent with the same PVM. -/
theorem exact_diagonal_measure
    (spectrum : JointTranslationSpectralData U)
    (ψ : Hphys) (s : Set (Spacetime d)) (hs : MeasurableSet s) :
    spectrum.diagonalMeasure ψ s =
      ENNReal.ofReal (Complex.re
        (inner ℂ ψ (spectrum.pvm.projection s ψ))) :=
  spectrum.diagonalMeasure_apply ψ s hs

/-- The diagonal measure used by the Fourier formula is finite, so Mathlib's nonintegrable-zero
convention cannot hide an infinite total spectral mass. -/
theorem diagonal_measure_total_mass_finite
    (spectrum : JointTranslationSpectralData U) (ψ : Hphys) :
    spectrum.diagonalMeasure ψ Set.univ < ⊤ :=
  spectrum.diagonalMeasure_univ_lt_top ψ

/-- The exact character is integrable against the selected diagonal measure. -/
theorem translation_character_integrable
    (spectrum : JointTranslationSpectralData U) (a : Spacetime d) (ψ : Hphys) :
    MeasureTheory.Integrable (fun p => minkowskiTranslationCharacter d p a)
      (spectrum.diagonalMeasure ψ) :=
  spectrum.integrable_translationCharacter a ψ

/-- The SNAG Fourier formula uses the exact physical translation unitary. -/
theorem exact_translation_fourier_diagonal
    (spectrum : JointTranslationSpectralData U) (a : Spacetime d) (ψ : Hphys) :
    inner ℂ ψ (U.translationUnitary a ψ) =
      ∫ p, minkowskiTranslationCharacter d p a ∂ spectrum.diagonalMeasure ψ :=
  spectrum.translation_fourier_diagonal a ψ

/-- An unrelated representation cannot claim the same PVM diagonal Fourier formula when its
physical translation diagonal differs. -/
theorem unrelated_translation_representation_blocked
    (spectrum : JointTranslationSpectralData U)
    (V : StronglyContinuousUnitaryPoincareRepresentation lift Hphys)
    (a : Spacetime d) (ψ : Hphys)
    (hUnrelatedClaim : inner ℂ ψ (V.translationUnitary a ψ) =
      ∫ p, minkowskiTranslationCharacter d p a ∂ spectrum.diagonalMeasure ψ)
    (hMismatch : inner ℂ ψ (V.translationUnitary a ψ) ≠
      inner ℂ ψ (U.translationUnitary a ψ)) : False := by
  apply hMismatch
  rw [hUnrelatedClaim, spectrum.translation_fourier_diagonal a ψ]

/-- The full Poincaré representation transports the exact PVM by its projected Lorentz action. -/
theorem exact_poincare_spectral_covariance
    (spectrum : JointTranslationSpectralData U) (g : G)
    (s : Set (Spacetime d)) (hs : MeasurableSet s) :
    U.unitary g * spectrum.pvm.projection s * U.unitary (g⁻¹) =
      spectrum.pvm.projection (lorentzMomentumImage lift g s) :=
  spectrum.poincare_covariant g s hs

/-- The closed forward cone carries the full physical projection. -/
theorem exact_forward_cone_full
    (spectrum : ForwardConeJointTranslationSpectrumData U) :
    spectrum.joint.pvm.projection (closedForwardMomentumCone d) = 1 :=
  spectrum.forward_cone_full

/-- The derived Hamiltonian spectral projection is normalized and remains a view of the same PVM. -/
theorem exact_hamiltonian_spectral_projection_univ
    (spectrum : ForwardConeJointTranslationSpectrumData U) :
    physicalHamiltonianSpectralProjection spectrum Set.univ = 1 :=
  physicalHamiltonianSpectralProjection_univ spectrum

/-- A forward-cone datum annihilates the exact complement projection. -/
theorem exact_outside_forward_cone_zero
    (spectrum : ForwardConeJointTranslationSpectrumData U) :
    spectrum.joint.pvm.projection (closedForwardMomentumCone d)ᶜ = 0 :=
  spectrum.outside_forward_cone_zero

/-- A singleton at explicit negative-time momentum has zero spectral projection. -/
theorem negative_time_singleton_projection_zero
    (spectrum : ForwardConeJointTranslationSpectrumData U) :
    spectrum.joint.pvm.projection
      ({-d.basisVector d.timeIndex} : Set (Spacetime d)) = 0 := by
  apply spectrum.projection_eq_zero_of_disjoint_forwardCone
    (measurableSet_singleton (-d.basisVector d.timeIndex))
  intro p hp
  have hpEq : p = -d.basisVector d.timeIndex := by simpa using hp
  subst p
  exact negative_time_basis_not_mem_closed_forward_cone d

variable (vacuumData : PoincareInvariantVacuumData U)
    (spectrum : ForwardConeJointTranslationSpectrumData U) (Δ : ℝ)

/-- PVM normalization cannot be realized by the zero projection family on the nonzero physical
Hilbert space. -/
theorem empty_projection_family_blocked
    (vacuum : PoincareInvariantVacuumData U) :
    spectrum.joint.pvm.projection Set.univ ≠ 0 := by
  intro hzero
  have happly := congrArg
    (fun T : Hphys →L[ℂ] Hphys => T vacuum.vacuum) hzero
  rw [spectrum.joint.pvm.projection_univ] at happly
  simp only [one_apply_eq_self, zero_apply] at happly
  exact vacuum.vacuum_ne_zero happly

/-- Forward-cone support prevents the complement projection from being the identity. -/
theorem full_outside_projection_blocked
    (vacuum : PoincareInvariantVacuumData U) :
    spectrum.joint.pvm.projection (closedForwardMomentumCone d)ᶜ ≠ 1 := by
  intro hfull
  have hzeroOne : (0 : Hphys →L[ℂ] Hphys) = 1 :=
    spectrum.outside_forward_cone_zero.symm.trans hfull
  have happly := congrArg
    (fun T : Hphys →L[ℂ] Hphys => T vacuum.vacuum) hzeroOne
  simp only [zero_apply, one_apply_eq_self] at happly
  exact vacuum.vacuum_ne_zero happly.symm

/-- A mass-gap declaration carries a strictly positive threshold. -/
theorem mass_gap_threshold_positive
    (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) : 0 < Δ :=
  hgap.1

/-- The zero-momentum spectral projection is exactly the selected normalized vacuum line. -/
theorem exact_zero_momentum_vacuum_projection
    (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) (ψ : Hphys) :
    spectrum.joint.pvm.projection ({0} : Set (Spacetime d)) ψ =
      inner ℂ vacuumData.vacuum ψ • vacuumData.vacuum :=
  hgap.2.1 ψ

/-- In particular, the zero-momentum projection fixes the exact selected vacuum. -/
theorem zero_momentum_projection_fixes_vacuum
    (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    spectrum.joint.pvm.projection ({0} : Set (Spacetime d)) vacuumData.vacuum =
      vacuumData.vacuum := by
  rw [hgap.2.1 vacuumData.vacuum]
  rw [inner_self_eq_norm_sq_to_K, vacuumData.norm_eq_one]
  norm_num

/-- The same joint PVM vanishes on the entire nonzero future subgap region. -/
theorem exact_nonzero_future_subgap_projection_zero
    (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    spectrum.joint.pvm.projection (nonzeroFutureSubgapMomentumRegion d Δ) = 0 :=
  hgap.2.2.1

/-- The invariant-mass formulation implies the exact Clay Hamiltonian subgap projection law. -/
theorem exact_positive_energy_subgap_projection_zero
    (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    spectrum.joint.pvm.projection (positiveEnergySubgapRegion d Δ) = 0 :=
  hgap.positiveEnergySubgap_projection_zero

/-- The exact Hamiltonian spectral pushforward has no spectrum in Clay's interval `(0, Δ)`. -/
theorem exact_hamiltonian_Ioo_projection_zero
    (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    physicalHamiltonianSpectralProjection spectrum (Set.Ioo 0 Δ) = 0 :=
  hgap.hamiltonian_Ioo_projection_zero

/-- A gap requires an actual nonzero projection in a bounded positive-energy band above `Δ`. -/
theorem bounded_positive_energy_excitation_required
    (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    ∃ E : ℝ, 0 < E ∧ Δ ≤ E ∧
      spectrum.joint.pvm.projection (boundedPositiveEnergyExcitationRegion d E) ≠ 0 :=
  hgap.2.2.2

/-- The same nonzero bounded band is visible through the derived Hamiltonian spectral interface. -/
theorem bounded_hamiltonian_excitation_required
    (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    ∃ E : ℝ, 0 < E ∧ Δ ≤ E ∧
      physicalHamiltonianSpectralProjection spectrum (Set.Ioc 0 E) ≠ 0 :=
  hgap.exists_boundedHamiltonian_excitation

/-- The same excitation provides a finite invariant-mass scale for the selected threshold. -/
theorem gap_has_finite_upper_scale
    (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    ∃ M : ℝ, 0 < M ∧ Δ ≤ M ∧
      spectrum.joint.pvm.projection (finiteMassExcitationRegion d M) ≠ 0 :=
  hgap.exists_finiteMass_scale

/-- Consequently the entire nonvacuum momentum sector cannot have zero projection. -/
theorem vacuum_only_spectrum_blocked
    (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    spectrum.joint.pvm.projection (({0} : Set (Spacetime d))ᶜ) ≠ 0 :=
  hgap.nonvacuum_projection_ne_zero

/-- Every actual nonzero future momentum below the selected invariant-mass threshold is excluded. -/
theorem exact_subgap_singleton_projection_zero
    (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ)
    (p : Spacetime d) (hfuture : p ∈ closedForwardMomentumCone d)
    (hp : p ≠ 0) (hmass : d.minkowskiQuadraticForm p < Δ ^ 2) :
    spectrum.joint.pvm.projection ({p} : Set (Spacetime d)) = 0 :=
  hgap.singleton_projection_zero hfuture hp hmass

/-- A nonpositive proposed threshold cannot satisfy the mass-gap predicate. -/
theorem nonpositive_threshold_blocked
    (hΔ : Δ ≤ 0) : ¬ HasPhysicalJointSpectralMassGap vacuumData spectrum Δ := by
  intro hgap
  exact (not_lt_of_ge hΔ) hgap.1

end YangMills.Minkowski.JointTranslationSpectrum.Probes
