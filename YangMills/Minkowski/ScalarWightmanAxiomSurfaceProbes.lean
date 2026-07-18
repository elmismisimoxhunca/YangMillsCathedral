/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.ScalarWightmanAxiomSurface

/-!
# Hostile probes for the integrated scalar Wightman surface

The probes make the shared indexing visible: field covariance/locality/cyclicity use the exact field
on the exact common domain, while spectral and optional gap statements use the exact representation
and vacuum that index that domain. No surface or gap witness is constructed.
-/

namespace YangMills.Minkowski.ScalarWightmanAxiomSurface.Probes

variable
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {fieldData : ScalarWightmanFieldOnCommonDomainData D}
    (surface : ScalarWightmanAxiomSurfaceData fieldData)

/-- Covariance is for the exact field datum indexing the surface. -/
theorem exact_covariance_surface
    (S : ScalarWightmanAxiomSurfaceData fieldData) :
    ScalarWightmanFieldCovarianceData fieldData :=
  S.covariance

/-- Cyclicity is for finite words in that exact field/adjoint acting on the exact domain vacuum. -/
theorem exact_cyclicity_surface
    (S : ScalarWightmanAxiomSurfaceData fieldData) :
    ScalarWightmanVacuumCyclicity fieldData :=
  S.cyclicity

/-- Locality is for that exact field/adjoint on that exact common domain. -/
theorem exact_locality_surface
    (S : ScalarWightmanAxiomSurfaceData fieldData) :
    ScalarWightmanLocalityData fieldData :=
  S.locality

/-- The spectral datum is tied to the exact representation from which the domain action derives. -/
theorem exact_forward_spectrum_surface
    (S : ScalarWightmanAxiomSurfaceData fieldData) :
    S.spectrum.joint.pvm.projection (closedForwardMomentumCone d)ᶜ = 0 :=
  S.spectrum.outside_forward_cone_zero

/-- The surface's SNAG formula uses the same physical translation representation. -/
theorem exact_surface_translation_fourier
    (a : Spacetime d) (ψ : H) :
    inner ℂ ψ (U.translationUnitary a ψ) =
      ∫ p, minkowskiTranslationCharacter d p a ∂
        surface.spectrum.joint.diagonalMeasure ψ :=
  surface.spectrum.joint.translation_fourier_diagonal a ψ

/-- A separately requested mass gap is exactly the physical joint-PVM predicate, not a new field or
Hamiltonian surrogate. -/
theorem exact_optional_mass_gap
    (Δ : ℝ) (hgap : surface.HasPhysicalMassGap Δ) :
    HasPhysicalJointSpectralMassGap vacuumData surface.spectrum Δ :=
  hgap

/-- Any optional mass-gap threshold remains strictly positive. -/
theorem optional_mass_gap_positive
    (Δ : ℝ) (hgap : surface.HasPhysicalMassGap Δ) : 0 < Δ :=
  hgap.1

/-- The optional gap has Clay's exact same-PVM Hamiltonian interval consequence. -/
theorem optional_mass_gap_hamiltonian_Ioo_zero
    (Δ : ℝ) (hgap : surface.HasPhysicalMassGap Δ) :
    physicalHamiltonianSpectralProjection surface.spectrum (Set.Ioo 0 Δ) = 0 :=
  hgap.hamiltonian_Ioo_projection_zero

/-- A nonpositive number cannot be smuggled in as the surface's optional mass gap. -/
theorem nonpositive_optional_gap_blocked
    (Δ : ℝ) (hΔ : Δ ≤ 0) : ¬ surface.HasPhysicalMassGap Δ := by
  intro hgap
  exact (not_lt_of_ge hΔ) hgap.1

end YangMills.Minkowski.ScalarWightmanAxiomSurface.Probes
