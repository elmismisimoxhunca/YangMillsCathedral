/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanCovariance
import YangMills.Minkowski.WightmanCyclicity
import YangMills.Minkowski.WightmanLocality
import YangMills.Minkowski.JointTranslationSpectrum

/-!
# Integrated scalar Wightman axiom surface

This record wires covariance, cyclicity, scalar bosonic locality, and forward-cone joint spectral
data to the exact same representation, normalized vacuum, common domain, and field datum. It is an
acceptance surface for a scalar Wightman sector, not an inhabitant and not yet a Yang–Mills theory:
gauge-invariant observable interpretation and Euclidean reconstruction coherence remain separate
obligations.

A physical mass gap is deliberately not a field of the Wightman axiom record. It remains an
additional predicate on this record's exact joint PVM and exact selected vacuum, so the axioms do
not silently assert the Clay conclusion.
-/

namespace YangMills.Minkowski

/-- Integrated scalar Wightman requirements on one exact field/domain/vacuum/representation chain. -/
structure ScalarWightmanAxiomSurfaceData
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (fieldData : ScalarWightmanFieldOnCommonDomainData D) where
  /-- Exact scalar covariance under the same restricted physical unitaries. -/
  covariance : ScalarWightmanFieldCovarianceData fieldData
  /-- Exact vacuum cyclicity for finite field/adjoint words. -/
  cyclicity : ScalarWightmanVacuumCyclicity fieldData
  /-- Exact scalar bosonic locality on the same common domain. -/
  locality : ScalarWightmanLocalityData fieldData
  /-- Exact forward-cone joint PVM tied to the same physical translations. -/
  spectrum : ForwardConeJointTranslationSpectrumData U

/-- The Clay mass-gap predicate specialized to the exact vacuum and spectrum of an integrated
scalar Wightman surface. This definition still does not assert that any threshold exists. -/
def ScalarWightmanAxiomSurfaceData.HasPhysicalMassGap
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {fieldData : ScalarWightmanFieldOnCommonDomainData D}
    (surface : ScalarWightmanAxiomSurfaceData fieldData) (Δ : ℝ) : Prop :=
  HasPhysicalJointSpectralMassGap vacuumData surface.spectrum Δ

end YangMills.Minkowski
