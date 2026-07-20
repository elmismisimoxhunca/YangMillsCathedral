/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.LocalObservableCovarianceCoverage

/-!
# Hostile probes for exhaustive local-observable covariance coverage

The probes expose exhaustive classification, exact residual-label coverage and covariance, and the
separate scalar/stress disjointness requirement. No observable datum is constructed.
-/

namespace YangMills.Minkowski.LocalObservableCovarianceCoverage.Probes

variable
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    {covariance : CovariantLocalObservableFamilyData family}
    {stress : LocalStressEnergyTensorData family}

/-- Every exact family label reaches one of the three transformation interfaces. -/
theorem exact_exhaustive_covariance_classification
    (coverage : LocalObservableCovarianceCoverageData covariance stress)
    (A : family.Label) :
    A ∈ covariance.scalarLabel ∨
      (∃ μ ν, A = stress.componentLabel μ ν) ∨
      A ∈ residualCovariantObservableLabelSet covariance stress :=
  coverage.label_scalar_or_stress_or_residual A

/-- A label outside both specialized sectors is covered by an exact finite projected-Lorentz multiplet. -/
theorem exact_residual_label_coverage
    (coverage : LocalObservableCovarianceCoverageData covariance stress)
    (A : family.Label)
    (hA : A ∈ residualCovariantObservableLabelSet covariance stress) :
    ∃ (m : coverage.residualMultipletCover.Multiplet)
      (i : Fin (coverage.residualMultipletCover.extraComponentCount m + 1)),
      (coverage.residualMultipletCover.multiplet m).componentLabel i = A :=
  coverage.residualMultipletCover.covers A hA

/-- Residual coverage acts on the original family operator and physical domain, not a disconnected
copy. -/
theorem exact_residual_label_covariance
    (coverage : LocalObservableCovarianceCoverageData covariance stress)
    (A : family.Label)
    (hA : A ∈ residualCovariantObservableLabelSet covariance stress) :
    ∃ (m : coverage.residualMultipletCover.Multiplet)
      (i : Fin (coverage.residualMultipletCover.extraComponentCount m + 1)),
      (coverage.residualMultipletCover.multiplet m).componentLabel i = A ∧
      ∀ (g : G) (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain),
        D.domainUnitary g
            (family.operator A f ((D.domainUnitary g).symm ψ)) =
          ∑ j,
            ((coverage.residualMultipletCover.multiplet m).mixingRepresentation g
              (Pi.single i 1) j) •
              family.operator
                ((coverage.residualMultipletCover.multiplet m).componentLabel j)
                (pullbackScalarMinkowskiSchwartzTestFunction d (lift.projection g) f) ψ := by
  rcases coverage.residualMultipletCover.covers A hA with ⟨m, i, hlabel⟩
  refine ⟨m, i, hlabel, ?_⟩
  intro g f ψ
  rw [← hlabel]
  exact (coverage.residualMultipletCover.multiplet m).component_covariant i g f ψ

/-- The specialized scalar and stress sectors cannot overlap when the separation contract is
present. -/
theorem scalar_stress_overlap_blocked
    (separation : ScalarStressCovarianceSeparationData covariance stress)
    (μ ν : d.CoordinateIndex) :
    stress.componentLabel μ ν ∉ covariance.scalarLabel :=
  separation.componentLabel_not_mem_scalar μ ν

/-- No unused component of a residual covering multiplet can silently import a scalar or stress
label and assign it a second mixing law. -/
theorem exact_residual_multiplet_component_exclusions
    (coverage : LocalObservableCovarianceCoverageData covariance stress)
    (m : coverage.residualMultipletCover.Multiplet)
    (i : Fin (coverage.residualMultipletCover.extraComponentCount m + 1)) :
    (coverage.residualMultipletCover.multiplet m).componentLabel i ∉
        covariance.scalarLabel ∧
      ∀ μ ν,
        (coverage.residualMultipletCover.multiplet m).componentLabel i ≠
          stress.componentLabel μ ν :=
  coverage.residualMultiplet_components_mem m i

/-- Residual labels cannot be silently reclassified as scalar or as stress components. -/
theorem exact_residual_exclusions
    (A : family.Label)
    (hA : A ∈ residualCovariantObservableLabelSet covariance stress) :
    A ∉ covariance.scalarLabel ∧ ∀ μ ν, A ≠ stress.componentLabel μ ν :=
  hA

end YangMills.Minkowski.LocalObservableCovarianceCoverage.Probes
