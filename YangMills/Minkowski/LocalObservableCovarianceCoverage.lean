/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.FiniteCovariantObservableMultipletAdjoint
import YangMills.Minkowski.LocalStressEnergyTensor

/-!
# Exhaustive covariance coverage for one local-observable family

The scalar-family interface, stress-tensor interface, and general finite-component Wightman
transformation law have independently meaningful scopes. This module joins them without assigning
simultaneous unrelated transformation laws to stress labels. This bosonic local-observable family
uses projected-Lorentz multiplets; spinorial fields require a separate graded-locality surface.

Every label is classified as scalar, an exact stress component, or residual. Only residual labels
are required to occur in finite projected-Lorentz multiplets. Existing scalar/stress disjointness makes
the first two cases nonoverlapping. No field, representation, observable family, or theory is
constructed.
-/

namespace YangMills.Minkowski

universe uLift uH uLabel

/-- Labels not already governed by the explicit scalar law or by the exact rank-two stress law. -/
def residualCovariantObservableLabelSet
    {d : EuclideanDimension} {G : Type uLift}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData.{uLift, uH, uLabel} D}
    (covariance : CovariantLocalObservableFamilyData family)
    (stress : LocalStressEnergyTensorData family) : Set family.Label :=
  {A | A ∉ covariance.scalarLabel ∧ ∀ μ ν, A ≠ stress.componentLabel μ ν}

/-- Exhaustive covariance infrastructure for one exact observable family. Scalar labels retain their
scalar pullback law, stress labels retain their separately supplied rank-two coefficient law, and
only the remaining bosonic observable labels are covered by finite projected-Lorentz multiplets. -/
structure LocalObservableCovarianceCoverageData
    {d : EuclideanDimension} {G : Type uLift}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData.{uLift, uH, uLabel} D}
    (covariance : CovariantLocalObservableFamilyData family)
    (stress : LocalStressEnergyTensorData family) where
  residualMultipletCover : FiniteLorentzCovariantObservableCoverData family
    (residualCovariantObservableLabelSet covariance stress)
  /-- Every component of every supplied residual multiplet is itself residual. Thus scalar and
  stress labels cannot silently receive a second unrelated multiplet law as an unused component. -/
  residualMultiplet_components_mem : ∀ m i,
    (residualMultipletCover.multiplet m).componentLabel i ∈
      residualCovariantObservableLabelSet covariance stress
  /-- Every residual multiplet has an exact adjoint partner inside the same residual cover, with
  existing family adjoint labels and coefficientwise conjugate mixing. -/
  residualMultiplet_adjointPartner : ∀ m,
    ∃ n, Nonempty (FiniteLiftCovariantObservableMultipletAdjointPartnerData covariance
      (residualMultipletCover.multiplet m).toFiniteLiftCovariantObservableMultipletData
      (residualMultipletCover.multiplet n).toFiniteLiftCovariantObservableMultipletData)

/-- Every original family label is governed by the scalar interface, is an exact stress component,
or belongs to the residual finite-multiplet cover. This is exhaustive classical classification, not
an added witness field. -/
theorem LocalObservableCovarianceCoverageData.label_scalar_or_stress_or_residual
    {d : EuclideanDimension} {G : Type uLift}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData.{uLift, uH, uLabel} D}
    {covariance : CovariantLocalObservableFamilyData family}
    {stress : LocalStressEnergyTensorData family}
    (_coverage : LocalObservableCovarianceCoverageData covariance stress)
    (A : family.Label) :
    A ∈ covariance.scalarLabel ∨
      (∃ μ ν, A = stress.componentLabel μ ν) ∨
      A ∈ residualCovariantObservableLabelSet covariance stress := by
  classical
  by_cases hscalar : A ∈ covariance.scalarLabel
  · exact Or.inl hscalar
  · by_cases hstress : ∃ μ ν, A = stress.componentLabel μ ν
    · exact Or.inr (Or.inl hstress)
    · refine Or.inr (Or.inr ⟨hscalar, ?_⟩)
      intro μ ν heq
      exact hstress ⟨μ, ν, heq⟩

end YangMills.Minkowski
