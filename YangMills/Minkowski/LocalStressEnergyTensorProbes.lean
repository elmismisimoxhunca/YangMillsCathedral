/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.LocalStressEnergyTensor

/-!
# Hostile probes for local stress-energy tensors

The probes expose the exact derivative and inverse-Lorentz conventions, symmetry, Hermiticity,
tensor covariance, locality, weak conservation, coherent tempered matrix elements, and a nonzero
non-unit energy density. No tensor datum is constructed.
-/

namespace YangMills.Minkowski.LocalStressEnergyTensor.Probes

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

/-- The coordinate derivative is pointwise the Fréchet derivative along the established basis. -/
theorem exact_coordinate_derivative
    (μ : d.CoordinateIndex) (f : ScalarMinkowskiSchwartzTestFunction d) (x : Spacetime d) :
    minkowskiSchwartzCoordinateDerivative μ f x =
      fderiv ℝ (f : Spacetime d → ℂ) x (d.basisVector μ) := by
  rw [minkowskiSchwartzCoordinateDerivative, LineDeriv.lineDerivOpCLM_apply]
  rfl

/-- Rank-two covariance uses entries of the inverse Lorentz transformation, not the forward one. -/
theorem exact_inverse_lorentz_coefficient
    (p : ProperOrthochronousPoincareTransformation d) (μ ρ : d.CoordinateIndex) :
    lorentzCoordinateCoefficient p μ ρ =
      p.lorentz.linear.symm (d.basisVector ρ) μ :=
  rfl

/-- Tensor symmetry is exact at both label and operator levels. -/
theorem exact_component_symmetry
    (stress : LocalStressEnergyTensorData family)
    (μ ν : d.CoordinateIndex) :
    stress.componentLabel μ ν = stress.componentLabel ν μ ∧
      family.operator (stress.componentLabel μ ν) =
        family.operator (stress.componentLabel ν μ) :=
  ⟨stress.componentLabel_symmetric μ ν,
    stress.component_operator_symmetric μ ν⟩

/-- A stress component cannot silently be governed by both scalar and rank-two covariance laws. -/
theorem scalar_tensor_covariance_overlap_blocked
    (covariance : CovariantLocalObservableFamilyData family)
    (stress : LocalStressEnergyTensorData family)
    (separation : ScalarStressCovarianceSeparationData covariance stress)
    (μ ν : d.CoordinateIndex) :
    stress.componentLabel μ ν ∉ covariance.scalarLabel :=
  separation.componentLabel_not_mem_scalar μ ν

/-- Every Hermitian stress component is fixed by the exact global family adjoint label. -/
theorem exact_stress_component_adjoint_label
    (covariance : CovariantLocalObservableFamilyData family)
    (stress : LocalStressEnergyTensorData family)
    (separation : ScalarStressCovarianceSeparationData covariance stress)
    (μ ν : d.CoordinateIndex) :
    covariance.adjointLabel (stress.componentLabel μ ν) = stress.componentLabel μ ν :=
  separation.componentLabel_adjoint μ ν

/-- Every component obeys the exact same-domain Hermitian relation. -/
theorem exact_component_adjoint_relation
    (stress : LocalStressEnergyTensorData family)
    (μ ν : d.CoordinateIndex) (ψ φ : D.domain)
    (f : ScalarMinkowskiSchwartzTestFunction d) :
    @inner ℂ H _ ψ.val (family.operator (stress.componentLabel μ ν) f φ).val =
      @inner ℂ H _
        (family.operator (stress.componentLabel μ ν)
          (conjugateScalarMinkowskiSchwartzTestFunction f) ψ).val φ.val :=
  stress.component_adjoint_relation μ ν ψ φ f

/-- Covariance uses the same lift element, projected Lorentz matrix and domain unitary. -/
theorem exact_rank_two_covariance
    (stress : LocalStressEnergyTensorData family)
    (μ ν : d.CoordinateIndex) (g : G)
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    D.domainUnitary g
        (family.operator (stress.componentLabel μ ν) f ((D.domainUnitary g).symm ψ)) =
      ∑ ρ, ∑ σ,
        stressTensorTransformCoefficient (lift.projection g) μ ν ρ σ •
          family.operator (stress.componentLabel ρ σ)
            (pullbackScalarMinkowskiSchwartzTestFunction d (lift.projection g) f) ψ :=
  stress.component_covariant μ ν g f ψ

/-- The affine test action in tensor covariance remains the exact inverse-affine pullback. -/
theorem exact_covariance_test_pullback
    (p : ProperOrthochronousPoincareTransformation d) (f : ScalarMinkowskiSchwartzTestFunction d)
    (x : Spacetime d) :
    pullbackScalarMinkowskiSchwartzTestFunction d p f x =
      f (p.lorentz.linear.symm (x - p.translation)) :=
  pullbackScalarMinkowskiSchwartzTestFunction_apply d p f x

/-- Every component is local relative to every label in the exact same family. -/
theorem exact_component_locality
    (stress : LocalStressEnergyTensorData family)
    (μ ν : d.CoordinateIndex) (A : family.Label)
    (f g : ScalarMinkowskiSchwartzTestFunction d)
    (hsep : HaveSpacelikeSeparatedTopologicalSupports f g) (ψ : D.domain) :
    family.operator (stress.componentLabel μ ν) f (family.operator A g ψ) =
      family.operator A g (family.operator (stress.componentLabel μ ν) f ψ) :=
  stress.component_local_with_family μ ν A f g hsep ψ

/-- Conservation is the exact weak distributional divergence identity. -/
theorem exact_weak_conservation
    (stress : LocalStressEnergyTensorData family)
    (ν : d.CoordinateIndex) (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    ∑ μ, family.operator (stress.componentLabel μ ν)
      (minkowskiSchwartzCoordinateDerivative μ f) ψ = 0 :=
  stress.weakly_conserved ν f ψ

/-- Every stress component inherits an actual coherent tempered matrix element from the same family. -/
theorem exact_component_tempered_matrix_element
    (stress : LocalStressEnergyTensorData family)
    (μ ν : d.CoordinateIndex) (ψ φ : D.domain)
    (f : ScalarMinkowskiSchwartzTestFunction d) :
    family.matrixElement (stress.componentLabel μ ν) ψ φ f =
      @inner ℂ H _ ψ.val (family.operator (stress.componentLabel μ ν) f φ).val :=
  family.matrixElement_coherent _ ψ φ f

/-- The energy-density label cannot be replaced by the unit label. -/
theorem unit_energy_density_blocked
    (stress : LocalStressEnergyTensorData family) :
    stress.componentLabel (stressTensorTimeIndex d) (stressTensorTimeIndex d) ≠
      family.unitLabel :=
  stress.energyDensityLabel_ne_unit

/-- A zero or duplicate-unit energy density cannot pass. -/
theorem zero_energy_density_blocked
    (stress : LocalStressEnergyTensorData family) :
    ∃ (f : ScalarMinkowskiSchwartzTestFunction d) (φ : D.domain),
      family.operator
        (stress.componentLabel (stressTensorTimeIndex d) (stressTensorTimeIndex d)) f φ ≠ 0 ∧
      family.operator
        (stress.componentLabel (stressTensorTimeIndex d) (stressTensorTimeIndex d)) f φ ≠
          family.operator family.unitLabel f φ :=
  stress.energyDensity_nontrivial

end YangMills.Minkowski.LocalStressEnergyTensor.Probes
