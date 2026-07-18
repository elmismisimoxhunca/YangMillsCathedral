/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.TemperedLocalObservableProducts
import YangMills.Minkowski.WightmanCovariance
import YangMills.Minkowski.WightmanLocality
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Local stress-energy tensor on one observable/domain chain

Clay/Jaffe–Witten §4 explicitly includes existence of a stress tensor among the required
short-distance predictions. Blaschke–Gieres–Reboud–Schweda 2016, §§2.1–2.2, supplies the
conservation/symmetry/gauge-theory semantics, while Streater–Wightman supplies quantum
common-domain covariance/locality/adjoint semantics. This module defines a source-facing
acceptance interface inside one exact local-observable family. Components are symmetric, Hermitian
operator-valued tempered distributions, transform by an explicit contravariant rank-two Lorentz convention under the same
Poincaré representation, and obey weak distributional conservation.

The coordinate tensor convention is an explicit formalization decision because the Clay statement
does not print a component formula. No tensor datum, translation-generator Ward identity, trace
identity/anomaly, renormalization theorem, theory, or mass gap is constructed.
-/

namespace YangMills.Minkowski

/-- Exact Schwartz directional derivative along one canonical spacetime coordinate. -/
noncomputable def minkowskiSchwartzCoordinateDerivative
    {d : EuclideanDimension} (μ : d.CoordinateIndex) :
    ScalarMinkowskiSchwartzTestFunction d →L[ℂ]
      ScalarMinkowskiSchwartzTestFunction d :=
  LineDeriv.lineDerivOpCLM ℂ (ScalarMinkowskiSchwartzTestFunction d) (d.basisVector μ)

/-- Matrix coefficient `Λ(A⁻¹)^μ_ρ` of the inverse selected Lorentz transformation in the
canonical coordinate basis. This matches the established `U(g) Φ(f) U(g)⁻¹` and inverse-affine
test-pullback convention. -/
def lorentzCoordinateCoefficient
    {d : EuclideanDimension}
    (p : ProperOrthochronousPoincareTransformation d)
    (μ ρ : d.CoordinateIndex) : ℝ :=
  p.lorentz.linear.symm (d.basisVector ρ) μ

/-- Complex coefficient `Λ(A⁻¹)^μ_ρ Λ(A⁻¹)^ν_σ` for the contravariant rank-two tensor
convention. -/
def stressTensorTransformCoefficient
    {d : EuclideanDimension}
    (p : ProperOrthochronousPoincareTransformation d)
    (μ ν ρ σ : d.CoordinateIndex) : ℂ :=
  (lorentzCoordinateCoefficient p μ ρ * lorentzCoordinateCoefficient p ν σ : ℝ)

/-- Distinguished coordinate-zero time index. -/
abbrev stressTensorTimeIndex (d : EuclideanDimension) : d.CoordinateIndex :=
  d.timeIndex

/-- Symmetric Hermitian conserved rank-two local stress tensor represented inside the same exact
local-observable family and common Poincaré/domain chain. -/
structure LocalStressEnergyTensorData
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (family : TemperedLocalObservableFamilyData D) where
  /-- Exact family label for each ordered tensor component. -/
  componentLabel : d.CoordinateIndex → d.CoordinateIndex → family.Label
  /-- Tensor symmetry is represented at the label level. -/
  componentLabel_symmetric : ∀ μ ν, componentLabel μ ν = componentLabel ν μ
  /-- Every component is Hermitian on the common domain with conjugated scalar test. -/
  component_adjoint_relation : ∀ μ ν ψ φ f,
    @inner ℂ H _ ψ.val (family.operator (componentLabel μ ν) f φ).val =
      @inner ℂ H _
        (family.operator (componentLabel μ ν)
          (conjugateScalarMinkowskiSchwartzTestFunction f) ψ).val φ.val
  /-- Explicit contravariant rank-two Poincaré covariance on the same restricted domain unitary. -/
  component_covariant : ∀ μ ν g f ψ,
    D.domainUnitary g
        (family.operator (componentLabel μ ν) f ((D.domainUnitary g).symm ψ)) =
      ∑ ρ, ∑ σ,
        stressTensorTransformCoefficient (lift.projection g) μ ν ρ σ •
          family.operator (componentLabel ρ σ)
            (pullbackScalarMinkowskiSchwartzTestFunction d (lift.projection g) f) ψ
  /-- Every stress component is local relative to every label in the same family. In particular,
  choosing another component label gives component-component locality. -/
  component_local_with_family : ∀ μ ν A f g,
    HaveSpacelikeSeparatedTopologicalSupports f g →
      ∀ ψ,
        family.operator (componentLabel μ ν) f (family.operator A g ψ) =
          family.operator A g (family.operator (componentLabel μ ν) f ψ)
  /-- Weak distributional conservation `∂_μ T^{μν} = 0` on every common-domain vector. The usual
  distributional derivative contributes an overall minus sign to test-function differentiation,
  which is immaterial in an equality to zero. -/
  weakly_conserved : ∀ ν f ψ,
    ∑ μ, family.operator (componentLabel μ ν)
      (minkowskiSchwartzCoordinateDerivative μ f) ψ = 0
  /-- The energy-density component is not the unit label. -/
  energyDensityLabel_ne_unit :
    componentLabel (stressTensorTimeIndex d) (stressTensorTimeIndex d) ≠ family.unitLabel
  /-- Energy density acts nontrivially and differently from the unit on one exact test/vector. -/
  energyDensity_nontrivial :
    ∃ (f : ScalarMinkowskiSchwartzTestFunction d) (φ : D.domain),
      family.operator
        (componentLabel (stressTensorTimeIndex d) (stressTensorTimeIndex d)) f φ ≠ 0 ∧
      family.operator
        (componentLabel (stressTensorTimeIndex d) (stressTensorTimeIndex d)) f φ ≠
          family.operator family.unitLabel f φ

/-- Symmetry gives exact equality of the corresponding same-family operators. -/
theorem LocalStressEnergyTensorData.component_operator_symmetric
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    (stress : LocalStressEnergyTensorData family)
    (μ ν : d.CoordinateIndex) :
    family.operator (stress.componentLabel μ ν) =
      family.operator (stress.componentLabel ν μ) := by
  rw [stress.componentLabel_symmetric]

end YangMills.Minkowski
