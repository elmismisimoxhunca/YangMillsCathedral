/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.LocalStressEnergyTensor
import YangMills.Minkowski.JointTranslationSpectrum
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Stress-energy charges and physical translation generators

Blaschke–Gieres–Reboud–Schweda 2016, §2.1.1, identifies spatial integrals of `T^{0ν}` with
energy-momentum charges and states that they generate spacetime translations. This module turns
that missing connection into an explicit acceptance bridge on the exact local-observable/domain/
representation/PVM chain.

Because a constant spatial smearing and a sharp time slice are not Schwartz tests, the bridge uses
a designated sequence whose temporal profiles approach a delta function and whose spatial profiles
have expanding unit plateaux. The sequence is part of the checked data rather than hidden behind a
formal symbol `∫ T^{0ν}`. No cutoff sequence, generator, tensor, theory, or mass gap is constructed.
-/

namespace YangMills.Minkowski

open MeasureTheory

/-- Spatial coordinate vector obtained by deleting the distinguished time coordinate. -/
def minkowskiSpatialCoordinates (d : EuclideanDimension) (x : Spacetime d) :
    Fin d.spatialDimension → ℝ :=
  fun i => x (d.spatialIndexSucc i)

/-- A controlled Schwartz approximation to a time-slice spatial charge integral. -/
structure StressTensorChargeCutoffData (d : EuclideanDimension) where
  /-- Temporal mollifier at each stage. -/
  temporalProfile : ℕ → SchwartzMap ℝ ℂ
  /-- Spatial cutoff at each stage. -/
  spatialProfile : ℕ → SchwartzMap (Fin d.spatialDimension → ℝ) ℂ
  /-- The actual spacetime Schwartz test used to smear `T^{0ν}`. -/
  cutoff : ℕ → ScalarMinkowskiSchwartzTestFunction d
  /-- Positive shrinking temporal half-width. -/
  temporalWidth : ℕ → ℝ
  temporalWidth_pos : ∀ n, 0 < temporalWidth n
  temporalWidth_tendsto_zero : Filter.Tendsto temporalWidth Filter.atTop (nhds 0)
  /-- Positive expanding spatial plateau radius. -/
  spatialRadius : ℕ → ℝ
  spatialRadius_pos : ∀ n, 0 < spatialRadius n
  spatialRadius_tendsto_atTop : Filter.Tendsto spatialRadius Filter.atTop Filter.atTop
  /-- Temporal profiles have integral one. -/
  temporal_integral_one : ∀ n, ∫ t, temporalProfile n t = 1
  /-- Temporal support shrinks to the selected zero-time slice. -/
  temporal_support : ∀ n,
    Function.support (temporalProfile n) ⊆ {t | |t| ≤ temporalWidth n}
  /-- The temporal profiles converge to the time-zero delta distribution on every Schwartz test.
  This excludes derivative contamination that support shrinkage and integral normalization alone do
  not detect. -/
  temporal_tendsto_delta : ∀ f : SchwartzMap ℝ ℂ,
    Filter.Tendsto (fun n => ∫ t, temporalProfile n t * f t)
      Filter.atTop (nhds (f 0))
  /-- Spatial cutoffs are exactly one on an expanding norm ball. -/
  spatial_plateau : ∀ n y, ‖y‖ ≤ spatialRadius n → spatialProfile n y = 1
  /-- Spatial cutoffs are real-valued and nonnegative. -/
  spatial_real_nonnegative : ∀ n y,
    Complex.im (spatialProfile n y) = 0 ∧ 0 ≤ Complex.re (spatialProfile n y)
  /-- Spatial cutoffs have magnitude at most one. -/
  spatial_norm_le_one : ∀ n y, ‖spatialProfile n y‖ ≤ 1
  /-- Spatial support remains controlled by twice the plateau radius. -/
  spatial_support : ∀ n,
    Function.support (spatialProfile n) ⊆ {y | ‖y‖ ≤ 2 * spatialRadius n}
  /-- The spacetime test is exactly the temporal-spatial product, not an unrelated sequence. -/
  cutoff_apply : ∀ n x,
    cutoff n x = temporalProfile n (x d.timeIndex) *
      spatialProfile n (minkowskiSpatialCoordinates d x)

/-- Physical translation generators connected simultaneously to the same unitary translations,
joint PVM, stress tensor charge limit, and local-observable Ward identity. -/
structure LocalStressEnergyTranslationWardData
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
    (spectrum : ForwardConeJointTranslationSpectrumData U) where
  /-- Controlled time-slice/spatial-volume approximation. -/
  chargeCutoff : StressTensorChargeCutoffData d
  /-- Contravariant momentum-coordinate generators preserve the exact common domain. -/
  momentumGenerator : d.CoordinateIndex → D.domain →ₗ[ℂ] D.domain
  /-- Generator quadratic forms are Hermitian on the common domain. -/
  momentumGenerator_symmetric : ∀ (μ : d.CoordinateIndex) (ψ φ : D.domain),
    @inner ℂ H _ ψ.val (momentumGenerator μ φ).val =
      @inner ℂ H _ (momentumGenerator μ ψ).val φ.val
  /-- Every common-domain vector has an integrable first momentum coordinate. -/
  spectral_coordinate_integrable : ∀ (μ : d.CoordinateIndex) (ψ : D.domain),
    Integrable (fun p : Spacetime d => p μ) (spectrum.joint.diagonalMeasure ψ.val)
  /-- Generator diagonal forms are the first moments of the same joint PVM. -/
  generator_spectral_diagonal : ∀ (μ : d.CoordinateIndex) (ψ : D.domain),
    ∫ p, p μ ∂ spectrum.joint.diagonalMeasure ψ.val =
      Complex.re (@inner ℂ H _ ψ.val (momentumGenerator μ ψ).val)
  /-- Differentiating the same physical translation unitary gives the signed momentum generator
  dictated by `exp(i p·a)` and the mostly-minus pairing. -/
  translation_derivative : ∀ (μ : d.CoordinateIndex) (ψ : D.domain),
    HasDerivAt
      (fun t : ℝ =>
        ((D.domainUnitary (lift.translation (t • d.basisVector μ))) ψ).val)
      ((Complex.I * (d.minkowskiWeight μ : ℂ)) • (momentumGenerator μ ψ).val) 0
  /-- Controlled stress charges converge strongly on the common domain to those same generators. -/
  stress_charge_tendsto : ∀ (ν : d.CoordinateIndex) (ψ : D.domain),
    Filter.Tendsto
      (fun n =>
        (family.operator
          (stress.componentLabel (stressTensorTimeIndex d) ν)
          (chargeCutoff.cutoff n) ψ).val)
      Filter.atTop (nhds (momentumGenerator ν ψ).val)
  /-- Infinitesimal covariance is imposed as the local-observable translation Ward identity on the
  same family and domain. -/
  observable_translation_ward : ∀ (μ : d.CoordinateIndex) (A : family.Label)
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain),
    (Complex.I * (d.minkowskiWeight μ : ℂ)) •
        (momentumGenerator μ (family.operator A f ψ) -
          family.operator A f (momentumGenerator μ ψ)) =
      -family.operator A (minkowskiSchwartzCoordinateDerivative μ f) ψ
  /-- Physical time translations are not represented by the zero generator. -/
  timeGenerator_nontrivial :
    ∃ ψ : D.domain, momentumGenerator (stressTensorTimeIndex d) ψ ≠ 0

end YangMills.Minkowski
