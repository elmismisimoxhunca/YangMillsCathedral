/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.StressEnergyTranslationWard

/-!
# Hostile probes for the stress-energy translation Ward bridge

These probes expose the controlled charge cutoffs and every connection from stress components to
the exact translation generators, unitary representation, joint PVM, and local-observable Ward
identity. No bridge datum is constructed.
-/

namespace YangMills.Minkowski.StressEnergyTranslationWard.Probes

open MeasureTheory

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
    {stress : LocalStressEnergyTensorData family}
    {spectrum : ForwardConeJointTranslationSpectrumData U}

/-- Cutoffs are exactly products of the designated temporal and spatial profiles. -/
theorem exact_charge_cutoff_product
    (ward : LocalStressEnergyTranslationWardData stress spectrum)
    (n : ℕ) (x : Spacetime d) :
    ward.chargeCutoff.cutoff n x =
      ward.chargeCutoff.temporalProfile n (x d.timeIndex) *
        ward.chargeCutoff.spatialProfile n (minkowskiSpatialCoordinates d x) :=
  ward.chargeCutoff.cutoff_apply n x

/-- Temporal profiles cannot be zero because their exact integral is one. -/
theorem zero_temporal_profile_blocked
    (ward : LocalStressEnergyTranslationWardData stress spectrum) (n : ℕ) :
    ward.chargeCutoff.temporalProfile n ≠ 0 := by
  intro hzero
  have hone := ward.chargeCutoff.temporal_integral_one n
  rw [hzero] at hone
  simp at hone

/-- Spatial profiles cannot be zero because each equals one at the origin of its plateau. -/
theorem zero_spatial_profile_blocked
    (ward : LocalStressEnergyTranslationWardData stress spectrum) (n : ℕ) :
    ward.chargeCutoff.spatialProfile n ≠ 0 := by
  intro hzero
  have hzero_le : ‖(0 : Fin d.spatialDimension → ℝ)‖ ≤
      ward.chargeCutoff.spatialRadius n := by
    simpa using le_of_lt (ward.chargeCutoff.spatialRadius_pos n)
  have hplateau := ward.chargeCutoff.spatial_plateau n
    (0 : Fin d.spatialDimension → ℝ) hzero_le
  rw [hzero] at hplateau
  simp at hplateau

/-- The exact product and unit spatial plateau prevent the spacetime cutoff from being zero. -/
theorem zero_charge_cutoff_blocked
    (ward : LocalStressEnergyTranslationWardData stress spectrum) (n : ℕ) :
    ward.chargeCutoff.cutoff n ≠ 0 := by
  intro hcutoff
  apply zero_temporal_profile_blocked ward n
  ext t
  let x : Spacetime d := fun j => if j = d.timeIndex then t else 0
  have hxTime : x d.timeIndex = t := by simp [x]
  have hxSpatial : minkowskiSpatialCoordinates d x = 0 := by
    funext i
    simp [x, minkowskiSpatialCoordinates, EuclideanDimension.spatialIndexSucc,
      EuclideanDimension.timeIndex]
  have hzero_le : ‖(0 : Fin d.spatialDimension → ℝ)‖ ≤
      ward.chargeCutoff.spatialRadius n := by
    simpa using le_of_lt (ward.chargeCutoff.spatialRadius_pos n)
  have hspatial := ward.chargeCutoff.spatial_plateau n
    (0 : Fin d.spatialDimension → ℝ) hzero_le
  have hvalue := congrArg (fun q : ScalarMinkowskiSchwartzTestFunction d => q x) hcutoff
  rw [ward.chargeCutoff.cutoff_apply, hxTime, hxSpatial, hspatial] at hvalue
  simpa using hvalue

/-- Temporal localization genuinely shrinks while spatial plateaux genuinely expand. -/
theorem exact_cutoff_scale_limits
    (ward : LocalStressEnergyTranslationWardData stress spectrum) :
    Filter.Tendsto ward.chargeCutoff.temporalWidth Filter.atTop (nhds 0) ∧
      Filter.Tendsto ward.chargeCutoff.spatialRadius Filter.atTop Filter.atTop :=
  ⟨ward.chargeCutoff.temporalWidth_tendsto_zero,
    ward.chargeCutoff.spatialRadius_tendsto_atTop⟩

/-- Temporal profiles converge to the actual time-zero delta distribution, while spatial cutoffs
are controlled real nonnegative functions of magnitude at most one. -/
theorem exact_regulator_control
    (ward : LocalStressEnergyTranslationWardData stress spectrum)
    (f : SchwartzMap ℝ ℂ) (n : ℕ) (y : Fin d.spatialDimension → ℝ) :
    Filter.Tendsto
        (fun k => ∫ t, ward.chargeCutoff.temporalProfile k t * f t)
        Filter.atTop (nhds (f 0)) ∧
      (Complex.im (ward.chargeCutoff.spatialProfile n y) = 0 ∧
        0 ≤ Complex.re (ward.chargeCutoff.spatialProfile n y)) ∧
      ‖ward.chargeCutoff.spatialProfile n y‖ ≤ 1 :=
  ⟨ward.chargeCutoff.temporal_tendsto_delta f,
    ward.chargeCutoff.spatial_real_nonnegative n y,
    ward.chargeCutoff.spatial_norm_le_one n y⟩

/-- The momentum generators preserve the exact common domain and have Hermitian quadratic forms. -/
theorem exact_generator_domain_symmetry
    (ward : LocalStressEnergyTranslationWardData stress spectrum)
    (μ : d.CoordinateIndex) (ψ φ : D.domain) :
    (ward.momentumGenerator μ ψ).val ∈ D.domain ∧
      @inner ℂ H _ ψ.val (ward.momentumGenerator μ φ).val =
        @inner ℂ H _ (ward.momentumGenerator μ ψ).val φ.val :=
  ⟨(ward.momentumGenerator μ ψ).property,
    ward.momentumGenerator_symmetric μ ψ φ⟩

/-- The generators have integrable first moments against the exact same joint PVM. -/
theorem exact_generator_spectral_diagonal
    (ward : LocalStressEnergyTranslationWardData stress spectrum)
    (μ : d.CoordinateIndex) (ψ : D.domain) :
    Integrable (fun p : Spacetime d => p μ) (spectrum.joint.diagonalMeasure ψ.val) ∧
      (∫ p, p μ ∂ spectrum.joint.diagonalMeasure ψ.val) =
        Complex.re (@inner ℂ H _ ψ.val (ward.momentumGenerator μ ψ).val) :=
  ⟨ward.spectral_coordinate_integrable μ ψ,
    ward.generator_spectral_diagonal μ ψ⟩

/-- The same generator is the derivative of the same physical translation unitary. -/
theorem exact_translation_derivative
    (ward : LocalStressEnergyTranslationWardData stress spectrum)
    (μ : d.CoordinateIndex) (ψ : D.domain) :
    HasDerivAt
      (fun t : ℝ =>
        ((D.domainUnitary (lift.translation (t • d.basisVector μ))) ψ).val)
      ((Complex.I * (d.minkowskiWeight μ : ℂ)) •
        (ward.momentumGenerator μ ψ).val) 0 :=
  ward.translation_derivative μ ψ

/-- The time derivative carries `+i`, independently exposing the mostly-minus sign choice. -/
theorem exact_time_translation_derivative_sign
    (ward : LocalStressEnergyTranslationWardData stress spectrum) (ψ : D.domain) :
    HasDerivAt
      (fun t : ℝ =>
        ((D.domainUnitary
          (lift.translation (t • d.basisVector (stressTensorTimeIndex d)))) ψ).val)
      (Complex.I • (ward.momentumGenerator (stressTensorTimeIndex d) ψ).val) 0 := by
  simpa [EuclideanDimension.minkowskiWeight, stressTensorTimeIndex,
    EuclideanDimension.timeIndex] using
    ward.translation_derivative (stressTensorTimeIndex d) ψ

/-- Every spatial derivative carries `-i`, independently exposing the mostly-minus sign choice. -/
theorem exact_spatial_translation_derivative_sign
    (ward : LocalStressEnergyTranslationWardData stress spectrum)
    (i : Fin d.spatialDimension) (ψ : D.domain) :
    HasDerivAt
      (fun t : ℝ =>
        ((D.domainUnitary
          (lift.translation (t • d.basisVector (d.spatialIndexSucc i)))) ψ).val)
      ((-Complex.I) • (ward.momentumGenerator (d.spatialIndexSucc i) ψ).val) 0 := by
  simpa [EuclideanDimension.minkowskiWeight, EuclideanDimension.spatialIndexSucc] using
    ward.translation_derivative (d.spatialIndexSucc i) ψ

/-- Controlled spatial stress charges converge to those exact physical generators. -/
theorem exact_stress_charge_limit
    (ward : LocalStressEnergyTranslationWardData stress spectrum)
    (ν : d.CoordinateIndex) (ψ : D.domain) :
    Filter.Tendsto
      (fun n =>
        (family.operator
          (stress.componentLabel (stressTensorTimeIndex d) ν)
          (ward.chargeCutoff.cutoff n) ψ).val)
      Filter.atTop (nhds (ward.momentumGenerator ν ψ).val) :=
  ward.stress_charge_tendsto ν ψ

/-- The same stress-generated momentum acts on every same-family observable by the translation Ward
identity. -/
theorem exact_observable_translation_ward
    (ward : LocalStressEnergyTranslationWardData stress spectrum)
    (μ : d.CoordinateIndex) (A : family.Label)
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    (Complex.I * (d.minkowskiWeight μ : ℂ)) •
        (ward.momentumGenerator μ (family.operator A f ψ) -
          family.operator A f (ward.momentumGenerator μ ψ)) =
      -family.operator A (minkowskiSchwartzCoordinateDerivative μ f) ψ :=
  ward.observable_translation_ward μ A f ψ

/-- A zero physical time-translation generator cannot satisfy the bridge. -/
theorem zero_time_generator_blocked
    (ward : LocalStressEnergyTranslationWardData stress spectrum) :
    ∃ ψ : D.domain,
      ward.momentumGenerator (stressTensorTimeIndex d) ψ ≠ 0 :=
  ward.timeGenerator_nontrivial

end YangMills.Minkowski.StressEnergyTranslationWard.Probes
