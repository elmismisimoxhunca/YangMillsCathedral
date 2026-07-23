/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.NormalizedCompactHaarConvolution
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatConvolutionSemigroup
import YangMills.Mathematics.UnitaryMatrixDualCasimirHeatInitialIdentity

/-!
# Positive real-density semigroup for the candidate Casimir spectral family

The complex character-series semigroup has already been proved conditionally from heat-trace
summability. This file transports that law to the real and `ENNReal` densities under the explicit
positivity datum. It proves

`q_{s+t}(z) = ∫ q_s(x) q_t(x⁻¹z) dμ_H(x)`

and the exact corresponding `ENNReal` density convolution used by the two-dimensional acceptance
checker.

Independently, unitarity gives `χ_q(g⁻¹)=conj(χ_q(g))`; real spectral coefficients and unconditional
summation therefore give inversion symmetry of the complex series up to conjugation and literal
inversion symmetry of its real/`ENNReal` densities.

No positivity datum or heat kernel is constructed.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Inversion of a selected unitary character is complex conjugation. -/
@[simp]
theorem unitaryMatrixDualCharacter_inv_eq_star
    (q : UnitaryMatrixDual G) (g : G) :
    unitaryMatrixDualCharacter q g⁻¹ = star (unitaryMatrixDualCharacter q g) := by
  unfold unitaryMatrixDualCharacter
  rw [unitaryMatrixRepresentation_inv_eq_conjTranspose
    (unitaryMatrixDualRepresentation q)
    (unitaryMatrixDualRepresentative q).unitary_representation]
  exact Matrix.trace_conjTranspose _

variable [CompactSpace G]

/-- The complex candidate spectral series transforms under inversion by complex conjugation. -/
theorem unitaryMatrixDualCasimirHeatCharacterSeries_inv
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) (g : G) :
    unitaryMatrixDualCasimirHeatCharacterSeries data t g⁻¹ =
      star (unitaryMatrixDualCasimirHeatCharacterSeries data t g) := by
  let a := unitaryMatrixDualCasimirHeatCoefficient data t
  have ha := summable_norm_unitaryMatrixDualCasimirHeatCoefficient_mul_dimension data ht
  have hs := hasSum_unitaryMatrixDualUniformCharacterSeries a ha
  have he : HasSum (fun q => a q * unitaryMatrixDualCharacter q g)
      (unitaryMatrixDualCasimirHeatCharacterSeries data t g) := by
    have hm := (compactContinuousMapEvaluation g).hasSum hs
    simpa [unitaryMatrixDualCasimirHeatCharacterSeries, a,
      unitaryMatrixDualContinuousCharacter] using hm
  rw [unitaryMatrixDualCasimirHeatCharacterSeries_apply data ht]
  apply HasSum.tsum_eq
  have hstar := he.star
  convert hstar using 1
  funext q
  rw [unitaryMatrixDualCharacter_inv_eq_star]
  have hareal : star (a q) = a q := by
    unfold a unitaryMatrixDualCasimirHeatCoefficient
    simp
  change a q * star (unitaryMatrixDualCharacter q g) = _
  rw [star_mul, hareal]
  ring

/-- The real-part density is inversion invariant. This conclusion does not require positivity. -/
theorem unitaryMatrixDualCasimirHeatDensityReal_inv
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) (g : G) :
    unitaryMatrixDualCasimirHeatDensityReal data t g⁻¹ =
      unitaryMatrixDualCasimirHeatDensityReal data t g := by
  have h := congrArg Complex.re
    (unitaryMatrixDualCasimirHeatCharacterSeries_inv data ht g)
  simpa [unitaryMatrixDualCasimirHeatDensityReal] using h

/-- The associated `ENNReal` density is inversion invariant. -/
theorem unitaryMatrixDualCasimirHeatDensityENNReal_inv
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    {t : ℝ} (ht : 0 < t) (g : G) :
    unitaryMatrixDualCasimirHeatDensityENNReal data t g⁻¹ =
      unitaryMatrixDualCasimirHeatDensityENNReal data t g := by
  unfold unitaryMatrixDualCasimirHeatDensityENNReal
  rw [unitaryMatrixDualCasimirHeatDensityReal_inv data ht]

variable [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Under explicit positivity, the real densities satisfy the exact normalized-Haar convolution
addition law. -/
theorem normalizedCompactHaar_integral_casimirHeatDensityReal_mul
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData data)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (z : G) :
    unitaryMatrixDualCasimirHeatDensityReal data (s + t) z =
      ∫ x, unitaryMatrixDualCasimirHeatDensityReal data s x *
        unitaryMatrixDualCasimirHeatDensityReal data t (x⁻¹ * z)
        ∂normalizedCompactHaarMeasure G := by
  have h := normalizedCompactHaarComplexConvolution_casimirHeatCharacterSeries
    data hs ht z
  rw [normalizedCompactHaarComplexConvolution_apply] at h
  rw [unitaryMatrixDualCasimirHeatCharacterSeries_eq_densityReal
    data positivity (add_pos hs ht) z] at h
  simp_rw [unitaryMatrixDualCasimirHeatCharacterSeries_eq_densityReal data positivity hs,
    unitaryMatrixDualCasimirHeatCharacterSeries_eq_densityReal data positivity ht] at h
  have hpoint (x : G) :
      (unitaryMatrixDualCasimirHeatDensityReal data s x : ℂ) *
          (unitaryMatrixDualCasimirHeatDensityReal data t (x⁻¹ * z) : ℂ) =
        ((unitaryMatrixDualCasimirHeatDensityReal data s x *
          unitaryMatrixDualCasimirHeatDensityReal data t (x⁻¹ * z) : ℝ) : ℂ) := by
    push_cast
    rfl
  simp_rw [hpoint] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h.symm

/-- Under positivity, the `ENNReal` densities satisfy the exact source-facing convolution law. -/
theorem unitaryMatrixDualCasimirHeatDensityENNReal_add
    (data : UnitaryMatrixDualHeatTraceSummabilityData (G := G))
    (positivity : UnitaryMatrixDualCasimirHeatPositivityData data)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (z : G) :
    unitaryMatrixDualCasimirHeatDensityENNReal data (s + t) z =
      normalizedCompactHaarDensityConvolution G
        (unitaryMatrixDualCasimirHeatDensityENNReal data s)
        (unitaryMatrixDualCasimirHeatDensityENNReal data t) z := by
  rw [unitaryMatrixDualCasimirHeatDensityENNReal,
    normalizedCompactHaarDensityConvolution_apply,
    normalizedCompactHaar_integral_casimirHeatDensityReal_mul data positivity hs ht z]
  rw [ofReal_integral_eq_lintegral_ofReal]
  · apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_mul
      (unitaryMatrixDualCasimirHeatDensityReal_pos data positivity hs x).le]
    rfl
  · let μ := normalizedCompactHaarMeasure G
    letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
    have hcs := continuous_unitaryMatrixDualCasimirHeatDensityReal data s
    have hct := continuous_unitaryMatrixDualCasimirHeatDensityReal data t
    have hc : Continuous (fun x =>
        unitaryMatrixDualCasimirHeatDensityReal data s x *
          unitaryMatrixDualCasimirHeatDensityReal data t (x⁻¹ * z)) := by
      fun_prop
    simpa only [integrableOn_univ] using
      hc.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
  · filter_upwards [] with x
    exact mul_nonneg
      (unitaryMatrixDualCasimirHeatDensityReal_pos data positivity hs x).le
      (unitaryMatrixDualCasimirHeatDensityReal_pos data positivity ht (x⁻¹ * z)).le

end

end Mathematics
end YangMills
