/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualDensitySemigroupHom

/-! Hostile probes for Fourier determination of density-semigroup transport. -/

namespace YangMills.Mathematics.UnitaryMatrixDualDensitySemigroupHom.Probes

open MeasureTheory
open scoped ENNReal

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
  [HasOuterApproxClosed H]
  {sourceDensity : ℝ → G → ℝ≥0∞} {targetDensity : ℝ → H → ℝ≥0∞}
  {sourceSemigroup : NormalizedCompactHaarDensitySemigroupData sourceDensity}
  {targetSemigroup : NormalizedCompactHaarDensitySemigroupData targetDensity}
  {projection : G →* H}
  (projection_continuous : Continuous projection)
  (projection_surjective : Function.Surjective projection)
  (density : UnitaryMatrixDual.HasContinuousPeterWeylDensity H)
  (coefficientIntegral : ∀ t : ℝ, 0 < t →
    ∀ A : UnitaryMatrixDualCoefficientSpace H,
      (∫ g, unitaryMatrixDualContinuousCoefficientSynthesis H A (projection g)
        ∂normalizedCompactHaarDensitySemigroupMeasure sourceDensity t) =
      ∫ h, unitaryMatrixDualContinuousCoefficientSynthesis H A h
        ∂normalizedCompactHaarDensitySemigroupMeasure targetDensity t)

include sourceSemigroup targetSemigroup projection_continuous density coefficientIntegral in
omit [HasOuterApproxClosed H] in
/-- Exact finite-coefficient compatibility extends to every continuous complex test. -/
theorem exact_all_continuous_integral_transport
    {t : ℝ} (ht : 0 < t) (f : C(H, ℂ)) :
    (∫ g, f (projection g)
      ∂normalizedCompactHaarDensitySemigroupMeasure sourceDensity t) =
    ∫ h, f h ∂normalizedCompactHaarDensitySemigroupMeasure targetDensity t :=
  integral_comp_projection_eq_of_continuousPeterWeyl
    (sourceSemigroup := sourceSemigroup) (targetSemigroup := targetSemigroup)
    projection_continuous density coefficientIntegral t ht f

/-- The Fourier-facing inputs construct the exact generic semigroup homomorphism. -/
noncomputable def exact_hom_of_continuousPeterWeyl_coefficients :
    NormalizedCompactHaarDensitySemigroupHomData
      sourceSemigroup targetSemigroup projection :=
  NormalizedCompactHaarDensitySemigroupHomData.of_continuousPeterWeylCoefficientIntegrals
    projection_continuous projection_surjective density coefficientIntegral

include sourceSemigroup targetSemigroup projection_continuous density coefficientIntegral in
omit [HasOuterApproxClosed H] in
/-- Hostile continuous-test probe: a changed expectation is rejected after dense extension. -/
theorem changed_continuous_integral_transport_blocked
    {t : ℝ} (ht : 0 < t) (f : C(H, ℂ))
    (changed : (∫ g, f (projection g)
      ∂normalizedCompactHaarDensitySemigroupMeasure sourceDensity t) ≠
      ∫ h, f h ∂normalizedCompactHaarDensitySemigroupMeasure targetDensity t) : False :=
  changed (integral_comp_projection_eq_of_continuousPeterWeyl
    (sourceSemigroup := sourceSemigroup) (targetSemigroup := targetSemigroup)
    projection_continuous density coefficientIntegral t ht f)

include sourceSemigroup targetSemigroup projection_continuous projection_surjective density
    coefficientIntegral in
/-- Hostile measure probe: changed pushforward is rejected from coefficient tests plus density. -/
theorem changed_measure_transport_blocked
    {t : ℝ} (ht : 0 < t)
    (changed : Measure.map projection
      (normalizedCompactHaarDensitySemigroupMeasure sourceDensity t) ≠
      normalizedCompactHaarDensitySemigroupMeasure targetDensity t) : False :=
  changed ((NormalizedCompactHaarDensitySemigroupHomData.of_continuousPeterWeylCoefficientIntegrals
    (sourceSemigroup := sourceSemigroup) (targetSemigroup := targetSemigroup)
    projection_continuous projection_surjective density coefficientIntegral).map_measure t ht)

include density in
omit [IsTopologicalGroup H] [CompactSpace H] [T2Space H] [MeasurableSpace H]
    [BorelSpace H] [HasOuterApproxClosed H] in
/-- Hostile dependency probe: selected continuous Peter--Weyl density is not synthesized from the
coefficient identities. -/
theorem missing_continuousPeterWeylDensity_blocked
    (missing : ¬ UnitaryMatrixDual.HasContinuousPeterWeylDensity H) : False :=
  missing density

end

end YangMills.Mathematics.UnitaryMatrixDualDensitySemigroupHom.Probes
