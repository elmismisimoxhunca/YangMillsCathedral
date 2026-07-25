/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.NormalizedCompactHaarDensitySemigroup
import YangMills.Mathematics.UnitaryMatrixDualContinuousDensity

/-!
# Fourier determination of compact density-semigroup transport

For finite measures on compact Hausdorff spaces, integration of continuous complex functions is a
bounded linear functional in the uniform norm. Consequently, selected Peter--Weyl density promotes
an integral identity on every finitely supported selected matrix-coefficient synthesis to every
continuous test. Taking real parts then supplies the bounded-continuous real-test identity used by
finite regular-measure extensionality.

This file therefore reduces a normalized density-semigroup homomorphism to three explicit inputs:
a continuous surjective group homomorphism, selected continuous Peter--Weyl density on the target,
and exact integral compatibility on every finite selected coefficient synthesis. It does not prove
Peter--Weyl density or any coefficient compatibility.
-/

namespace YangMills.Mathematics

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

noncomputable section

universe uX uG uH

/-- Integration of continuous complex functions against a finite measure on a compact Hausdorff
space, as a bounded complex-linear functional in the uniform norm. -/
noncomputable def compactContinuousMapIntegralCLM
    {X : Type uX} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] : C(X, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := by
        intro f g
        apply integral_add
        · simpa only [integrableOn_univ] using
            f.continuous.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
        · simpa only [integrableOn_univ] using
            g.continuous.continuousOn.integrableOn_compact (μ := μ) isCompact_univ
      map_smul' := by intro c f; exact integral_smul c f }
    (μ.real Set.univ)
    (fun f => by
      simpa [mul_comm] using norm_integral_le_of_norm_le_const (μ := μ)
        (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x))

/-- Pullback integration along a continuous map, again as a bounded complex-linear functional on
continuous target tests. -/
noncomputable def compactContinuousMapPullbackIntegralCLM
    {X : Type uX} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    {Y : Type uH} [TopologicalSpace Y] [CompactSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] (p : X → Y) (hp : Continuous p) :
    C(Y, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f (p x) ∂μ
      map_add' := by
        intro f g
        apply integral_add
        · change Integrable (f ∘ p) μ
          simpa only [integrableOn_univ] using
            (f.continuous.comp hp).continuousOn.integrableOn_compact (μ := μ) isCompact_univ
        · change Integrable (g ∘ p) μ
          simpa only [integrableOn_univ] using
            (g.continuous.comp hp).continuousOn.integrableOn_compact (μ := μ) isCompact_univ
      map_smul' := by intro c f; exact integral_smul c (fun x => f (p x)) }
    (μ.real Set.univ)
    (fun f => by
      simpa [mul_comm] using norm_integral_le_of_norm_le_const (μ := μ)
        (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm (p x)))

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
  {sourceDensity : ℝ → G → ℝ≥0∞} {targetDensity : ℝ → H → ℝ≥0∞}
  {sourceSemigroup : NormalizedCompactHaarDensitySemigroupData sourceDensity}
  {targetSemigroup : NormalizedCompactHaarDensitySemigroupData targetDensity}
  {projection : G →* H}

include sourceSemigroup targetSemigroup in
/-- Selected Peter--Weyl density promotes finite coefficient-synthesis compatibility to every
continuous complex test. -/
theorem integral_comp_projection_eq_of_continuousPeterWeyl
    (projection_continuous : Continuous projection)
    (density : UnitaryMatrixDual.HasContinuousPeterWeylDensity H)
    (coefficientIntegral : ∀ t : ℝ, 0 < t →
      ∀ A : UnitaryMatrixDualCoefficientSpace H,
        (∫ g, unitaryMatrixDualContinuousCoefficientSynthesis H A (projection g)
          ∂normalizedCompactHaarDensitySemigroupMeasure sourceDensity t) =
        ∫ h, unitaryMatrixDualContinuousCoefficientSynthesis H A h
          ∂normalizedCompactHaarDensitySemigroupMeasure targetDensity t) :
    ∀ t : ℝ, 0 < t → ∀ f : C(H, ℂ),
      (∫ g, f (projection g)
        ∂normalizedCompactHaarDensitySemigroupMeasure sourceDensity t) =
      ∫ h, f h ∂normalizedCompactHaarDensitySemigroupMeasure targetDensity t := by
  intro t ht
  let μs := normalizedCompactHaarDensitySemigroupMeasure sourceDensity t
  let μt := normalizedCompactHaarDensitySemigroupMeasure targetDensity t
  letI : IsFiniteMeasure μs :=
    ⟨by rw [sourceSemigroup.measure_univ ht]; exact ENNReal.one_lt_top⟩
  letI : IsFiniteMeasure μt :=
    ⟨by rw [targetSemigroup.measure_univ ht]; exact ENNReal.one_lt_top⟩
  let Ls := compactContinuousMapPullbackIntegralCLM μs projection projection_continuous
  let Lt := compactContinuousMapIntegralCLM μt
  have heq : Ls = Lt := by
    apply ContinuousLinearMap.ext
    intro f
    apply congrFun (Continuous.ext_on density Ls.continuous Lt.continuous ?_) f
    rintro f ⟨A, rfl⟩
    exact coefficientIntegral t ht A
  intro f
  change Ls f = Lt f
  rw [heq]

namespace NormalizedCompactHaarDensitySemigroupHomData

/-- Construct exact positive-time measure transport from selected Peter--Weyl density and integral
compatibility on every finite selected matrix-coefficient synthesis. -/
noncomputable def of_continuousPeterWeylCoefficientIntegrals
    [HasOuterApproxClosed H]
    (projection_continuous : Continuous projection)
    (projection_surjective : Function.Surjective projection)
    (density : UnitaryMatrixDual.HasContinuousPeterWeylDensity H)
    (coefficientIntegral : ∀ t : ℝ, 0 < t →
      ∀ A : UnitaryMatrixDualCoefficientSpace H,
        (∫ g, unitaryMatrixDualContinuousCoefficientSynthesis H A (projection g)
          ∂normalizedCompactHaarDensitySemigroupMeasure sourceDensity t) =
        ∫ h, unitaryMatrixDualContinuousCoefficientSynthesis H A h
          ∂normalizedCompactHaarDensitySemigroupMeasure targetDensity t) :
    NormalizedCompactHaarDensitySemigroupHomData
      sourceSemigroup targetSemigroup projection :=
  of_integral_comp_projection projection_continuous.measurable projection_surjective (by
    intro t ht f
    let fc : C(H, ℂ) :=
      { toFun := fun h => (f h : ℂ)
        continuous_toFun := Complex.continuous_ofReal.comp f.continuous }
    have hc := integral_comp_projection_eq_of_continuousPeterWeyl
      (sourceSemigroup := sourceSemigroup) (targetSemigroup := targetSemigroup)
      projection_continuous density coefficientIntegral t ht fc
    have his : Integrable (fun g => fc (projection g))
        (normalizedCompactHaarDensitySemigroupMeasure sourceDensity t) := by
      letI : IsFiniteMeasure
          (normalizedCompactHaarDensitySemigroupMeasure sourceDensity t) :=
        ⟨by rw [sourceSemigroup.measure_univ ht]; exact ENNReal.one_lt_top⟩
      change Integrable (fc ∘ projection)
        (normalizedCompactHaarDensitySemigroupMeasure sourceDensity t)
      simpa only [integrableOn_univ] using
        (fc.continuous.comp projection_continuous).continuousOn.integrableOn_compact
          (μ := normalizedCompactHaarDensitySemigroupMeasure sourceDensity t) isCompact_univ
    have hit : Integrable fc
        (normalizedCompactHaarDensitySemigroupMeasure targetDensity t) := by
      letI : IsFiniteMeasure
          (normalizedCompactHaarDensitySemigroupMeasure targetDensity t) :=
        ⟨by rw [targetSemigroup.measure_univ ht]; exact ENNReal.one_lt_top⟩
      simpa only [integrableOn_univ] using
        fc.continuous.continuousOn.integrableOn_compact
          (μ := normalizedCompactHaarDensitySemigroupMeasure targetDensity t) isCompact_univ
    calc
      (∫ g, f (projection g)
          ∂normalizedCompactHaarDensitySemigroupMeasure sourceDensity t) =
          Complex.re (∫ g, fc (projection g)
            ∂normalizedCompactHaarDensitySemigroupMeasure sourceDensity t) := by
              exact integral_re his
      _ = Complex.re (∫ h, fc h
            ∂normalizedCompactHaarDensitySemigroupMeasure targetDensity t) :=
          congrArg Complex.re hc
      _ = ∫ h, f h
            ∂normalizedCompactHaarDensitySemigroupMeasure targetDensity t := by
          exact (integral_re hit).symm)

end NormalizedCompactHaarDensitySemigroupHomData

end

end YangMills.Mathematics
