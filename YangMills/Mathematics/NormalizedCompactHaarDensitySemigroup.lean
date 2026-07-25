/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.Basic
import YangMills.Mathematics.NormalizedCompactHaarConvolution

/-!
# Normalized compact-Haar density semigroups

A reusable source-neutral interface for positive-time central convolution densities on a compact
group, together with weak convergence to the identity. This packages the exact analytic object shared
by compact-group heat kernels without asserting that any supplied family is geometrically generated
by a Laplacian.
-/

namespace YangMills.Mathematics

open MeasureTheory Filter
open scoped ENNReal BoundedContinuousFunction

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Source-neutral positive-time normalized central convolution density semigroup. -/
structure NormalizedCompactHaarDensitySemigroupData (density : ℝ → G → ℝ≥0∞) where
  density_measurable : ∀ t, 0 < t → Measurable (density t)
  density_central : ∀ t, 0 < t → ∀ h g, density t (h * g * h⁻¹) = density t g
  density_inv : ∀ t, 0 < t → ∀ g, density t g⁻¹ = density t g
  density_lintegral_normalized : ∀ t, 0 < t →
    ∫⁻ g, density t g ∂normalizedCompactHaarMeasure G = 1
  density_add : ∀ s t, 0 < s → 0 < t → ∀ g,
    density (s + t) g = normalizedCompactHaarDensityConvolution G (density s) (density t) g
  weak_tendsto_identity : ∀ f : C(G, ℂ),
    Tendsto
      (fun t : ℝ => ∫ g, f g
        ∂((normalizedCompactHaarMeasure G).withDensity (density t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 1))

/-- Probability measure represented by one member of a normalized Haar-density semigroup. -/
noncomputable def normalizedCompactHaarDensitySemigroupMeasure
    (density : ℝ → G → ℝ≥0∞) (t : ℝ) : Measure G :=
  (normalizedCompactHaarMeasure G).withDensity (density t)

namespace NormalizedCompactHaarDensitySemigroupData

/-- Every positive-time member has total mass one. -/
theorem measure_univ
    {density : ℝ → G → ℝ≥0∞}
    (data : NormalizedCompactHaarDensitySemigroupData density)
    {t : ℝ} (ht : 0 < t) :
    normalizedCompactHaarDensitySemigroupMeasure density t Set.univ = 1 := by
  rw [normalizedCompactHaarDensitySemigroupMeasure,
    withDensity_apply _ MeasurableSet.univ]
  simpa only [Measure.restrict_univ] using data.density_lintegral_normalized t ht

/-- Hence no positive-time member is the zero measure. -/
theorem measure_ne_zero
    {density : ℝ → G → ℝ≥0∞}
    (data : NormalizedCompactHaarDensitySemigroupData density)
    {t : ℝ} (ht : 0 < t) :
    normalizedCompactHaarDensitySemigroupMeasure density t ≠ 0 := by
  intro zeroMeasure
  have normalized := data.measure_univ ht
  rw [zeroMeasure] at normalized
  simp at normalized

end NormalizedCompactHaarDensitySemigroupData

section Hom

variable {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [MeasurableSpace H] [BorelSpace H]

/-- A measurable surjective homomorphism intertwining two exact normalized Haar-density semigroups
at every positive time. This is phrased at measure level because covering heat kernels need not agree
pointwise across fibers. -/
structure NormalizedCompactHaarDensitySemigroupHomData
    {sourceDensity : ℝ → G → ℝ≥0∞} {targetDensity : ℝ → H → ℝ≥0∞}
    (sourceSemigroup : NormalizedCompactHaarDensitySemigroupData sourceDensity)
    (targetSemigroup : NormalizedCompactHaarDensitySemigroupData targetDensity)
    (projection : G →* H) where
  projection_measurable : Measurable projection
  projection_surjective : Function.Surjective projection
  map_measure : ∀ t, 0 < t →
    Measure.map projection (normalizedCompactHaarDensitySemigroupMeasure sourceDensity t) =
      normalizedCompactHaarDensitySemigroupMeasure targetDensity t

namespace NormalizedCompactHaarDensitySemigroupHomData

/-- Construct exact measure transport from equality against every bounded continuous real test.
Finite positive-time mass is derived from the two normalized semigroup records. -/
noncomputable def of_integral_comp_projection
    [HasOuterApproxClosed H]
    {sourceDensity : ℝ → G → ℝ≥0∞} {targetDensity : ℝ → H → ℝ≥0∞}
    {sourceSemigroup : NormalizedCompactHaarDensitySemigroupData sourceDensity}
    {targetSemigroup : NormalizedCompactHaarDensitySemigroupData targetDensity}
    {projection : G →* H}
    (projection_measurable : Measurable projection)
    (projection_surjective : Function.Surjective projection)
    (integral_comp_projection : ∀ t : ℝ, 0 < t → ∀ f : H →ᵇ ℝ,
      (∫ g, f (projection g)
        ∂normalizedCompactHaarDensitySemigroupMeasure sourceDensity t) =
      ∫ h, f h ∂normalizedCompactHaarDensitySemigroupMeasure targetDensity t) :
    NormalizedCompactHaarDensitySemigroupHomData
      sourceSemigroup targetSemigroup projection where
  projection_measurable := projection_measurable
  projection_surjective := projection_surjective
  map_measure := by
    intro t ht
    let μs := normalizedCompactHaarDensitySemigroupMeasure sourceDensity t
    let μt := normalizedCompactHaarDensitySemigroupMeasure targetDensity t
    letI : IsFiniteMeasure μs :=
      ⟨by rw [sourceSemigroup.measure_univ ht]; exact ENNReal.one_lt_top⟩
    letI : IsFiniteMeasure μt :=
      ⟨by rw [targetSemigroup.measure_univ ht]; exact ENNReal.one_lt_top⟩
    letI : IsFiniteMeasure (Measure.map projection μs) := by infer_instance
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    rw [integral_map projection_measurable.aemeasurable
      f.continuous.aestronglyMeasurable]
    exact integral_comp_projection t ht f

/-- Continuous-test form of exact positive-time semigroup transport. -/
theorem integral_comp_projection
    {sourceDensity : ℝ → G → ℝ≥0∞} {targetDensity : ℝ → H → ℝ≥0∞}
    {sourceSemigroup : NormalizedCompactHaarDensitySemigroupData sourceDensity}
    {targetSemigroup : NormalizedCompactHaarDensitySemigroupData targetDensity}
    {projection : G →* H}
    (hom : NormalizedCompactHaarDensitySemigroupHomData
      sourceSemigroup targetSemigroup projection)
    {t : ℝ} (ht : 0 < t) (test : C(H, ℂ)) :
    (∫ g, test (projection g)
        ∂normalizedCompactHaarDensitySemigroupMeasure sourceDensity t) =
      ∫ h, test h ∂normalizedCompactHaarDensitySemigroupMeasure targetDensity t := by
  rw [← hom.map_measure t ht]
  exact (integral_map hom.projection_measurable.aemeasurable
    test.continuous.aestronglyMeasurable).symm

end NormalizedCompactHaarDensitySemigroupHomData

end Hom

end

end YangMills.Mathematics
