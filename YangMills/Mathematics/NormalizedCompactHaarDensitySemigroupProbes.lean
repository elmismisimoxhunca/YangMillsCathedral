/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.NormalizedCompactHaarDensitySemigroup

/-! Hostile probes for normalized compact-Haar density semigroups. -/

namespace YangMills.Mathematics.NormalizedCompactHaarDensitySemigroup.Probes

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {density : ℝ → G → ℝ≥0∞}
  (data : NormalizedCompactHaarDensitySemigroupData density)

include data in
/-- Exact positive-time normalization and nonzeroness. -/
theorem exact_positive_time_probability {t : ℝ} (ht : 0 < t) :
    normalizedCompactHaarDensitySemigroupMeasure density t Set.univ = 1 ∧
      normalizedCompactHaarDensitySemigroupMeasure density t ≠ 0 :=
  ⟨NormalizedCompactHaarDensitySemigroupData.measure_univ data ht,
    NormalizedCompactHaarDensitySemigroupData.measure_ne_zero data ht⟩

include data in
/-- Hostile zero-measure probe. -/
theorem zero_positive_time_measure_blocked
    {t : ℝ} (ht : 0 < t)
    (zeroMeasure : normalizedCompactHaarDensitySemigroupMeasure density t = 0) : False :=
  NormalizedCompactHaarDensitySemigroupData.measure_ne_zero data ht zeroMeasure

include data in
/-- Hostile convolution-order probe: changing the source-facing output is rejected. -/
theorem changed_density_add_blocked
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (g : G)
    (changed : density (s + t) g ≠
      normalizedCompactHaarDensityConvolution G (density s) (density t) g) : False :=
  changed (NormalizedCompactHaarDensitySemigroupData.density_add data s t hs ht g)

section Hom

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [MeasurableSpace H] [BorelSpace H]
  {targetDensity : ℝ → H → ℝ≥0∞}
  {sourceData : NormalizedCompactHaarDensitySemigroupData density}
  {targetData : NormalizedCompactHaarDensitySemigroupData targetDensity}
  {projection : G →* H}
  (hom : NormalizedCompactHaarDensitySemigroupHomData sourceData targetData projection)

include hom in
/-- Exact continuous-test transport through a semigroup homomorphism. -/
theorem exact_integral_transport {t : ℝ} (ht : 0 < t) (test : C(H, ℂ)) :
    (∫ g, test (projection g)
        ∂normalizedCompactHaarDensitySemigroupMeasure density t) =
      ∫ h, test h ∂normalizedCompactHaarDensitySemigroupMeasure targetDensity t :=
  hom.integral_comp_projection ht test

include hom in
/-- Hostile transport probe: a changed projected positive-time law is rejected. -/
theorem changed_projected_measure_blocked
    {t : ℝ} (ht : 0 < t)
    (changed : Measure.map projection
        (normalizedCompactHaarDensitySemigroupMeasure density t) ≠
      normalizedCompactHaarDensitySemigroupMeasure targetDensity t) : False :=
  changed (hom.map_measure t ht)

end Hom

end

end YangMills.Mathematics.NormalizedCompactHaarDensitySemigroup.Probes
