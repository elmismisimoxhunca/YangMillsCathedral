/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.SmoothUnitaryMatrixCoefficientSelectedRealification

namespace YangMills
namespace Mathematics
namespace SmoothUnitaryMatrixCoefficientSelectedRealification
namespace Probes

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact selected-block probe: a retained smooth representative realifies the unchanged selected
coefficient synthesis inside the smooth real core. -/
theorem exact_selectedCoefficientSingle_realification
    (q : UnitaryMatrixDual G) (hq : q.HasSmoothRepresentative (E := E))
    (A : Matrix (Fin (unitaryMatrixDualDimension q))
      (Fin (unitaryMatrixDualDimension q)) ℂ) :
    ∃ f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G),
      ∀ g : G, f g =
        (unitaryMatrixDualCoefficientSynthesis G
          (unitaryMatrixDualCoefficientSingle q A) g).re :=
  unitaryMatrixDualCoefficientSingle_realPart_mem_smoothRealCore q hq A

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact continuous-image form of selected-block realification. -/
theorem exact_selectedCoefficientSingle_continuous_realification
    (q : UnitaryMatrixDual G) (hq : q.HasSmoothRepresentative (E := E))
    (A : Matrix (Fin (unitaryMatrixDualDimension q))
      (Fin (unitaryMatrixDualDimension q)) ℂ) :
    ∃ f ∈ smoothLieGroupScalarToContinuousLinearMap ''
        smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G),
      ∀ g : G, f g =
        (unitaryMatrixDualCoefficientSynthesis G
          (unitaryMatrixDualCoefficientSingle q A) g).re :=
  unitaryMatrixDualCoefficientSingle_realPart_mem_continuousSmoothRealCoreImage q hq A

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Hostile selected-block probe: changing one exact realified point value is contradictory. -/
theorem changed_selectedCoefficientSingle_realification_blocked
    (q : UnitaryMatrixDual G) (hq : q.HasSmoothRepresentative (E := E))
    (A : Matrix (Fin (unitaryMatrixDualDimension q))
      (Fin (unitaryMatrixDualDimension q)) ℂ)
    (g : G) (changed : ℝ)
    (changed_ne_exact : changed ≠
      (unitaryMatrixDualCoefficientSynthesis G
        (unitaryMatrixDualCoefficientSingle q A) g).re)
    (claimed : ∀ f : SmoothLieGroupScalarFunction (E := E) (G := G),
      f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) →
      (∀ x : G, f x =
        (unitaryMatrixDualCoefficientSynthesis G
          (unitaryMatrixDualCoefficientSingle q A) x).re) →
      f g = changed) : False := by
  obtain ⟨f, hf, hpointwise⟩ :=
    unitaryMatrixDualCoefficientSingle_realPart_mem_smoothRealCore q hq A
  exact changed_ne_exact ((claimed f hf hpointwise).symm.trans (hpointwise g))

end

end Probes
end SmoothUnitaryMatrixCoefficientSelectedRealification
end Mathematics
end YangMills
