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
/-- Exact finite-support probe under explicit all-class smooth coverage. -/
theorem exact_selectedCoefficientSynthesis_realification
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E))
    (A : UnitaryMatrixDualCoefficientSpace G) :
    ∃ f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G),
      ∀ g : G, f g = (unitaryMatrixDualCoefficientSynthesis G A g).re :=
  unitaryMatrixDualCoefficientSynthesis_realPart_mem_smoothRealCore
    smoothCoverage A

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact continuous-image finite-support probe under explicit all-class smooth coverage. -/
theorem exact_selectedCoefficientSynthesis_continuous_realification
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E))
    (A : UnitaryMatrixDualCoefficientSpace G) :
    ∃ f ∈ smoothLieGroupScalarToContinuousLinearMap ''
        smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G),
      ∀ g : G, f g = (unitaryMatrixDualCoefficientSynthesis G A g).re :=
  unitaryMatrixDualCoefficientSynthesis_realPart_mem_continuousSmoothRealCoreImage
    smoothCoverage A

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Hostile finite-support probe: changing one point of every alleged realification contradicts the
constructed realification under all-class smooth coverage. -/
theorem changed_selectedCoefficientSynthesis_realification_blocked
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E))
    (A : UnitaryMatrixDualCoefficientSpace G) (g : G) (changed : ℝ)
    (changed_ne_exact : changed ≠ (unitaryMatrixDualCoefficientSynthesis G A g).re)
    (claimed : ∀ f : SmoothLieGroupScalarFunction (E := E) (G := G),
      f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) →
      (∀ x : G, f x = (unitaryMatrixDualCoefficientSynthesis G A x).re) →
      f g = changed) : False := by
  obtain ⟨f, hf, hpointwise⟩ :=
    unitaryMatrixDualCoefficientSynthesis_realPart_mem_smoothRealCore
      smoothCoverage A
  exact changed_ne_exact ((claimed f hf hpointwise).symm.trans (hpointwise g))

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact topological realification probe: real part retracts complexification and is nonexpansive. -/
theorem exact_continuousMap_complex_realification
    [CompactSpace G] (f : C(G, ℝ)) (h k : C(G, ℂ)) :
    continuousMapComplexRealPart (continuousMapComplexOfReal f) = f ∧
      dist (continuousMapComplexRealPart h) (continuousMapComplexRealPart k) ≤ dist h k :=
  ⟨continuousMapComplexRealPart_ofReal f,
    dist_continuousMapComplexRealPart_le h k⟩

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact conditional density transfer from continuous selected Peter--Weyl density and smooth-dual
coverage to the real smooth coefficient image. -/
theorem exact_smoothRealCoefficientCore_density
    [CompactSpace G] [T2Space G]
    (continuousDensity : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E)) :
    Dense (smoothLieGroupScalarToContinuousLinearMap ''
      smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) : Set C(G, ℝ)) :=
  smoothUnitaryMatrixCoefficientRealCore_continuousImage_dense
    continuousDensity smoothCoverage

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact ambient smooth-density consequence of the same selected Fourier hypotheses. -/
theorem exact_smoothAmbientDensity_of_selectedPeterWeyl_smoothCoverage
    [CompactSpace G] [T2Space G]
    (continuousDensity : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E)) :
    SmoothLieGroupScalarFunctionsDenseInContinuous (E := E) (G := G) :=
  smoothLieGroupScalarFunctionsDenseInContinuous_of_continuousPeterWeyl_of_smoothCoverage
    continuousDensity smoothCoverage

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact automatic-smoothness specialization of the density transfer. -/
theorem exact_smoothRealCoefficientCore_density_of_automaticSmoothness
    [CompactSpace G] [T2Space G]
    (continuousDensity : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (automaticSmoothness :
      AllContinuousUnitaryIrreducibleMatrixRepresentationsHaveSmoothCoordinates
        (E := E) (G := G)) :
    Dense (smoothLieGroupScalarToContinuousLinearMap ''
      smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) : Set C(G, ℝ)) :=
  smoothUnitaryMatrixCoefficientRealCore_continuousImage_dense_of_automaticSmoothness
    continuousDensity automaticSmoothness

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Hostile density probe: failure of the target real density contradicts simultaneous selected
continuous density and all-class smooth coverage. -/
theorem missing_smoothRealCoefficientCore_density_blocks_joint_hypotheses
    [CompactSpace G] [T2Space G]
    (missing : ¬ Dense (smoothLieGroupScalarToContinuousLinearMap ''
      smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) : Set C(G, ℝ)))
    (continuousDensity : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E)) : False :=
  missing (smoothUnitaryMatrixCoefficientRealCore_continuousImage_dense
    continuousDensity smoothCoverage)

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact faithful compact matrix-group specialization retaining smooth coverage explicitly. -/
theorem exact_smoothRealCoefficientCore_density_of_faithful
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E)) :
    Dense (smoothLieGroupScalarToContinuousLinearMap ''
      smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) : Set C(G, ℝ)) :=
  smoothUnitaryMatrixCoefficientRealCore_continuousImage_dense_of_faithful
    faithful smoothCoverage

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Exact faithful-plus-automatic-smoothness density specialization. -/
theorem exact_smoothRealCoefficientCore_density_of_faithful_of_automaticSmoothness
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (automaticSmoothness :
      AllContinuousUnitaryIrreducibleMatrixRepresentationsHaveSmoothCoordinates
        (E := E) (G := G)) :
    Dense (smoothLieGroupScalarToContinuousLinearMap ''
      smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) : Set C(G, ℝ)) :=
  smoothUnitaryMatrixCoefficientRealCore_continuousImage_dense_of_faithful_of_automaticSmoothness
    faithful automaticSmoothness

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
