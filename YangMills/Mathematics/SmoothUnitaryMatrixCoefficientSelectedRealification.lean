/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualContinuousDensity
import YangMills.Mathematics.SmoothUnitaryMatrixCoefficientRealCore

/-!
# Realification of selected-dual coefficients through smooth representatives

A selected continuous unitary-dual class with an explicitly retained smooth representative can be
transported, with both change-of-basis matrices, to a finite coefficient synthesis in that smooth
presentation. Taking its real part then lands in the existing smooth real matrix-coefficient core.

This file does not assert that every continuous-dual class has a smooth representative and does not
identify raw coefficients across presentations. It transfers an explicitly supplied selected
continuous Peter--Weyl density theorem to real smooth-core density only under explicit all-class
smooth coverage; neither premise is constructed here.
-/

namespace YangMills
namespace Mathematics

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

/-- Pointwise complexification of a continuous real function. -/
def continuousMapComplexOfReal (f : C(G, ℝ)) : C(G, ℂ) :=
  ⟨fun g => (f g : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

/-- Pointwise real part of a continuous complex function. -/
def continuousMapComplexRealPart (f : C(G, ℂ)) : C(G, ℝ) :=
  ⟨fun g => (f g).re, Complex.continuous_re.comp f.continuous⟩

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
@[simp]
theorem continuousMapComplexRealPart_ofReal (f : C(G, ℝ)) :
    continuousMapComplexRealPart (continuousMapComplexOfReal f) = f := by
  ext g
  rfl

omit [Group G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Taking pointwise real parts is nonexpansive in the uniform norm. -/
theorem dist_continuousMapComplexRealPart_le
    [CompactSpace G] (f h : C(G, ℂ)) :
    dist (continuousMapComplexRealPart f) (continuousMapComplexRealPart h) ≤ dist f h := by
  rw [dist_eq_norm, dist_eq_norm]
  apply (ContinuousMap.norm_le (f :=
    continuousMapComplexRealPart f - continuousMapComplexRealPart h)
      (norm_nonneg (f - h))).2
  intro g
  change |(f g).re - (h g).re| ≤ ‖f - h‖
  rw [← Complex.sub_re]
  exact (Complex.abs_re_le_norm (f g - h g)).trans
    (ContinuousMap.norm_coe_le_norm (f - h) g)

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- One selected-dual coefficient block whose class has a smooth representative has a real part in
the exact smooth real coefficient core. The witness retains the chosen smooth presentation and the
basis-aware pulled-back coefficient matrix. -/
theorem unitaryMatrixDualCoefficientSingle_realPart_mem_smoothRealCore
    (q : UnitaryMatrixDual G) (hq : q.HasSmoothRepresentative (E := E))
    (A : Matrix (Fin (unitaryMatrixDualDimension q))
      (Fin (unitaryMatrixDualDimension q)) ℂ) :
    ∃ f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G),
      ∀ g : G, f g =
        (unitaryMatrixDualCoefficientSynthesis G
          (unitaryMatrixDualCoefficientSingle q A) g).re := by
  obtain ⟨ρ, hρ⟩ := q.hasSmoothRepresentative_iff_exists_representation.mp hq
  subst q
  let equivalence := unitaryMatrixDualSelectedRepresentativeEquiv
    ρ.toContinuousUnitaryIrreducibleMatrixRepresentation
  let pulledBack := representationEquivPullbackCoefficientMatrix equivalence A
  refine ⟨smoothUnitaryMatrixCoefficientMatrixRealification ρ pulledBack,
    smoothUnitaryMatrixCoefficientMatrixRealification_mem_coreCandidate ρ pulledBack, ?_⟩
  intro g
  rw [smoothUnitaryMatrixCoefficientMatrixRealification_apply,
    unitaryMatrixDualCoefficientSynthesis_single]
  congr 1
  exact (representationEquiv_weightedMatrixCoefficientSum
    ρ.representation
    (unitaryMatrixDualRepresentation
      (unitaryMatrixDualClass ρ.toContinuousUnitaryIrreducibleMatrixRepresentation))
    equivalence A g).symm

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Continuous-image form of selected-block realification. -/
theorem unitaryMatrixDualCoefficientSingle_realPart_mem_continuousSmoothRealCoreImage
    (q : UnitaryMatrixDual G) (hq : q.HasSmoothRepresentative (E := E))
    (A : Matrix (Fin (unitaryMatrixDualDimension q))
      (Fin (unitaryMatrixDualDimension q)) ℂ) :
    ∃ f ∈ smoothLieGroupScalarToContinuousLinearMap ''
        smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G),
      ∀ g : G, f g =
        (unitaryMatrixDualCoefficientSynthesis G
          (unitaryMatrixDualCoefficientSingle q A) g).re := by
  obtain ⟨smoothFunction, hsmoothFunction, hpointwise⟩ :=
    unitaryMatrixDualCoefficientSingle_realPart_mem_smoothRealCore q hq A
  exact ⟨smoothLieGroupScalarToContinuousLinearMap smoothFunction,
    ⟨smoothFunction, hsmoothFunction, rfl⟩, hpointwise⟩

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- If every selected continuous-dual class has a smooth representative, the real part of every
finite-support selected-dual synthesis belongs to the smooth real coefficient core. The universal
smooth-coverage premise remains explicit. -/
theorem unitaryMatrixDualCoefficientSynthesis_realPart_mem_smoothRealCore
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E))
    (A : UnitaryMatrixDualCoefficientSpace G) :
    ∃ f ∈ smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G),
      ∀ g : G, f g = (unitaryMatrixDualCoefficientSynthesis G A g).re := by
  classical
  induction A using DirectSum.induction_on with
  | zero =>
      refine ⟨0, ?_, ?_⟩
      · change (0 : SmoothLieGroupScalarFunction (E := E) (G := G)) ∈
          smoothUnitaryMatrixCoefficientRealCoreSubmodule (E := E) (G := G)
        exact (smoothUnitaryMatrixCoefficientRealCoreSubmodule
          (E := E) (G := G)).zero_mem
      · intro g
        simp
  | of q coefficientMatrix =>
      exact unitaryMatrixDualCoefficientSingle_realPart_mem_smoothRealCore
        q (smoothCoverage q) coefficientMatrix
  | add A B hA hB =>
      obtain ⟨f, hf, hfpointwise⟩ := hA
      obtain ⟨h, hh, hhpointwise⟩ := hB
      refine ⟨f + h, ?_, ?_⟩
      · change f + h ∈ smoothUnitaryMatrixCoefficientRealCoreSubmodule
          (E := E) (G := G)
        exact (smoothUnitaryMatrixCoefficientRealCoreSubmodule
          (E := E) (G := G)).add_mem hf hh
      · intro g
        rw [SmoothLieGroupScalarFunction.add_apply, hfpointwise g, hhpointwise g,
          map_add]
        exact Complex.add_re _ _

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Continuous-image form of full finite-support selected-dual realification under explicit smooth
coverage of every continuous-dual class. -/
theorem unitaryMatrixDualCoefficientSynthesis_realPart_mem_continuousSmoothRealCoreImage
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E))
    (A : UnitaryMatrixDualCoefficientSpace G) :
    ∃ f ∈ smoothLieGroupScalarToContinuousLinearMap ''
        smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G),
      ∀ g : G, f g = (unitaryMatrixDualCoefficientSynthesis G A g).re := by
  obtain ⟨smoothFunction, hsmoothFunction, hpointwise⟩ :=
    unitaryMatrixDualCoefficientSynthesis_realPart_mem_smoothRealCore
      smoothCoverage A
  exact ⟨smoothLieGroupScalarToContinuousLinearMap smoothFunction,
    ⟨smoothFunction, hsmoothFunction, rfl⟩, hpointwise⟩

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Selected-dual continuous Peter--Weyl density transfers to uniform density of the smooth real
coefficient-core image when every selected continuous class has a smooth representative. The two
premises remain separate and explicit. -/
theorem smoothUnitaryMatrixCoefficientRealCore_continuousImage_dense
    [CompactSpace G] [T2Space G]
    (continuousDensity : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E)) :
    Dense (smoothLieGroupScalarToContinuousLinearMap ''
      smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) : Set C(G, ℝ)) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro f
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨complexApproximation, hcomplexRange, hcomplexDistance⟩ :=
    continuousDensity.exists_dist_lt (continuousMapComplexOfReal f) hε
  obtain ⟨A, rfl⟩ := hcomplexRange
  obtain ⟨realApproximation, hrealCore, hrealPointwise⟩ :=
    unitaryMatrixDualCoefficientSynthesis_realPart_mem_smoothRealCore
      smoothCoverage A
  refine ⟨smoothLieGroupScalarToContinuousLinearMap realApproximation,
    ⟨realApproximation, hrealCore, rfl⟩, ?_⟩
  have hrealification :
      smoothLieGroupScalarToContinuousLinearMap realApproximation =
        continuousMapComplexRealPart
          (unitaryMatrixDualContinuousCoefficientSynthesis G A) := by
    ext g
    exact hrealPointwise g
  rw [hrealification, ← continuousMapComplexRealPart_ofReal f]
  exact (dist_continuousMapComplexRealPart_le
    (continuousMapComplexOfReal f)
    (unitaryMatrixDualContinuousCoefficientSynthesis G A)).trans_lt
      hcomplexDistance

omit [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- Concrete compact matrix-group corollary: a faithful finite continuous representation supplies
the complex density premise, while smooth coverage remains the exact unresolved comparison premise. -/
theorem smoothUnitaryMatrixCoefficientRealCore_continuousImage_dense_of_faithful
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (smoothCoverage : ∀ q : UnitaryMatrixDual G,
      q.HasSmoothRepresentative (E := E)) :
    Dense (smoothLieGroupScalarToContinuousLinearMap ''
      smoothUnitaryMatrixCoefficientRealCoreCandidate (E := E) (G := G) : Set C(G, ℝ)) :=
  smoothUnitaryMatrixCoefficientRealCore_continuousImage_dense
    (unitaryMatrixDual_hasContinuousPeterWeylDensity_of_faithful faithful)
    smoothCoverage

end

end Mathematics
end YangMills
