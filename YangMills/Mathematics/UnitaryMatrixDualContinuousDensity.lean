/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactMatrixGroupSelectedDualDensity

/-!
# The exact selected-dual continuous Peter–Weyl density target

The finite span of constants and all bundled continuous irreducible-unitary coefficients was defined
using arbitrary coordinate presentations. This file proves that it is exactly—not merely contained
in—the range of finite-support synthesis over the quotient-selected `UnitaryMatrixDual`
representatives.

It then names the general continuous Peter–Weyl density obligation as density of this selected-dual
range and proves that:

* a faithful finite matrix representation supplies the obligation;
* the obligation implies the existing normalized-Haar `L²` completeness target.

For arbitrary compact Hausdorff groups the obligation remains uninhabited here. No countability,
infinite inversion, or series convergence is inferred.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

/-- Continuous-map packaging of a finite matrix-coefficient synthesis. -/
noncomputable def continuousMatrixCoefficientSynthesis
    {G : Type uG} [Group G] [TopologicalSpace G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (A : Matrix (Fin n) (Fin n) ℂ) : C(G, ℂ) :=
  ⟨matrixCoefficientSynthesis ρ A, continuous_matrixCoefficientSynthesis ρ hρ A⟩

/-- Every finite synthesis for an arbitrary continuous matrix representation belongs to the finite
irreducible-unitary coefficient span. -/
theorem continuousMatrixCoefficientSynthesis_mem_compactUnitaryCoefficientSpan
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    continuousMatrixCoefficientSynthesis ρ hρ A ∈
      compactUnitaryCoefficientSpan (G := G) := by
  have synthesis_eq : continuousMatrixCoefficientSynthesis ρ hρ A =
      ∑ i, ∑ j, A i j • continuousMatrixRepresentationCoefficient ρ hρ i j := by
    ext g
    change (∑ i, ∑ j, A i j * ρ g i j) =
      (ContinuousMap.evalAlgHom ℂ ℂ g) (∑ i, ∑ j,
        A i j • continuousMatrixRepresentationCoefficient ρ hρ i j)
    rw [map_sum (ContinuousMap.evalAlgHom ℂ ℂ g)]
    simp_rw [map_sum (ContinuousMap.evalAlgHom ℂ ℂ g)]
    rfl
  rw [synthesis_eq]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _
    (continuousMatrixRepresentationCoefficient_mem_span ρ hρ i j)

/-- Every finite-support selected quotient-dual synthesis belongs to the finite coefficient span. -/
theorem unitaryMatrixDualContinuousCoefficientSynthesis_mem_compactUnitaryCoefficientSpan
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (A : UnitaryMatrixDualCoefficientSpace G) :
    unitaryMatrixDualContinuousCoefficientSynthesis G A ∈
      compactUnitaryCoefficientSpan (G := G) := by
  classical
  induction A using DirectSum.induction_on with
  | zero => simp
  | of q A =>
      change unitaryMatrixDualContinuousCoefficientSynthesis G
        (unitaryMatrixDualCoefficientSingle q A) ∈ _
      have synthesis_eq : unitaryMatrixDualContinuousCoefficientSynthesis G
          (unitaryMatrixDualCoefficientSingle q A) =
          continuousMatrixCoefficientSynthesis (unitaryMatrixDualRepresentation q)
            (continuous_unitaryMatrixDualRepresentation q) A := by
        ext g
        exact congrFun (unitaryMatrixDualCoefficientSynthesis_single q A) g
      rw [synthesis_eq]
      exact continuousMatrixCoefficientSynthesis_mem_compactUnitaryCoefficientSpan _ _ _
  | add A B hA hB =>
      rw [map_add]
      exact Submodule.add_mem _ hA hB

/-- The selected quotient-dual continuous synthesis range is contained in the finite coefficient
span. -/
theorem unitaryMatrixDualContinuousCoefficientSynthesis_range_le_span
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    LinearMap.range (unitaryMatrixDualContinuousCoefficientSynthesis G) ≤
      compactUnitaryCoefficientSpan (G := G) := by
  rintro f ⟨A, rfl⟩
  exact unitaryMatrixDualContinuousCoefficientSynthesis_mem_compactUnitaryCoefficientSpan A

/-- Exact algebraic identification: selected quotient-dual finite-support synthesis has precisely the
same range as the finite span of constants and all bundled irreducible-unitary coefficients. -/
theorem unitaryMatrixDualContinuousCoefficientSynthesis_range_eq_span
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    LinearMap.range (unitaryMatrixDualContinuousCoefficientSynthesis G) =
      compactUnitaryCoefficientSpan (G := G) :=
  le_antisymm unitaryMatrixDualContinuousCoefficientSynthesis_range_le_span
    compactUnitaryCoefficientSpan_le_unitaryMatrixDualContinuousRange

/-- General selected-coordinate continuous Peter–Weyl density target. -/
def UnitaryMatrixDual.HasContinuousPeterWeylDensity
    (G : Type uG) [Group G] [TopologicalSpace G] : Prop :=
  Dense (LinearMap.range (unitaryMatrixDualContinuousCoefficientSynthesis G) : Set C(G, ℂ))

/-- The continuous density target is exactly density of the finite irreducible-unitary coefficient
span. -/
theorem unitaryMatrixDual_hasContinuousPeterWeylDensity_iff_span_dense
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    UnitaryMatrixDual.HasContinuousPeterWeylDensity G ↔
      Dense (compactUnitaryCoefficientSpan (G := G) : Set C(G, ℂ)) := by
  rw [UnitaryMatrixDual.HasContinuousPeterWeylDensity,
    unitaryMatrixDualContinuousCoefficientSynthesis_range_eq_span]

/-- A continuous faithful finite matrix representation supplies selected-dual continuous
Peter–Weyl density. -/
theorem unitaryMatrixDual_hasContinuousPeterWeylDensity_of_faithful
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G) :
    UnitaryMatrixDual.HasContinuousPeterWeylDensity G :=
  unitaryMatrixDualContinuousCoefficientSynthesis_denseRange_of_faithful faithful

/-- General bridge from selected-dual uniform density to normalized-Haar `L²` completeness. -/
theorem UnitaryMatrixDual.HasContinuousPeterWeylDensity.hasL2PeterWeylCompleteness
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (density : UnitaryMatrixDual.HasContinuousPeterWeylDensity G) :
    UnitaryMatrixDual.HasL2PeterWeylCompleteness G := by
  let μ := normalizedCompactHaarMeasure G
  let S := LinearMap.range (unitaryMatrixDualContinuousCoefficientSynthesis G)
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  letI : μ.WeaklyRegular := by
    dsimp only [μ, normalizedCompactHaarMeasure]
    letI : (Measure.haar (G := G)).Regular := inferInstance
    letI : (((Measure.haar (G := G)) Set.univ)⁻¹ • Measure.haar (G := G)).Regular :=
      Measure.Regular.smul (ENNReal.inv_ne_top.mpr
        (Measure.measure_univ_eq_zero.not.mpr (NeZero.ne _)))
    exact Measure.Regular.weaklyRegular
  have denseS : DenseRange (fun f : S => (f : C(G, ℂ))) :=
    denseRange_subtype_val.mpr density
  have denseToLp : DenseRange
      (ContinuousMap.toLp 2 μ ℂ : C(G, ℂ) →L[ℂ] Lp ℂ 2 μ) :=
    ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num)
  have denseComp := denseToLp.comp denseS (ContinuousMap.toLp 2 μ ℂ).continuous
  rw [unitaryMatrixDual_hasL2PeterWeylCompleteness_iff_dense]
  apply Dense.mono _ denseComp
  rintro f ⟨s, rfl⟩
  exact unitaryMatrixDual_toLp_continuousRange_subset_L2AlgebraicRange
    ⟨(s : C(G, ℂ)), s.property, rfl⟩

end

end Mathematics
end YangMills
