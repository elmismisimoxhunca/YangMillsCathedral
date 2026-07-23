/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactMatrixGroupCoefficientDensity
import YangMills.Mathematics.UnitaryMatrixDualL2Span
import YangMills.Mathematics.RepresentationEquivMatrixCoefficientTransport
import Mathlib.RingTheory.SimpleModule.Rank
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Selected-dual continuous and L² density for compact matrix groups

For every bundled irreducible unitary representation, this file transports each coefficient to a
finite coefficient synthesis of the noncomputably selected representative of its quotient
`UnitaryMatrixDual` class. It also constructs the one-dimensional trivial class explicitly. Hence
the previously constructed finite coefficient star algebra lies in the selected-dual synthesis
range.

Under Hall's explicit faithful finite matrix-representation hypothesis, the selected-dual range is
therefore uniformly dense in `C(G, ℂ)`. Regularity of normalized compact Haar measure and Mathlib's
density of continuous functions in normalized-Haar `L²` then prove the existing coordinate-dual Peter–Weyl completeness
target.

These are conditional compact matrix-group results. They do not prove point separation for an
arbitrary compact Hausdorff group, countability of the unitary dual, or infinite Fourier inversion.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

/-- The one-dimensional trivial complex matrix representation. -/
noncomputable def trivialOneDimensionalMatrixRepresentation
    (G:Type uG) [Group G] : G →* Matrix (Fin 1) (Fin 1) ℂ where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := by simp

/-- The one-dimensional trivial matrix representation is irreducible. -/
theorem trivialOneDimensionalMatrixRepresentation_irreducible (G:Type uG) [Group G] :
    Representation.IsIrreducible (matrixRepresentation (trivialOneDimensionalMatrixRepresentation G)) := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  rw [isSimpleModule_iff]
  apply is_simple_module_of_finrank_eq_one (K:=ℂ)
  change Module.finrank ℂ (Fin 1 → ℂ) = 1
  simp

/-- The explicit positive-dimensional continuous irreducible unitary bundle for the trivial
representation. -/
noncomputable def trivialContinuousUnitaryIrreducibleMatrixRepresentation
    (G:Type uG) [Group G] [TopologicalSpace G] :
    ContinuousUnitaryIrreducibleMatrixRepresentation G where
  dimension := 1
  dimension_pos := by omega
  representation := trivialOneDimensionalMatrixRepresentation G
  continuous_representation := by
    change Continuous (fun _ : G => (1 : Matrix (Fin 1) (Fin 1) ℂ))
    fun_prop
  unitary_representation := by intro g; simp [trivialOneDimensionalMatrixRepresentation]
  irreducible_representation := trivialOneDimensionalMatrixRepresentation_irreducible G

/-- A selected exact representation equivalence from a bundle to the chosen representative of
its unitary-dual quotient class. -/
noncomputable def unitaryMatrixDualSelectedRepresentativeEquiv
    {G:Type uG} [Group G] [TopologicalSpace G]
    (ρ:ContinuousUnitaryIrreducibleMatrixRepresentation G) :
    Representation.Equiv (matrixRepresentation ρ.representation)
      (matrixRepresentation (unitaryMatrixDualRepresentation (unitaryMatrixDualClass ρ))) :=
  Classical.choice (unitaryMatrixDual_equivalent_representative ρ)

/-- The coefficient matrix in the selected representative whose synthesis recovers one specified
coefficient in the original equivalent presentation. -/
noncomputable def unitaryMatrixDualSelectedCoefficientMatrix
    {G:Type uG} [Group G] [TopologicalSpace G]
    (ρ:ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column:Fin ρ.dimension) :
    Matrix (Fin (unitaryMatrixDualDimension (unitaryMatrixDualClass ρ)))
      (Fin (unitaryMatrixDualDimension (unitaryMatrixDualClass ρ))) ℂ :=
  fun sr sc => representationEquivMatrix (unitaryMatrixDualSelectedRepresentativeEquiv ρ).symm row sr *
    representationEquivInverseMatrix (unitaryMatrixDualSelectedRepresentativeEquiv ρ).symm sc column

/-- Exact finite selected-representative synthesis of an arbitrary bundled irreducible-unitary
coefficient. -/
theorem unitaryMatrixDualCoefficientSynthesis_selectedCoefficient
    {G:Type uG} [Group G] [TopologicalSpace G]
    (ρ:ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column:Fin ρ.dimension) :
    unitaryMatrixDualCoefficientSynthesis G
      (unitaryMatrixDualCoefficientSingle (unitaryMatrixDualClass ρ)
        (unitaryMatrixDualSelectedCoefficientMatrix ρ row column)) =
      fun g => ρ.representation g row column := by
  rw [unitaryMatrixDualCoefficientSynthesis_single]
  funext g
  rw [representationEquiv_matrixCoefficient
    (unitaryMatrixDualRepresentation (unitaryMatrixDualClass ρ)) ρ.representation
    (unitaryMatrixDualSelectedRepresentativeEquiv ρ).symm g row column]
  change (∑ sr, ∑ sc, unitaryMatrixDualSelectedCoefficientMatrix ρ row column sr sc *
    unitaryMatrixDualRepresentation (unitaryMatrixDualClass ρ) g sr sc) = _
  apply Finset.sum_congr rfl
  intro sr _
  apply Finset.sum_congr rfl
  intro sc _
  simp only [unitaryMatrixDualSelectedCoefficientMatrix]
  ring

/-- Every bundled irreducible-unitary continuous coefficient belongs to the selected-dual
continuous synthesis range. -/
theorem continuousUnitaryCoefficient_mem_unitaryMatrixDualContinuousRange
    {G:Type uG} [Group G] [TopologicalSpace G]
    (ρ:ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column:Fin ρ.dimension) :
    ρ.continuousCoefficient row column ∈
      LinearMap.range (unitaryMatrixDualContinuousCoefficientSynthesis G) := by
  refine ⟨unitaryMatrixDualCoefficientSingle (unitaryMatrixDualClass ρ)
    (unitaryMatrixDualSelectedCoefficientMatrix ρ row column), ?_⟩
  ext g
  exact congrFun (unitaryMatrixDualCoefficientSynthesis_selectedCoefficient ρ row column) g

/-- The constant function one belongs to the selected-dual continuous synthesis range through the
explicit trivial representation class. -/
theorem one_mem_unitaryMatrixDualContinuousRange
    {G:Type uG} [Group G] [TopologicalSpace G] :
    (1:C(G,ℂ)) ∈ LinearMap.range (unitaryMatrixDualContinuousCoefficientSynthesis G) := by
  rcases continuousUnitaryCoefficient_mem_unitaryMatrixDualContinuousRange (trivialContinuousUnitaryIrreducibleMatrixRepresentation G) (0:Fin 1) (0:Fin 1) with ⟨A,hA⟩
  refine ⟨A, ?_⟩
  rw [hA]
  ext g
  change (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = 1
  simp

/-- The full finite irreducible-unitary coefficient span with constants is contained in the
selected quotient-dual continuous synthesis range. -/
theorem compactUnitaryCoefficientSpan_le_unitaryMatrixDualContinuousRange
    {G:Type uG} [Group G] [TopologicalSpace G] :
    compactUnitaryCoefficientSpan (G:=G) ≤
      LinearMap.range (unitaryMatrixDualContinuousCoefficientSynthesis G) := by
  apply Submodule.span_le.mpr
  intro f hf
  rcases hf with rfl | ⟨ρ,i,j,rfl⟩
  · exact one_mem_unitaryMatrixDualContinuousRange
  · exact continuousUnitaryCoefficient_mem_unitaryMatrixDualContinuousRange ρ i j

/-- Under an explicit faithful finite matrix representation, the selected quotient-dual
continuous coefficient synthesis has dense range in `C(G, ℂ)`. -/
theorem unitaryMatrixDualContinuousCoefficientSynthesis_denseRange_of_faithful
    {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (faithful:ContinuousFaithfulFiniteMatrixRepresentation G) :
    Dense (LinearMap.range (unitaryMatrixDualContinuousCoefficientSynthesis G) : Set C(G,ℂ)) := by
  apply Dense.mono (compactUnitaryCoefficientSpan_le_unitaryMatrixDualContinuousRange (G:=G))
  rw [dense_iff_closure_eq]
  have h := congrArg (fun A : StarSubalgebra ℂ C(G,ℂ) => (A : Set C(G,ℂ)))
    (compactUnitaryCoefficientStarSubalgebra_topologicalClosure_eq_top_of_faithful faithful)
  rw [StarSubalgebra.topologicalClosure_coe] at h
  exact h

/-- The canonical map from continuous functions to normalized-Haar `L²`, with probability
finiteness installed locally rather than required as an external instance. -/
noncomputable def normalizedCompactHaarContinuousToL2
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    C(G, ℂ) →L[ℂ] NormalizedCompactHaarL2 G := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  exact ContinuousMap.toLp 2 (normalizedCompactHaarMeasure G) ℂ

/-- Mapping any member of the selected-dual continuous synthesis range into normalized-Haar
`L²` lands in the selected-dual algebraic `L²` range. -/
theorem unitaryMatrixDual_toLp_continuousRange_subset_L2AlgebraicRange
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    normalizedCompactHaarContinuousToL2 G ''
      (LinearMap.range (unitaryMatrixDualContinuousCoefficientSynthesis G) : Set C(G, ℂ)) ⊆
      (unitaryMatrixDualL2AlgebraicRange G : Set (NormalizedCompactHaarL2 G)) := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  rintro f ⟨continuousCoefficient, ⟨A, hA⟩, rfl⟩
  refine ⟨A, ?_⟩
  change normalizedCompactHaarContinuousToL2 G
      (unitaryMatrixDualContinuousCoefficientSynthesis G A) =
    normalizedCompactHaarContinuousToL2 G continuousCoefficient
  rw [hA]

/-- Under faithful finite matrix coordinates, regularity of normalized compact Haar measure
transfers selected-dual continuous density to dense algebraic coefficient range in normalized-Haar
`L²`. -/
theorem unitaryMatrixDual_hasL2PeterWeylCompleteness_of_faithful
    {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (faithful:ContinuousFaithfulFiniteMatrixRepresentation G) :
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
  have denseS : DenseRange (fun f:S => (f:C(G,ℂ))) :=
    denseRange_subtype_val.mpr (unitaryMatrixDualContinuousCoefficientSynthesis_denseRange_of_faithful faithful)
  have denseToLp : DenseRange (ContinuousMap.toLp 2 μ ℂ : C(G,ℂ) →L[ℂ] Lp ℂ 2 μ) :=
    ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num)
  have denseComp := denseToLp.comp denseS
    (ContinuousMap.toLp 2 μ ℂ).continuous
  rw [unitaryMatrixDual_hasL2PeterWeylCompleteness_iff_dense]
  apply Dense.mono _ denseComp
  rintro f ⟨s, rfl⟩
  exact unitaryMatrixDual_toLp_continuousRange_subset_L2AlgebraicRange
    ⟨(s : C(G, ℂ)), s.property, rfl⟩

end

end Mathematics
end YangMills
