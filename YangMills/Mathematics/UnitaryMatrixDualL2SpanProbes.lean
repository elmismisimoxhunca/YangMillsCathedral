/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualL2Span

/-!
# Hostile probes for the normalized-Haar `L²` coefficient span
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualL2Span
namespace Probes

open MeasureTheory

noncomputable section

universe uG

/-- The actual Mathlib `L²` inner product retains the exact algebraic Fourier pairing. -/
theorem exact_l2_inner_plancherel
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (A B : UnitaryMatrixDualCoefficientSpace G) :
    inner ℂ (unitaryMatrixDualL2CoefficientSynthesis G A)
      (unitaryMatrixDualL2CoefficientSynthesis G B) =
        unitaryMatrixDualAlgebraicFourierPairing A B :=
  unitaryMatrixDualL2CoefficientSynthesis_inner A B

/-- Every algebraically synthesized vector belongs to the exact algebraic `L²` range. -/
theorem synthesis_mem_algebraic_range
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (A : UnitaryMatrixDualCoefficientSpace G) :
    unitaryMatrixDualL2CoefficientSynthesis G A ∈
      unitaryMatrixDualL2AlgebraicRange G := by
  exact ⟨A, rfl⟩

/-- The algebraic range is contained in the closed coefficient span. -/
theorem algebraic_range_mem_closed_span
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (vector : NormalizedCompactHaarL2 G)
    (member : vector ∈ unitaryMatrixDualL2AlgebraicRange G) :
    vector ∈ unitaryMatrixDualL2CoefficientClosedSpan G :=
  unitaryMatrixDualL2AlgebraicRange_le_closedSpan G member

/-- The coefficient closure is genuinely closed in the `L²` topology. -/
theorem coefficient_span_is_closed
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    IsClosed (unitaryMatrixDualL2CoefficientClosedSpan G :
      Set (NormalizedCompactHaarL2 G)) :=
  unitaryMatrixDualL2CoefficientClosedSpan_isClosed G

/-- The exact Peter–Weyl target is equivalent to density of the finite-support algebraic image. -/
theorem completeness_iff_dense_algebraic_range
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] :
    UnitaryMatrixDual.HasL2PeterWeylCompleteness G ↔
      Dense (unitaryMatrixDualL2AlgebraicRange G :
        Set (NormalizedCompactHaarL2 G)) :=
  unitaryMatrixDual_hasL2PeterWeylCompleteness_iff_dense

/-- Hostile completeness probe: a single `L²` vector outside the closed coefficient span prevents
Peter–Weyl completeness. -/
theorem vector_outside_closed_span_blocks_completeness
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (vector : NormalizedCompactHaarL2 G)
    (outside : vector ∉ unitaryMatrixDualL2CoefficientClosedSpan G) :
    ¬UnitaryMatrixDual.HasL2PeterWeylCompleteness G := by
  intro complete
  apply outside
  rw [complete]
  exact Submodule.mem_top

/-- Hostile density probe: failure of density directly blocks the completeness target; no build or
algebraic Plancherel theorem can substitute for this analytic obligation. -/
theorem nondense_range_blocks_completeness
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (notDense : ¬Dense (unitaryMatrixDualL2AlgebraicRange G :
      Set (NormalizedCompactHaarL2 G))) :
    ¬UnitaryMatrixDual.HasL2PeterWeylCompleteness G := by
  intro complete
  exact notDense
    (unitaryMatrixDual_hasL2PeterWeylCompleteness_iff_dense.mp complete)

end

end Probes
end UnitaryMatrixDualL2Span
end Mathematics
end YangMills
