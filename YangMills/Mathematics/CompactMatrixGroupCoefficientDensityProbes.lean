/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactMatrixGroupCoefficientDensity

/-!
# Hostile probes for conditional compact matrix-group coefficient density
-/

namespace YangMills
namespace Mathematics
namespace CompactMatrixGroupCoefficientDensity
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Faithfulness gives an exact separating matrix entry, not merely matrix inequality. -/
theorem exact_faithful_entry_separation
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    {x y : G} (hxy : x ≠ y) :
    ∃ i j, faithful.representation x i j ≠ faithful.representation y i j :=
  faithful.exists_entry_ne hxy

/-- Hostile faithfulness probe: a changed representation value on distinct points is contradictory. -/
theorem changed_faithful_value_blocked
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    {x y : G} (hxy : x ≠ y)
    (changed : faithful.representation x = faithful.representation y) : False :=
  hxy (faithful.faithful_representation changed)

/-- A genuinely distinct pair forces the coordinate dimension to be positive. Thus dimension zero
cannot separate distinct group elements. -/
theorem positive_dimension_of_distinct
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    {x y : G} (hxy : x ≠ y) :
    0 < faithful.dimension := by
  rcases faithful.exists_entry_ne hxy with ⟨i, -, -⟩
  exact Fin.pos_iff_nonempty.mpr ⟨i⟩

variable [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

/-- Point separation follows under the explicit faithful finite representation hypothesis. -/
theorem exact_conditional_point_separation
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G) :
    (compactUnitaryCoefficientStarSubalgebra (G := G)).SeparatesPoints :=
  compactUnitaryCoefficientStarSubalgebra_separatesPoints_of_faithful faithful

/-- Stone–Weierstrass density follows under the same explicit hypothesis. -/
theorem exact_conditional_density
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G) :
    (compactUnitaryCoefficientStarSubalgebra (G := G)).topologicalClosure = ⊤ :=
  compactUnitaryCoefficientStarSubalgebra_topologicalClosure_eq_top_of_faithful faithful

/-- Hostile density probe: changing the conditional closure result is contradictory. -/
theorem changed_conditional_density_blocked
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (changed :
      (compactUnitaryCoefficientStarSubalgebra (G := G)).topologicalClosure ≠ ⊤) : False :=
  changed (compactUnitaryCoefficientStarSubalgebra_topologicalClosure_eq_top_of_faithful faithful)

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- The theorem does not hide the matrix-group hypothesis: its reusable input remains explicit. -/
theorem faithful_hypothesis_is_data
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G) :
    Function.Injective faithful.representation :=
  faithful.faithful_representation

end

end Probes
end CompactMatrixGroupCoefficientDensity
end Mathematics
end YangMills
