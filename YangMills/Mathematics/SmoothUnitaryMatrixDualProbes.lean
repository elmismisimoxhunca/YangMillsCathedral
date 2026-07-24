/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.SmoothUnitaryMatrixDual

/-!
# Hostile probes for the smooth/continuous coordinate-dual comparison
-/

namespace YangMills
namespace Mathematics
namespace SmoothUnitaryMatrixDual
namespace Probes

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]

/-- The stored smoothness applies to the exact representation matrix used by the continuous
bundle. -/
theorem exact_matrix_coordinate_smoothness
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G) :
    ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ
        (Fin ρ.toContinuousUnitaryIrreducibleMatrixRepresentation.dimension →
          Fin ρ.toContinuousUnitaryIrreducibleMatrixRepresentation.dimension → ℂ)) ∞
      (fun g i j =>
        ρ.toContinuousUnitaryIrreducibleMatrixRepresentation.representation g i j) :=
  ρ.representation_contMDiff

/-- Forgetting smoothness sends a smooth class to the exact underlying continuous class. -/
theorem exact_class_comparison
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G) :
    smoothUnitaryMatrixDualToUnitaryMatrixDual
        (smoothUnitaryMatrixDualClass ρ) =
      unitaryMatrixDualClass
        ρ.toContinuousUnitaryIrreducibleMatrixRepresentation :=
  smoothUnitaryMatrixDualToUnitaryMatrixDual_class ρ

/-- No two distinct smooth classes collapse after forgetting smoothness. -/
theorem comparison_is_injective :
    Function.Injective
      (smoothUnitaryMatrixDualToUnitaryMatrixDual (E := E) (G := G)) :=
  smoothUnitaryMatrixDualToUnitaryMatrixDual_injective

/-- Every explicitly smooth representation supplies a smooth representative of its underlying
continuous dual class. -/
theorem smooth_bundle_is_in_comparison_image
    (ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G) :
    (unitaryMatrixDualClass
      ρ.toContinuousUnitaryIrreducibleMatrixRepresentation).HasSmoothRepresentative
        (E := E) :=
  unitaryMatrixDualClass_hasSmoothRepresentative ρ

/-- Exact quotient-elimination probe: the image predicate supplies an explicit smooth
presentation of the unchanged continuous class. -/
theorem smooth_representative_extracts_explicit_presentation
    (q : UnitaryMatrixDual G) :
    q.HasSmoothRepresentative (E := E) ↔
      ∃ ρ : SmoothUnitaryIrreducibleMatrixRepresentation E G,
        unitaryMatrixDualClass
          ρ.toContinuousUnitaryIrreducibleMatrixRepresentation = q :=
  q.hasSmoothRepresentative_iff_exists_representation

/-- Exact automatic-smoothness bridge: coordinate smoothness of every bundled continuous
representation supplies smooth coverage of every quotient class. -/
theorem automatic_smooth_coordinates_supply_dual_coverage
    (automaticSmoothness :
      AllContinuousUnitaryIrreducibleMatrixRepresentationsHaveSmoothCoordinates
        (E := E) (G := G)) :
    ∀ q : UnitaryMatrixDual G, q.HasSmoothRepresentative (E := E) :=
  all_unitaryMatrixDual_hasSmoothRepresentative_of_all_hasSmoothCoordinates
    automaticSmoothness

/-- Exact two-way audit: universal quotient-class smooth coverage is equivalent to automatic
smoothness of every explicit continuous coordinate presentation. -/
theorem automatic_smooth_coordinates_iff_dual_coverage :
    AllContinuousUnitaryIrreducibleMatrixRepresentationsHaveSmoothCoordinates
        (E := E) (G := G) ↔
      ∀ q : UnitaryMatrixDual G, q.HasSmoothRepresentative (E := E) :=
  all_hasSmoothCoordinates_iff_all_unitaryMatrixDual_hasSmoothRepresentative

/-- The smooth-to-continuous quotient comparison is surjective exactly when every explicit
continuous irreducible coordinate presentation is smooth. -/
theorem comparison_surjective_iff_automatic_smooth_coordinates :
    Function.Surjective
        (smoothUnitaryMatrixDualToUnitaryMatrixDual (E := E) (G := G)) ↔
      AllContinuousUnitaryIrreducibleMatrixRepresentationsHaveSmoothCoordinates
        (E := E) (G := G) :=
  smoothUnitaryMatrixDual_surjective_iff_all_hasSmoothCoordinates

/-- Hostile automatic-smoothness probe: one explicitly nonsmooth coordinate presentation blocks the
universal automatic-smoothness premise. -/
theorem missing_smooth_coordinates_blocks_automatic_smoothness
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (missing : ¬ρ.HasSmoothCoordinates (E := E)) :
    ¬AllContinuousUnitaryIrreducibleMatrixRepresentationsHaveSmoothCoordinates
      (E := E) (G := G) := by
  intro automaticSmoothness
  exact missing (automaticSmoothness ρ)

/-- The exact comparison debt is retained: surjectivity is equivalent to smooth representability of
every continuous coordinate class. -/
theorem surjectivity_exactly_matches_smooth_coverage :
    Function.Surjective
        (smoothUnitaryMatrixDualToUnitaryMatrixDual (E := E) (G := G)) ↔
      ∀ q : UnitaryMatrixDual G, q.HasSmoothRepresentative (E := E) :=
  smoothUnitaryMatrixDual_surjective_iff_all_hasSmoothRepresentative

/-- Hostile gap probe: one continuous class without a smooth representative rules out surjectivity;
the comparison cannot be silently promoted to an equivalence. -/
theorem missing_smooth_representative_blocks_surjectivity
    (q : UnitaryMatrixDual G)
    (missing : ¬q.HasSmoothRepresentative (E := E)) :
    ¬Function.Surjective
      (smoothUnitaryMatrixDualToUnitaryMatrixDual (E := E) (G := G)) := by
  intro surjective
  apply missing
  rcases surjective q with ⟨smoothClass, equality⟩
  exact ⟨smoothClass, equality⟩

/-- Hostile scope probe: the current comparison gives an embedding and an image predicate, not an
unconditional equivalence of smooth and continuous duals. -/
theorem image_membership_retained
    (q : UnitaryMatrixDual G) :
    q.HasSmoothRepresentative (E := E) ↔
      q ∈ Set.range
        (smoothUnitaryMatrixDualToUnitaryMatrixDual (E := E) (G := G)) :=
  unitaryMatrixDual_hasSmoothRepresentative_iff_mem_range q

end

end Probes
end SmoothUnitaryMatrixDual
end Mathematics
end YangMills
