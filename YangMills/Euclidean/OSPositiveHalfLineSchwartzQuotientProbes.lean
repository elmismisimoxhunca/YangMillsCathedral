/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSPositiveHalfLineSchwartzQuotient

/-!
# Hostile probes for the OS positive-half-line Schwartz quotient

The probes lock support semantics, closedness, quotient topology and surjectivity, exact CLM
packaging, Hausdorff separation, and a nonzero positive representative.
-/

namespace YangMills.OSPositiveHalfLineSchwartzQuotient.Probes

open Filter
open scoped Topology

noncomputable section

/-- Negative-half-line membership is exactly nonpositive topological support. -/
theorem exact_negative_support
    (f : OneDimensionalComplexSchwartzSpace) :
    f ∈ osNegativeHalfLineSchwartzSubmodule ↔ tsupport f ⊆ Set.Iic 0 :=
  mem_osNegativeHalfLineSchwartzSubmodule_iff_tsupport f

/-- The quotient kernel is a genuine closed subspace, not an arbitrary equivalence relation. -/
theorem exact_closed_negative_submodule :
    IsClosed (osNegativeHalfLineSchwartzSubmodule :
      Set OneDimensionalComplexSchwartzSpace) :=
  isClosed_osNegativeHalfLineSchwartzSubmodule

/-- The canonical map has the actual quotient topology and reaches every quotient class. -/
theorem exact_quotient_map :
    Topology.IsQuotientMap osPositiveHalfLineSchwartzQuotientMap ∧
      Function.Surjective osPositiveHalfLineSchwartzQuotientMap :=
  ⟨osPositiveHalfLineSchwartzQuotientMap_isQuotientMap,
    osPositiveHalfLineSchwartzQuotientMap_isQuotientMap.surjective⟩

/-- Zero quotient classes are exactly representatives supported in the nonpositive half-line. -/
theorem exact_quotient_zero_iff
    (f : OneDimensionalComplexSchwartzSpace) :
    osPositiveHalfLineSchwartzQuotientMap f = 0 ↔ tsupport f ⊆ Set.Iic 0 :=
  osPositiveHalfLineSchwartzQuotientMap_eq_zero_iff f

/-- Continuous-linear packaging retains the exact quotient class. -/
theorem exact_quotient_clm (f : OneDimensionalComplexSchwartzSpace) :
    osPositiveHalfLineSchwartzQuotientCLM f =
      osPositiveHalfLineSchwartzQuotientMap f :=
  rfl

/-- The explicit representative really has nonnegative topological support. -/
theorem exact_positive_bump_support :
    tsupport osPositiveHalfLineBumpSchwartz ⊆ Set.Ici 0 :=
  osPositiveHalfLineBumpSchwartz_tsupport_subset

/-- The explicit positive bump remains visible at its exact center. -/
theorem positive_bump_value_retained : osPositiveHalfLineBumpSchwartz 1 = 1 :=
  osPositiveHalfLineBumpSchwartz_one

/-- The quotient cannot collapse to the zero space. -/
theorem nonzero_positive_class_retained :
    osPositiveHalfLineSchwartzQuotientMap osPositiveHalfLineBumpSchwartz ≠ 0 :=
  osPositiveHalfLineBumpQuotient_ne_zero

/-- Named quotient structures expose genuine joint addition and complex scalar continuity. -/
theorem exact_named_topological_operations :
    letI : IsTopologicalAddGroup OSPositiveHalfLineSchwartzSpace :=
      osPositiveHalfLineSchwartzIsTopologicalAddGroup
    letI : ContinuousSMul ℂ OSPositiveHalfLineSchwartzSpace :=
      osPositiveHalfLineSchwartzContinuousSMul
    Continuous (fun p : OSPositiveHalfLineSchwartzSpace × OSPositiveHalfLineSchwartzSpace =>
      p.1 + p.2) ∧
    Continuous (fun p : ℂ × OSPositiveHalfLineSchwartzSpace => p.1 • p.2) := by
  letI : IsTopologicalAddGroup OSPositiveHalfLineSchwartzSpace :=
    osPositiveHalfLineSchwartzIsTopologicalAddGroup
  letI : ContinuousSMul ℂ OSPositiveHalfLineSchwartzSpace :=
    osPositiveHalfLineSchwartzContinuousSMul
  exact ⟨continuous_add, continuous_smul⟩

/-- Named quotient local convexity gives an actual convex refinement of every zero neighborhood. -/
theorem exact_convex_zero_neighborhood
    (U : Set OSPositiveHalfLineSchwartzSpace)
    (hU : U ∈ 𝓝 (0 : OSPositiveHalfLineSchwartzSpace)) :
    ∃ V ∈ 𝓝 (0 : OSPositiveHalfLineSchwartzSpace), Convex ℝ V ∧ V ⊆ U := by
  letI : IsTopologicalAddGroup OSPositiveHalfLineSchwartzSpace :=
    osPositiveHalfLineSchwartzIsTopologicalAddGroup
  letI : LocallyConvexSpace ℝ OSPositiveHalfLineSchwartzSpace :=
    osPositiveHalfLineSchwartzLocallyConvexSpace
  exact (locallyConvexSpace_iff_exists_convex_subset_zero ℝ
    OSPositiveHalfLineSchwartzSpace).mp inferInstance U hU

/-- Installing the named Hausdorff structure separates the positive bump class from zero by
disjoint open neighborhoods. -/
theorem exact_hausdorff_nonzero_separation :
    letI : T2Space OSPositiveHalfLineSchwartzSpace := osPositiveHalfLineSchwartzT2Space
    ∃ U V : Set OSPositiveHalfLineSchwartzSpace,
      IsOpen U ∧ IsOpen V ∧
      osPositiveHalfLineSchwartzQuotientMap osPositiveHalfLineBumpSchwartz ∈ U ∧
      (0 : OSPositiveHalfLineSchwartzSpace) ∈ V ∧ Disjoint U V := by
  letI : T2Space OSPositiveHalfLineSchwartzSpace := osPositiveHalfLineSchwartzT2Space
  exact t2_separation osPositiveHalfLineBumpQuotient_ne_zero

end

end YangMills.OSPositiveHalfLineSchwartzQuotient.Probes
