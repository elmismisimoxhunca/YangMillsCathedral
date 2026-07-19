/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalSourceSpaceLocallyConvex

/-!
# Hostile probes for local convexity of exact OS source spaces

The probes lock the real-linear map to the exact Schwartz function, exercise its algebraic laws and
inducing topology, install the named local-convexity structure, and retain the nonzero source test.
-/

namespace YangMills.OSOrderedFourDimensionalSourceSpaceLocallyConvex.Probes

open scoped Topology

noncomputable section

open Filter OSPositiveTimeOrderedFourDimensionalSourceSpace

noncomputable local instance sourceAddCommGroupForProbes (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  addCommGroup arity

noncomputable local instance sourceModuleForProbes (arity : PositiveArity) :
    Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  module arity

noncomputable local instance sourceTopologicalAddGroupForProbes (arity : PositiveArity) :
    IsTopologicalAddGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  isTopologicalAddGroup arity

/-- The real-linear map cannot replace or forget the exact underlying source test. -/
theorem exact_real_linear_forgetful_map (arity : PositiveArity)
    (f : OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :
    toSchwartzRealLinearMap arity f = f.toSchwartz :=
  rfl

/-- Real scalar multiplication agrees exactly with the ambient Schwartz operation. -/
theorem exact_real_scalar_action (arity : PositiveArity) (c : ℝ)
    (f : OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :
    toSchwartzRealLinearMap arity (c • f) = c • f.toSchwartz :=
  map_smul (toSchwartzRealLinearMap arity) c f

/-- The real-linear map induces the exact source topology rather than a disconnected topology. -/
theorem exact_inducing_topology (arity : PositiveArity) :
    Topology.IsInducing (toSchwartzRealLinearMap arity) :=
  inducing_toSchwartzRealLinearMap arity

/-- Installing the named structure supplies convex neighborhoods at zero. -/
theorem exact_convex_zero_neighborhood (arity : PositiveArity)
    (U : Set (OSPositiveTimeOrderedFourDimensionalSourceSpace arity))
    (hU : U ∈ 𝓝 (0 : OSPositiveTimeOrderedFourDimensionalSourceSpace arity)) :
    ∃ S ∈ 𝓝 (0 : OSPositiveTimeOrderedFourDimensionalSourceSpace arity),
      Convex ℝ S ∧ S ⊆ U := by
  letI : LocallyConvexSpace ℝ
      (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
    locallyConvexSpace arity
  have hb := (locallyConvexSpace_iff_zero ℝ
    (OSPositiveTimeOrderedFourDimensionalSourceSpace arity)).mp inferInstance
  rcases hb.mem_iff.mp hU with ⟨S, hS, hsub⟩
  exact ⟨S, hS.1, hS.2, hsub⟩

/-- Local-convexity transport does not collapse the explicit nonzero source test. -/
theorem nonzero_source_test_retained :
    toSchwartzRealLinearMap PositiveArity.one
      OSPositiveTimeOrderedFourDimensionalSourceSpace.positiveTimeBump ≠ 0 := by
  simpa only [toSchwartzRealLinearMap_apply] using
    OSPositiveTimeOrderedFourDimensionalSourceSpace.positiveTimeBump_toSchwartz_ne_zero

end

end YangMills.OSOrderedFourDimensionalSourceSpaceLocallyConvex.Probes
