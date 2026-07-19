/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Topology.Algebra.Module.LocallyConvex
import YangMills.Euclidean.OSOrderedFourDimensionalSourceSpaceTopologicalAlgebra

/-!
# Local convexity of exact positive-arity OS source spaces

The exact source topology is induced from real locally convex Schwartz space, and the transported
complex algebra restricts canonically to a real module. This module packages the forgetful map as a
real linear map and transports local convexity through its inducing topology.

The result is per positive arity. It does not establish local convexity of finite source sequences,
identify their final topology with OS-I's locally convex direct sum, construct a completion or
completed tensor product, state `(E2)`, or perform reconstruction.
-/

namespace YangMills

noncomputable section

namespace OSPositiveTimeOrderedFourDimensionalSourceSpace

noncomputable local instance addCommGroupForLocallyConvex (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  addCommGroup arity

noncomputable local instance moduleForLocallyConvex (arity : PositiveArity) :
    Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  module arity

/-- The exact forgetful map is real-linear for the canonical real restriction of the transported
complex module. -/
def toSchwartzRealLinearMap (arity : PositiveArity) :
    OSPositiveTimeOrderedFourDimensionalSourceSpace arity →ₗ[ℝ]
      ScalarSchwartzTestFunction EuclideanDimension.four arity.value where
  toFun := toSchwartz
  map_add' f g := instance_add_toSchwartz arity f g
  map_smul' c f := instance_smul_toSchwartz arity (c : ℂ) f

/-- Real-linear packaging preserves the exact underlying Schwartz function. -/
@[simp]
theorem toSchwartzRealLinearMap_apply (arity : PositiveArity)
    (f : OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :
    toSchwartzRealLinearMap arity f = f.toSchwartz :=
  rfl

/-- The real-linear forgetful map induces exactly the source-space topology. -/
theorem inducing_toSchwartzRealLinearMap (arity : PositiveArity) :
    Topology.IsInducing (toSchwartzRealLinearMap arity) :=
  (closedEmbedding_toSchwartz arity).isInducing

/-- Named real local-convexity structure on each exact positive-arity source space. -/
@[reducible]
noncomputable def locallyConvexSpace (arity : PositiveArity) :
    LocallyConvexSpace ℝ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  Topology.IsInducing.locallyConvexSpace
    (f := toSchwartzRealLinearMap arity)
    (inducing_toSchwartzRealLinearMap arity)

end OSPositiveTimeOrderedFourDimensionalSourceSpace

end

end YangMills
