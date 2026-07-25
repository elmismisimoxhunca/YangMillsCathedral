/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.LinearAlgebra.Alternating.Curry

/-!
# Degree-two alternating maps as bilinear maps

This module gives exact linear adapters from alternating maps indexed by `Fin 2` to curried
bilinear maps. The construction curries twice and evaluates the remaining zero-argument alternating
map. A corresponding adapter for continuous alternating maps forgets only the continuity packaging;
its pointwise values are unchanged.
-/

namespace YangMills.Mathematics

universe uR uE uV

noncomputable section

variable
    {R : Type uR} [CommSemiring R]
    {E : Type uE} [AddCommMonoid E] [Module R E]
    {V : Type uV} [AddCommMonoid V] [Module R V]

/-- Evaluate a zero-argument alternating map on the unique empty vector family. -/
def alternatingMapFinZeroEval : (E [⋀^Fin 0]→ₗ[R] V) →ₗ[R] V where
  toFun form := form ![]
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

/-- A one-argument alternating map is canonically a linear map. -/
def alternatingMapFinOneToLinear :
    (E [⋀^Fin 1]→ₗ[R] V) →ₗ[R] E →ₗ[R] V :=
  (LinearMap.compRight R
    (alternatingMapFinZeroEval (R := R) (E := E) (V := V))).comp
      AlternatingMap.curryLeftLinearMap

/-- A two-argument alternating map is canonically a curried bilinear map. -/
def alternatingMapFinTwoToBilinear :
    (E [⋀^Fin 2]→ₗ[R] V) →ₗ[R] E →ₗ[R] E →ₗ[R] V :=
  (LinearMap.compRight R
    (alternatingMapFinOneToLinear (R := R) (E := E) (V := V))).comp
      AlternatingMap.curryLeftLinearMap

/-- Bilinear packaging preserves exact evaluation of an algebraic degree-two alternating map. -/
@[simp]
theorem alternatingMapFinTwoToBilinear_apply
    (form : E [⋀^Fin 2]→ₗ[R] V) (first second : E) :
    alternatingMapFinTwoToBilinear form first second = form ![first, second] := by
  rfl

variable [TopologicalSpace E] [TopologicalSpace V]

/-- Forget continuity from a degree-two continuous alternating map while packaging its exact values
as a bilinear map. -/
def continuousAlternatingMapFinTwoToBilinear
    (form : E [⋀^Fin 2]→L[R] V) : E →ₗ[R] E →ₗ[R] V :=
  alternatingMapFinTwoToBilinear form.toAlternatingMap

/-- Bilinear packaging preserves exact evaluation of a continuous degree-two alternating map. -/
@[simp]
theorem continuousAlternatingMapFinTwoToBilinear_apply
    (form : E [⋀^Fin 2]→L[R] V) (first second : E) :
    continuousAlternatingMapFinTwoToBilinear form first second = form ![first, second] := by
  rfl

end

end YangMills.Mathematics
