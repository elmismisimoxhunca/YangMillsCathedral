/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalSourceSpace
import YangMills.Euclidean.SchwingerTestSequence

/-!
# Finite sequences over the exact four-dimensional OS-I source spaces

OS-I printed pp. 86–88 separates the scalar component `f₀ ∈ ℂ` from positive-arity components
`fₙ ∈ 𝒮₊(ℝ^(4n))`, `n ≥ 1`, and requires only finitely many nonzero components. This module
packages exactly that algebraic carrier using the positive-arity source spaces constructed from the
paper's `D^α` condition. Its support finset is definitionally connected to nonvanishing of the
actual underlying Schwartz component.

The earlier strict topological-support sequence maps componentwise into this carrier without
changing the scalar, support, or Schwartz functions; no properness claim is made. This module installs no direct-sum topology, product, involution,
reflection-positive form, `(E2)`, OS-II growth, or reconstruction.
-/

namespace YangMills

noncomputable section

/-- Algebraic finite sequence with a separate scalar zero-point component and exact positive-arity
OS-I source-space components. -/
structure OSPositiveTimeOrderedFourDimensionalTestSequence where
  /-- The separate source scalar `f₀`. -/
  zeroPoint : ℂ
  /-- Exact finite set of nonzero positive arities. -/
  support : Finset PositiveArity
  /-- Exact OS-I ordered source test at every positive arity. -/
  component : ∀ arity : PositiveArity,
    OSPositiveTimeOrderedFourDimensionalSourceSpace arity
  /-- Support membership is tied to the same underlying Schwartz component. -/
  mem_support_iff : ∀ arity,
    arity ∈ support ↔ (component arity).toSchwartz ≠ 0

namespace OSPositiveTimeOrderedFourDimensionalTestSequence

/-- Every positive component outside exact support is the zero ambient Schwartz function. -/
theorem component_toSchwartz_eq_zero_of_not_mem
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence)
    (arity : PositiveArity) (h : arity ∉ f.support) :
    (f.component arity).toSchwartz = 0 := by
  by_contra hne
  exact h ((f.mem_support_iff arity).2 hne)

/-- Every nonzero positive component belongs to exact support. -/
theorem mem_support_of_component_toSchwartz_ne_zero
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence)
    (arity : PositiveArity) (hne : (f.component arity).toSchwartz ≠ 0) :
    arity ∈ f.support :=
  (f.mem_support_iff arity).2 hne

end OSPositiveTimeOrderedFourDimensionalTestSequence

/-- Zero element of every exact positive-arity source space. -/
def zeroOSPositiveTimeOrderedFourDimensionalSourceTest (arity : PositiveArity) :
    OSPositiveTimeOrderedFourDimensionalSourceSpace arity := by
  refine ⟨0, ?_⟩
  exact (osPositiveTimeOrderedFourDimensionalSourceTest_iff_frechet arity 0).mpr
    ((osPositiveTimeOrderedDerivativeSubmodule
      EuclideanDimension.four arity.value).zero_mem)

/-- Algebraic source sequence with scalar and every positive component zero. -/
def zeroOSPositiveTimeOrderedFourDimensionalTestSequence :
    OSPositiveTimeOrderedFourDimensionalTestSequence where
  zeroPoint := 0
  support := ∅
  component := zeroOSPositiveTimeOrderedFourDimensionalSourceTest
  mem_support_iff := by
    intro arity
    simp [zeroOSPositiveTimeOrderedFourDimensionalSourceTest,
      OSPositiveTimeOrderedFourDimensionalSourceSpace.toSchwartz]

/-- Exact componentwise map from the earlier strict topological-support sequence into the source
sequence carrier. This does not assert proper inclusion. -/
def MathlibStrictPositiveTimeTestSequence.toFourDimensionalOSSourceSequence
    (f : MathlibStrictPositiveTimeTestSequence EuclideanDimension.four) :
    OSPositiveTimeOrderedFourDimensionalTestSequence where
  zeroPoint := f.zeroPoint
  support := f.support
  component := fun arity => by
    let strict : MathlibPositiveTimeOrderedFlatTestFunction
        EuclideanDimension.four arity.value :=
      ⟨f.component arity, f.component_ordered arity, f.component_flat arity⟩
    let candidate := OSPositiveTimeOrderedDerivativeCarrier.ofStrictOrderedFlat strict
    exact ⟨candidate.toSchwartz,
      (osPositiveTimeOrderedFourDimensionalSourceTest_iff_frechet arity
        candidate.toSchwartz).mpr candidate.2⟩
  mem_support_iff := by
    intro arity
    change arity ∈ f.support ↔ f.component arity ≠ 0
    exact f.mem_support_iff arity

/-- The strict-carrier map preserves the separate scalar component exactly. -/
@[simp]
theorem MathlibStrictPositiveTimeTestSequence.toFourDimensionalOSSourceSequence_zeroPoint
    (f : MathlibStrictPositiveTimeTestSequence EuclideanDimension.four) :
    f.toFourDimensionalOSSourceSequence.zeroPoint = f.zeroPoint :=
  rfl

/-- The strict-carrier map preserves exact positive support. -/
@[simp]
theorem MathlibStrictPositiveTimeTestSequence.toFourDimensionalOSSourceSequence_support
    (f : MathlibStrictPositiveTimeTestSequence EuclideanDimension.four) :
    f.toFourDimensionalOSSourceSequence.support = f.support :=
  rfl

/-- The strict-carrier map preserves every underlying positive-arity Schwartz component exactly. -/
@[simp]
theorem MathlibStrictPositiveTimeTestSequence.toFourDimensionalOSSourceSequence_component
    (f : MathlibStrictPositiveTimeTestSequence EuclideanDimension.four)
    (arity : PositiveArity) :
    (f.toFourDimensionalOSSourceSequence.component arity).toSchwartz =
      f.component arity :=
  rfl

/-- Source sequence with scalar component one and every positive component zero. -/
def unitZeroPointFourDimensionalOSSourceSequence :
    OSPositiveTimeOrderedFourDimensionalTestSequence where
  zeroPoint := 1
  support := ∅
  component := zeroOSPositiveTimeOrderedFourDimensionalSourceTest
  mem_support_iff := by
    intro arity
    simp [zeroOSPositiveTimeOrderedFourDimensionalSourceTest,
      OSPositiveTimeOrderedFourDimensionalSourceSpace.toSchwartz]

/-- Source sequence whose sole nonzero positive component is the explicit arity-one bump. -/
def singletonPositiveTimeBumpFourDimensionalOSSourceSequence :
    OSPositiveTimeOrderedFourDimensionalTestSequence :=
  (singletonPositiveTimeBumpSequence
    EuclideanDimension.four).toFourDimensionalOSSourceSequence

end

end YangMills
