/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalTestSequence

/-!
# Hostile probes for exact four-dimensional OS-I source sequences

These probes lock the separate scalar component, exact positive support, exact source-space
components, the strict-carrier componentwise map and nonzero content. They install no topology or `(E2)`.
-/

namespace YangMills.OSOrderedFourDimensionalTestSequence.Probes

noncomputable section

/-- Constructor surface requires an actual scalar, exact finite support, source-space components and
support equality; no natural-arity-zero source component is accepted. -/
def exact_constructor_surface
    (zeroPoint : ℂ) (support : Finset PositiveArity)
    (component : ∀ arity : PositiveArity,
      OSPositiveTimeOrderedFourDimensionalSourceSpace arity)
    (support_exact : ∀ arity,
      arity ∈ support ↔ (component arity).toSchwartz ≠ 0) :
    OSPositiveTimeOrderedFourDimensionalTestSequence :=
  ⟨zeroPoint, support, component, support_exact⟩

/-- A component omitted from exact positive support must be the zero ambient Schwartz function. -/
theorem omitted_component_blocked
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence)
    (arity : PositiveArity) (h : arity ∉ f.support) :
    (f.component arity).toSchwartz = 0 :=
  f.component_toSchwartz_eq_zero_of_not_mem arity h

/-- Every component carries the exact positive-arity OS-I source membership law. -/
theorem exact_component_source_membership
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence)
    (arity : PositiveArity) :
    IsOSPositiveTimeOrderedFourDimensionalSourceTest arity
      (f.component arity).toSchwartz :=
  (f.component arity).2

/-- The componentwise map from the strict-support carrier preserves scalar, support and every
underlying Schwartz component together; no properness claim is made. -/
theorem strictCarrier_componentwise_map_exact
    (f : MathlibStrictPositiveTimeTestSequence EuclideanDimension.four)
    (arity : PositiveArity) :
    f.toFourDimensionalOSSourceSequence.zeroPoint = f.zeroPoint ∧
      f.toFourDimensionalOSSourceSequence.support = f.support ∧
      (f.toFourDimensionalOSSourceSequence.component arity).toSchwartz =
        f.component arity :=
  ⟨rfl, rfl, rfl⟩

/-- The designated zero sequence has scalar zero, empty support and zero at every positive arity. -/
theorem zero_sequence_exact :
    zeroOSPositiveTimeOrderedFourDimensionalTestSequence.zeroPoint = 0 ∧
      zeroOSPositiveTimeOrderedFourDimensionalTestSequence.support = ∅ ∧
      ∀ arity : PositiveArity,
        (zeroOSPositiveTimeOrderedFourDimensionalTestSequence.component arity).toSchwartz = 0 := by
  refine ⟨rfl, rfl, ?_⟩
  intro arity
  exact zeroOSPositiveTimeOrderedFourDimensionalTestSequence.component_toSchwartz_eq_zero_of_not_mem
    arity (by
      change arity ∉ (∅ : Finset PositiveArity)
      simp)

/-- The scalar unit remains exactly scalar one while every positive component is absent. -/
theorem scalar_unit_is_separate :
    unitZeroPointFourDimensionalOSSourceSequence.zeroPoint = 1 ∧
      unitZeroPointFourDimensionalOSSourceSequence.support = ∅ ∧
      ∀ arity : PositiveArity,
        (unitZeroPointFourDimensionalOSSourceSequence.component arity).toSchwartz = 0 := by
  refine ⟨rfl, rfl, ?_⟩
  intro arity
  exact unitZeroPointFourDimensionalOSSourceSequence.component_toSchwartz_eq_zero_of_not_mem
    arity (by
      change arity ∉ (∅ : Finset PositiveArity)
      simp)

/-- The explicit singleton has exactly arity one in support. -/
theorem singleton_support_exact :
    singletonPositiveTimeBumpFourDimensionalOSSourceSequence.support =
      {PositiveArity.one} :=
  rfl

/-- The singleton's source component is exactly the original nonzero bump. -/
theorem singleton_component_exact :
    (singletonPositiveTimeBumpFourDimensionalOSSourceSequence.component
      PositiveArity.one).toSchwartz =
        positiveTimeBumpSchwartz EuclideanDimension.four := by
  rw [singletonPositiveTimeBumpFourDimensionalOSSourceSequence,
    MathlibStrictPositiveTimeTestSequence.toFourDimensionalOSSourceSequence_component,
    singletonPositiveTimeBumpSequence_component_one]

/-- The source sequence carrier is not reduced to scalar-only or zero-only data. -/
theorem singleton_component_nonzero :
    (singletonPositiveTimeBumpFourDimensionalOSSourceSequence.component
      PositiveArity.one).toSchwartz ≠ 0 := by
  rw [singleton_component_exact]
  exact positiveTimeBumpSchwartz_ne_zero EuclideanDimension.four

end

end YangMills.OSOrderedFourDimensionalTestSequence.Probes
