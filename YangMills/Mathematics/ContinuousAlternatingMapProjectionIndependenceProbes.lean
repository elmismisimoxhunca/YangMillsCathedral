/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ContinuousAlternatingMapProjectionIndependence

/-!
# Hostile probes for projection independence
-/

namespace YangMills.Mathematics.ContinuousAlternatingMapProjectionIndependence.Probes

universe uR uE uF uV

variable
    {R : Type uR} [Ring R]
    {E : Type uE} [AddCommGroup E] [Module R E] [TopologicalSpace E]
    {F : Type uF} [AddCommGroup F] [Module R F]
    {V : Type uV} [AddCommGroup V] [Module R V] [TopologicalSpace V]

/-- Arbitrary-degree tuples with identical projections have identical horizontal-form values. -/
theorem exact_projection_independence
    {k : ℕ} (form : ContinuousAlternatingMap R E V (Fin k))
    (projection : E →ₗ[R] F)
    (horizontal : ∀ v : Fin k → E, (∃ i, projection (v i) = 0) → form v = 0)
    (first second : Fin k → E)
    (sameProjection : ∀ i, projection (first i) = projection (second i)) :
    form first = form second :=
  form.eq_of_linearMap_apply_eq projection horizontal first second sameProjection

/-- Arity zero is covered without assuming an argument exists. -/
theorem exact_zero_arity_projection_independence
    (form : ContinuousAlternatingMap R E V (Fin 0))
    (projection : E →ₗ[R] F)
    (horizontal : ∀ v : Fin 0 → E, (∃ i, projection (v i) = 0) → form v = 0)
    (first second : Fin 0 → E) :
    form first = form second :=
  form.eq_of_linearMap_apply_eq projection horizontal first second (fun i => Fin.elim0 i)

/-- One-slot replacement with vertical difference is preserved exactly. -/
theorem exact_vertical_replacement
    {k : ℕ} (form : ContinuousAlternatingMap R E V (Fin k))
    (projection : E →ₗ[R] F)
    (horizontal : ∀ v : Fin k → E, (∃ i, projection (v i) = 0) → form v = 0)
    (args : Fin k → E) (i : Fin k) (replacement : E)
    (vertical : projection (args i - replacement) = 0) :
    form args = form (Function.update args i replacement) :=
  form.eq_update_of_sub_mem_ker projection horizontal args i replacement vertical

/-- A changed value on equal-projection tuples contradicts horizontality. -/
theorem mismatched_projection_value_blocked
    {k : ℕ} (form : ContinuousAlternatingMap R E V (Fin k))
    (projection : E →ₗ[R] F)
    (horizontal : ∀ v : Fin k → E, (∃ i, projection (v i) = 0) → form v = 0)
    (first second : Fin k → E)
    (sameProjection : ∀ i, projection (first i) = projection (second i))
    (wrong : form first ≠ form second) : False :=
  wrong (form.eq_of_linearMap_apply_eq projection horizontal first second sameProjection)

end YangMills.Mathematics.ContinuousAlternatingMapProjectionIndependence.Probes
