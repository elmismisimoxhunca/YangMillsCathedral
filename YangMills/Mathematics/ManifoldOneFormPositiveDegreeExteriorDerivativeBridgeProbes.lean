/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldOneFormPositiveDegreeExteriorDerivativeBridge

/-!
# Hostile probes for one-form/positive-degree Cartan coherence

These probes lock the `n = 0` expression equality, both certificate conversions, and exact carrier
preservation through both round trips. They prevent the parallel certificate APIs from silently
using unrelated degree-two derivatives.
-/

namespace YangMills.Mathematics.ManifoldOneFormPositiveDegreeExteriorDerivativeBridge.Probes

open Set
open scoped Manifold ContDiff

universe uE uH uM uV uW

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]
    {coordinates : V ≃L[ℝ] W}

omit [IsManifold I ∞ M] in
/-- The positive-degree expression at `n = 0` is exactly the earlier one-form expression. -/
theorem exact_expression_bridge
    (form : ManifoldDifferentialForm I M V 1) (s : Set M) (x : M)
    (first second : (x : M) → TangentSpace I x) :
    form.positiveDegreeCartanExpressionCoordinates coordinates 0 s x
        (ManifoldDifferentialForm.twoTangentFieldFamily first second) =
      form.oneFormCartanExpressionCoordinates coordinates s x first second :=
  form.positiveDegreeCartanExpressionCoordinates_zero_eq_oneForm
    coordinates s x first second

variable {form : SmoothManifoldDifferentialForm I M V coordinates 1}

/-- Forward conversion keeps the exact specialized derivative carrier. -/
theorem exact_forward_derivative
    (certificate : SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form) :
    certificate.toPositiveDegreeZero.derivative = certificate.derivative :=
  rfl

/-- Reverse conversion keeps the exact positive-degree derivative carrier. -/
theorem exact_reverse_derivative
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates 0 form) :
    certificate.toOneForm.derivative = certificate.derivative :=
  rfl

/-- Converting a specialized certificate forward and back cannot change its derivative. -/
theorem exact_specialized_round_trip_derivative
    (certificate : SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form) :
    certificate.toPositiveDegreeZero.toOneForm.derivative = certificate.derivative :=
  rfl

/-- Converting a positive-degree-zero certificate back and forward cannot change its derivative. -/
theorem exact_positive_round_trip_derivative
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates 0 form) :
    certificate.toOneForm.toPositiveDegreeZero.derivative = certificate.derivative :=
  rfl

/-- A purported forward conversion with an unrelated derivative is rejected. -/
theorem unrelated_forward_derivative_blocked
    (certificate : SmoothManifoldOneFormExteriorDerivativeCertificate coordinates form)
    (other : SmoothManifoldDifferentialForm I M V coordinates 2)
    (hne : other ≠ certificate.derivative)
    (claimed : certificate.toPositiveDegreeZero.derivative = other) : False := by
  apply hne
  rw [← claimed]
  rfl

/-- A purported reverse conversion with an unrelated derivative is rejected. -/
theorem unrelated_reverse_derivative_blocked
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates 0 form)
    (other : SmoothManifoldDifferentialForm I M V coordinates 2)
    (hne : other ≠ certificate.derivative)
    (claimed : certificate.toOneForm.derivative = other) : False := by
  apply hne
  rw [← claimed]
  rfl

end YangMills.Mathematics.ManifoldOneFormPositiveDegreeExteriorDerivativeBridge.Probes
