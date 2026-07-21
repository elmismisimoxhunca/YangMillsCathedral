/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SmoothManifoldDifferentialFormOutputLinear

namespace YangMills.Mathematics.SmoothManifoldDifferentialFormOutputLinear.Probes

open scoped Manifold ContDiff

universe uE uH uM uV uW
noncomputable section

variable {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Output postcomposition evaluates by the exact designated linear map. -/
theorem exact_output_postcomposition
    (coordinates : V ≃L[ℝ] W) (L : V →L[ℝ] V) (k : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates k)
    (x : M) (v : Fin k → TangentSpace I x) :
    (form.postcompContinuousLinearMap coordinates L k).toForm x v = L (form.toForm x v) := rfl

/-- The transported exterior certificate has exactly the postcomposed derivative carrier. -/
theorem exact_postcomposed_derivative
    (coordinates : V ≃L[ℝ] W) (L : V →L[ℝ] V) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates n form)
    (x : M) (v : Fin (n + 2) → TangentSpace I x) :
    (certificate.postcompContinuousLinearMap coordinates L n).derivative.toForm x v =
      L (certificate.derivative.toForm x v) := rfl

/-- A disconnected derivative output cannot replace exact linear postcomposition. -/
theorem changed_postcomposed_derivative_blocked
    (coordinates : V ≃L[ℝ] W) (L : V →L[ℝ] V) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates n form)
    (x : M) (v : Fin (n + 2) → TangentSpace I x)
    (changed : (certificate.postcompContinuousLinearMap coordinates L n).derivative.toForm x v ≠
      L (certificate.derivative.toForm x v)) : False := changed rfl

end

end YangMills.Mathematics.SmoothManifoldDifferentialFormOutputLinear.Probes
