/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivativeExtChart
import YangMills.Mathematics.ManifoldOneFormExteriorDerivativeSmoothMapCoordinates
import YangMills.Mathematics.ManifoldOneFormPositiveDegreeExteriorDerivativeBridge

namespace YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivativeExtChart.Probes

open Set
open scoped Manifold ContDiff Topology
open YangMills.Mathematics

universe uE uH uM uV uW

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable section

/-- The certificate exposes the exact arbitrary-degree centered equality. -/
theorem exact_positive_degree_centered_extDeriv
    (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates n form)
    (p : M) :
    certificate.derivative.toForm.inExtChartAt coordinates (n + 2) p ((extChartAt I p) p) =
      extDerivWithin (form.toForm.inExtChartAt coordinates (n + 1) p)
        (extChartAt I p).target ((extChartAt I p) p) :=
  certificate.inExtChartAt_derivative_eq_extDerivWithin coordinates n form p

/-- At `n = 0`, the older one-form route proves the identical centered statement. -/
theorem n_zero_centered_coherence
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates 0 form)
    (p : M) :
    certificate.derivative.toForm.inExtChartAt coordinates 2 p ((extChartAt I p) p) =
      extDerivWithin (form.toForm.inExtChartAt coordinates 1 p)
        (extChartAt I p).target ((extChartAt I p) p) := by
  simpa using certificate.toOneForm.inExtChartAt_derivative_eq_extDerivWithin coordinates form p

/-- The arbitrary-degree and specialized one-form proof terms are propositionally coherent. -/
theorem n_zero_proof_coherence
    (coordinates : V ≃L[ℝ] W)
    (form : SmoothManifoldDifferentialForm I M V coordinates 1)
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates 0 form)
    (p : M) :
    certificate.inExtChartAt_derivative_eq_extDerivWithin coordinates 0 form p =
      certificate.toOneForm.inExtChartAt_derivative_eq_extDerivWithin coordinates form p :=
  Subsingleton.elim _ _

/-- A changed centered derivative is rejected for every degree. -/
theorem changed_positive_degree_centered_derivative_blocked
    (coordinates : V ≃L[ℝ] W) (n : ℕ)
    (form : SmoothManifoldDifferentialForm I M V coordinates (n + 1))
    (certificate : SmoothManifoldPositiveDegreeExteriorDerivativeCertificate coordinates n form)
    (p : M)
    (wrong : certificate.derivative.toForm.inExtChartAt coordinates (n + 2) p
        ((extChartAt I p) p) ≠
      extDerivWithin (form.toForm.inExtChartAt coordinates (n + 1) p)
        (extChartAt I p).target ((extChartAt I p) p)) : False :=
  wrong (certificate.inExtChartAt_derivative_eq_extDerivWithin coordinates n form p)

end

end YangMills.Mathematics.ManifoldPositiveDegreeExteriorDerivativeExtChart.Probes
