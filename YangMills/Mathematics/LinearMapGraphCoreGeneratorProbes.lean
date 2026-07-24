/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.LinearMapGraphCoreGenerator

namespace YangMills
namespace Mathematics

open Filter

noncomputable section

universe uK uX uI

variable {𝕜 : Type uK} [NormedField 𝕜]
  {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {ι : Type uI} {l : Filter ι}
  (A : X →ₗ[𝕜] X) (Q : ι → X →ₗ[𝕜] X) (core : Set X)
  (C : ℝ) (hC : 0 ≤ C)
  (graphBound : ∀ᶠ i in l, ∀ z : X, ‖Q i z‖ ≤ C * (‖z‖ + ‖A z‖))
  (coreGenerator : ∀ z ∈ core, Tendsto (fun i => Q i z) l (nhds (A z)))

/-- Positive probe: pointwise graph approximation supplies the full generator limit. -/
theorem exact_graphCore_generator_extension
    (hC : 0 ≤ C)
    (graphBound : ∀ᶠ i in l, ∀ z : X, ‖Q i z‖ ≤ C * (‖z‖ + ‖A z‖))
    (coreGenerator : ∀ z ∈ core, Tendsto (fun i => Q i z) l (nhds (A z)))
    {x : X} (graphApprox : IsLinearMapGraphDenseAt A core x) :
    Tendsto (fun i => Q i x) l (nhds (A x)) :=
  tendsto_linearMap_of_graphDenseAt_of_eventually_graphBound A Q core C hC graphBound
    coreGenerator graphApprox

/-- Positive probe: a global graph core supplies generator convergence everywhere. -/
theorem exact_globalGraphCore_generator_extension
    (hC : 0 ≤ C)
    (graphBound : ∀ᶠ i in l, ∀ z : X, ‖Q i z‖ ≤ C * (‖z‖ + ‖A z‖))
    (coreGenerator : ∀ z ∈ core, Tendsto (fun i => Q i z) l (nhds (A z)))
    (graphDense : IsLinearMapGraphDenseCore A core) :
    ∀ x, Tendsto (fun i => Q i x) l (nhds (A x)) :=
  tendsto_linearMap_of_graphDenseCore_of_eventually_graphBound A Q core C hC graphDense graphBound
    coreGenerator

/-- Hostile probe: under the exact graph-core hypotheses, the same approximants cannot converge to
a changed generator target. -/
theorem changed_graphCore_generator_target_blocked
    [NeBot l] (hC : 0 ≤ C)
    (graphBound : ∀ᶠ i in l, ∀ z : X, ‖Q i z‖ ≤ C * (‖z‖ + ‖A z‖))
    (coreGenerator : ∀ z ∈ core, Tendsto (fun i => Q i z) l (nhds (A z)))
    {x : X} (graphApprox : IsLinearMapGraphDenseAt A core x) (changed : X)
    (changed_ne_exact : changed ≠ A x)
    (claimed : Tendsto (fun i => Q i x) l (nhds changed)) : False :=
  changed_ne_exact (tendsto_nhds_unique claimed
    (tendsto_linearMap_of_graphDenseAt_of_eventually_graphBound A Q core C hC graphBound
      coreGenerator graphApprox))

end

end Mathematics
end YangMills
