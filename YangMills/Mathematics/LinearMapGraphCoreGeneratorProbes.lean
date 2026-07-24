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

universe uK uD uX uI

variable {𝕜 : Type uK} [NormedField 𝕜]
  {D : Type uD} [AddCommGroup D] [Module 𝕜 D]
  {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {ι : Type uI} {l : Filter ι}
  (A : X →ₗ[𝕜] X) (Q : ι → X →ₗ[𝕜] X) (core : Set X)
  (C : ℝ) (hC : 0 ≤ C)
  (graphBound : ∀ᶠ i in l, ∀ z : X, ‖Q i z‖ ≤ C * (‖z‖ + ‖A z‖))
  (coreGenerator : ∀ z ∈ core, Tendsto (fun i => Q i z) l (nhds (A z)))

/-- Positive probe: convergence gives a pointwise eventual norm bound, without asserting a
bound uniform over a family of vectors. -/
theorem exact_eventually_normBound_of_tendsto
    {f : ι → X} {y : X} (hf : Tendsto f l (nhds y)) :
    ∀ᶠ i in l, ‖f i‖ ≤ ‖y‖ + 1 :=
  eventually_norm_le_norm_add_one_of_tendsto hf

/-- Exact quantifier-order probe: convergence at one domain vector gives one vector-dependent
nonnegative graph-bound constant. -/
theorem exact_exists_eventually_pointwise_graphBound_of_tendsto
    (J AOnDomain : D →ₗ[𝕜] X) (z : D)
    (hz : Tendsto (fun i => Q i (J z)) l (nhds (AOnDomain z))) :
    ∃ Cz : ℝ, 0 ≤ Cz ∧ ∀ᶠ i in l,
      ‖Q i (J z)‖ ≤ Cz * (‖J z‖ + ‖AOnDomain z‖) :=
  exists_eventually_pointwise_graphBound_of_tendsto J AOnDomain Q z hz

/-- Positive probe: graph approximation on a proper algebraic domain supplies the ambient
operator limit. -/
theorem exact_domainGraphCore_generator_extension
    (J AOnDomain : D →ₗ[𝕜] X) (domainCore : Set D)
    (hC : 0 ≤ C)
    (graphBound : ∀ᶠ i in l, ∀ z : D,
      ‖Q i (J z)‖ ≤ C * (‖J z‖ + ‖AOnDomain z‖))
    (coreGenerator : ∀ z ∈ domainCore,
      Tendsto (fun i => Q i (J z)) l (nhds (AOnDomain z)))
    {x : D} (graphApprox :
      IsLinearMapDomainGraphDenseAt J AOnDomain domainCore x) :
    Tendsto (fun i => Q i (J x)) l (nhds (AOnDomain x)) :=
  tendsto_linearMapOnDomain_of_graphDenseAt_of_eventually_graphBound
    J AOnDomain Q domainCore C hC graphBound coreGenerator graphApprox

/-- Positive probe: a global graph core on a proper algebraic domain gives convergence everywhere
on that domain. -/
theorem exact_globalDomainGraphCore_generator_extension
    (J AOnDomain : D →ₗ[𝕜] X) (domainCore : Set D)
    (hC : 0 ≤ C)
    (graphDense : IsLinearMapDomainGraphDenseCore J AOnDomain domainCore)
    (graphBound : ∀ᶠ i in l, ∀ z : D,
      ‖Q i (J z)‖ ≤ C * (‖J z‖ + ‖AOnDomain z‖))
    (coreGenerator : ∀ z ∈ domainCore,
      Tendsto (fun i => Q i (J z)) l (nhds (AOnDomain z))) :
    ∀ x, Tendsto (fun i => Q i (J x)) l (nhds (AOnDomain x)) :=
  tendsto_linearMapOnDomain_of_graphDenseCore_of_eventually_graphBound
    J AOnDomain Q domainCore C hC graphDense graphBound coreGenerator

/-- Hostile proper-domain probe: exact hypotheses reject a changed ambient generator target. -/
theorem changed_domainGraphCore_generator_target_blocked
    [NeBot l] (J AOnDomain : D →ₗ[𝕜] X) (domainCore : Set D)
    (hC : 0 ≤ C)
    (graphBound : ∀ᶠ i in l, ∀ z : D,
      ‖Q i (J z)‖ ≤ C * (‖J z‖ + ‖AOnDomain z‖))
    (coreGenerator : ∀ z ∈ domainCore,
      Tendsto (fun i => Q i (J z)) l (nhds (AOnDomain z)))
    {x : D} (graphApprox : IsLinearMapDomainGraphDenseAt J AOnDomain domainCore x)
    (changed : X) (changed_ne_exact : changed ≠ AOnDomain x)
    (claimed : Tendsto (fun i => Q i (J x)) l (nhds changed)) : False :=
  changed_ne_exact (tendsto_nhds_unique claimed
    (tendsto_linearMapOnDomain_of_graphDenseAt_of_eventually_graphBound
      J AOnDomain Q domainCore C hC graphBound coreGenerator graphApprox))

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
