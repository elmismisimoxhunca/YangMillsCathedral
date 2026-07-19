/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedCoordinateJets
import YangMills.Mathematics.SchwartzDirectionalEvaluation

/-!
# Closedness of the OS ordered Fréchet candidate

Osterwalder–Schrader I, printed p. 86, calls its four-dimensional multi-index space
`𝒮_{s,t}(ℝ^{4n})` a closed subspace of Schwartz space. This module proves the corresponding
closedness theorem for the repository's still dimension-generic **Fréchet candidate**: the carrier
is the intersection of kernels of all continuous coordinate-directional jet evaluations outside
strict positive time order.

Downstream modules complete four-dimensional coordinate flattening, multiplicity and permutation
comparison, interpret OS-I's `D^α` at positive arity, and transport this theorem to the resulting
source spaces. This closedness layer itself supplies no reflection positivity, completion, OS-II
growth, reconstruction, theory inhabitant, or mass-gap claim.
-/

namespace YangMills

open Set

noncomputable section

/-- The dimension-generic ordered Fréchet candidate is a closed subset of the exact ambient
Schwartz topology. The proof uses the coordinate-jet equivalence and realizes every required jet
condition as the kernel of a continuous complex-linear functional. -/
theorem isClosed_osPositiveTimeOrderedDerivativeSubmodule
    (d : EuclideanDimension) (n : ℕ) :
    IsClosed ((osPositiveTimeOrderedDerivativeSubmodule d n :
      Submodule ℂ (ScalarSchwartzTestFunction d n)) :
        Set (ScalarSchwartzTestFunction d n)) := by
  let closedJets : Set (ScalarSchwartzTestFunction d n) :=
    ⋂ k : ℕ, ⋂ x : EuclideanNPointSpace d n,
      ⋂ (_hx : x ∉ strictPositiveTimeOrderedConfigurationSet d n),
        ⋂ directions : Fin k → ((_point : Fin n) × d.CoordinateIndex),
          (SchwartzMap.iteratedDirectionalEvaluationCLM
            (fun j => euclideanNPointCoordinateBasis d n (directions j)) x).ker
  have closed_closedJets : IsClosed closedJets := by
    apply isClosed_iInter
    intro k
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro hx
    apply isClosed_iInter
    intro directions
    exact SchwartzMap.isClosed_iteratedDirectionalEvaluationCLM_ker
      (fun j => euclideanNPointCoordinateBasis d n (directions j)) x
  have carrier_eq :
      ((osPositiveTimeOrderedDerivativeSubmodule d n :
        Submodule ℂ (ScalarSchwartzTestFunction d n)) :
          Set (ScalarSchwartzTestFunction d n)) = closedJets := by
    ext f
    change IsOSPositiveTimeOrderedDerivativeVanishing f ↔ f ∈ closedJets
    rw [osPositiveTimeOrderedFrechet_iff_coordinateJets]
    constructor
    · intro h
      simp only [closedJets, mem_iInter]
      intro k x hx directions
      change SchwartzMap.iteratedDirectionalEvaluationCLM
        (fun j => euclideanNPointCoordinateBasis d n (directions j)) x f = 0
      rw [SchwartzMap.iteratedDirectionalEvaluationCLM_apply]
      exact h k x hx directions
    · intro h k x hx directions
      have hk := Set.mem_iInter.mp h k
      have hx' := Set.mem_iInter.mp hk x
      have hhx := Set.mem_iInter.mp hx' hx
      have hm := Set.mem_iInter.mp hhx directions
      change SchwartzMap.iteratedDirectionalEvaluationCLM
        (fun j => euclideanNPointCoordinateBasis d n (directions j)) x f = 0 at hm
      simpa only [SchwartzMap.iteratedDirectionalEvaluationCLM_apply] using hm
  rw [carrier_eq]
  exact closed_closedJets

namespace OSPositiveTimeOrderedDerivativeCarrier

/-- With its already declared induced topology, the exact forgetful map from the candidate is a
closed topological embedding into ambient Schwartz space. -/
theorem closedEmbedding_toSchwartz (d : EuclideanDimension) (n : ℕ) :
    Topology.IsClosedEmbedding
      (toSchwartz : OSPositiveTimeOrderedDerivativeCarrier d n →
        ScalarSchwartzTestFunction d n) := by
  exact (isClosed_osPositiveTimeOrderedDerivativeSubmodule d n).isClosedEmbedding_subtypeVal

end OSPositiveTimeOrderedDerivativeCarrier

end

end YangMills
