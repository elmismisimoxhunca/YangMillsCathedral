/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedDerivativeClosed

/-!
# Hostile probes for closedness of the OS ordered Fréchet candidate

These probes lock closedness to the exact ambient Schwartz topology and exact derivative-vanishing
carrier. In particular, an ambient limit of accepted tests cannot escape through an unrelated
closed set or a disconnected topology.
-/

namespace YangMills.OSOrderedDerivativeClosed.Probes

open Filter Set

noncomputable section

/-- Closedness is asserted for exactly the named derivative-vanishing complex submodule. -/
theorem exact_closed_carrier (d : EuclideanDimension) (n : ℕ) :
    IsClosed ((osPositiveTimeOrderedDerivativeSubmodule d n :
      Submodule ℂ (ScalarSchwartzTestFunction d n)) :
        Set (ScalarSchwartzTestFunction d n)) :=
  isClosed_osPositiveTimeOrderedDerivativeSubmodule d n

/-- Every ambient Schwartz limit of eventually accepted tests retains the exact all-order
vanishing law. -/
theorem ambient_limit_retains_derivative_vanishing
    {d : EuclideanDimension} {n : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    (tests : ι → OSPositiveTimeOrderedDerivativeCarrier d n)
    (limit : ScalarSchwartzTestFunction d n)
    (converges : Tendsto (fun i => tests i |>.toSchwartz) l (nhds limit)) :
    IsOSPositiveTimeOrderedDerivativeVanishing limit := by
  exact (isClosed_osPositiveTimeOrderedDerivativeSubmodule d n).mem_of_tendsto
    converges (Filter.Eventually.of_forall fun i => (tests i).2)

/-- A function with one nonzero exterior jet cannot arise as an ambient limit of eventually
accepted tests. -/
theorem nonvanishing_exterior_jet_blocks_limit
    {d : EuclideanDimension} {n : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    (tests : ι → OSPositiveTimeOrderedDerivativeCarrier d n)
    (limit : ScalarSchwartzTestFunction d n)
    (k : ℕ) (x : EuclideanNPointSpace d n)
    (hx : x ∉ strictPositiveTimeOrderedConfigurationSet d n)
    (hne : iteratedFDeriv ℝ k
      (limit : EuclideanNPointSpace d n → ℂ) x ≠ 0) :
    ¬ Tendsto (fun i => tests i |>.toSchwartz) l (nhds limit) := by
  intro converges
  exact hne ((ambient_limit_retains_derivative_vanishing tests limit converges) k x hx)

/-- The closed embedding retains the exact underlying Schwartz function and induced topology. -/
theorem exact_closed_embedding (d : EuclideanDimension) (n : ℕ) :
    Topology.IsClosedEmbedding
      (OSPositiveTimeOrderedDerivativeCarrier.toSchwartz :
        OSPositiveTimeOrderedDerivativeCarrier d n → ScalarSchwartzTestFunction d n) :=
  OSPositiveTimeOrderedDerivativeCarrier.closedEmbedding_toSchwartz d n

end

end YangMills.OSOrderedDerivativeClosed.Probes
