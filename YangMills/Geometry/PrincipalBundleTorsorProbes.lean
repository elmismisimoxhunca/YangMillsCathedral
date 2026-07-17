/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalBundleTorsor

/-!
# Hostile probes for the principal-bundle torsor core

These checks isolate surjectivity/nonempty fibers, verticality, the action laws, freeness, and
fiberwise transitivity. They do not pretend to test smooth local triviality, which belongs to a
later interface.
-/

namespace YangMills.Geometry.Probes

universe uG uB uP

variable {G : Type uG} {B : Type uB} {P : Type uP} [Group G]

/-- A nonempty base cannot be paired with an empty total carrier. -/
theorem empty_totalCarrier_blocked
    (nonemptyBase : Nonempty B) (emptyTotal : P → False)
    (data : PrincipalBundleTorsorData G B P) : False := by
  obtain ⟨b⟩ := nonemptyBase
  obtain ⟨p, _⟩ := data.fiber_nonempty b
  exact emptyTotal p

/-- A candidate projection that misses a base point cannot be a torsor family. -/
theorem nonsurjective_projection_blocked
    (data : PrincipalBundleTorsorData G B P) (b : B)
    (missing : ∀ p, data.projection p ≠ b) : False := by
  obtain ⟨p, projected⟩ := data.fiber_nonempty b
  exact missing p projected

/-- The group action cannot move a point to another base fiber. -/
theorem base_moving_rightAction_blocked
    (data : PrincipalBundleTorsorData G B P) (p : P) (g : G)
    (movesBase : data.projection (data.rightAction p g) ≠ data.projection p) : False :=
  movesBase (data.projection_rightAction p g)

/-- A mutation of the right identity law is rejected independently. -/
theorem broken_right_identity_blocked
    (data : PrincipalBundleTorsorData G B P) (p : P)
    (broken : data.rightAction p 1 ≠ p) : False :=
  broken (data.right_one p)

/-- A mutation of right-action associativity is rejected independently. -/
theorem broken_right_multiplication_blocked
    (data : PrincipalBundleTorsorData G B P) (p : P) (g h : G)
    (broken : data.rightAction (data.rightAction p g) h ≠
      data.rightAction p (g * h)) : False :=
  broken (data.right_mul p g h)

/-- A nonidentity stabilizer contradicts freeness. -/
theorem nonfree_rightAction_blocked
    (data : PrincipalBundleTorsorData G B P) (p : P) (g : G)
    (nonidentity : g ≠ 1) (fixed : data.rightAction p g = p) : False :=
  data.rightAction_ne_of_ne_one p nonidentity fixed

/-- Two points in one fiber cannot lie in distinct action orbits. -/
theorem nontransitive_fiber_blocked
    (data : PrincipalBundleTorsorData G B P) (p q : P)
    (sameFiber : data.projection p = data.projection q)
    (differentOrbits : ∀ g, data.rightAction p g ≠ q) : False := by
  obtain ⟨g, reaches⟩ := data.sameFiber_transitive sameFiber
  exact differentOrbits g reaches

/-- In the trivial torsor, `g⁻¹h` is the expected unique element carrying `(b,g)` to `(b,h)`. -/
theorem trivial_torsor_solving_element (b : B) (g h : G) :
    (PrincipalBundleTorsorData.trivial G B).rightAction (b, g) (g⁻¹ * h) = (b, h) := by
  simp [PrincipalBundleTorsorData.trivial]

end YangMills.Geometry.Probes
