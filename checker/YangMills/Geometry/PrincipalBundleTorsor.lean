/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Algebra.Group.Basic

/-!
# The fiberwise torsor core of a principal bundle

Freed describes each fiber of a principal bundle as a simply transitive right `G`-space. This
module isolates that algebraic core before topology, smooth local triviality, and bundle maps are
added. It is deliberately not named `PrincipalBundle`: inhabiting this structure alone does not
certify a topological or smooth principal bundle.
-/

namespace YangMills.Geometry

universe uG uB uP

/-- A surjective family of nonempty right `G`-torsors over `B`.

The action is stored rather than installed globally as a typeclass, so multiple bundle structures on
the same carrier cannot silently share or overwrite an action. `fiber_unique` packages freeness and
transitivity in the source-facing `∃!` form. -/
structure PrincipalBundleTorsorData
    (G : Type uG) (B : Type uB) (P : Type uP) [Group G] where
  /-- Projection from the total carrier to the base. -/
  projection : P → B
  /-- Right group action on the total carrier. -/
  rightAction : P → G → P
  /-- Right action by the identity. -/
  right_one : ∀ p, rightAction p 1 = p
  /-- Associativity in right-action order. -/
  right_mul : ∀ p g h, rightAction (rightAction p g) h = rightAction p (g * h)
  /-- The right action is vertical. -/
  projection_rightAction : ∀ p g, projection (rightAction p g) = projection p
  /-- Every base point has a nonempty fiber. -/
  fiber_nonempty : ∀ b, ∃ p, projection p = b
  /-- Two points are in the same fiber exactly up to a unique right group element. -/
  fiber_unique : ∀ p q, projection p = projection q → ∃! g, rightAction p g = q

namespace PrincipalBundleTorsorData

variable {G : Type uG} {B : Type uB} {P : Type uP} [Group G]

/-- The projection of a torsor family is surjective. -/
theorem projection_surjective (data : PrincipalBundleTorsorData G B P) :
    Function.Surjective data.projection :=
  data.fiber_nonempty

/-- The right action on every fiber is transitive. -/
theorem sameFiber_transitive (data : PrincipalBundleTorsorData G B P)
    {p q : P} (sameFiber : data.projection p = data.projection q) :
    ∃ g, data.rightAction p g = q :=
  (data.fiber_unique p q sameFiber).exists

/-- Equality in the base is exactly the relation of lying in one right-action orbit, with a unique
solving group element. This is the set-level quotient statement; no quotient topology is claimed. -/
theorem sameFiber_iff_existsUnique_rightAction
    (data : PrincipalBundleTorsorData G B P) (p q : P) :
    data.projection p = data.projection q ↔ ∃! g, data.rightAction p g = q := by
  constructor
  · exact data.fiber_unique p q
  · rintro ⟨g, action_eq, _⟩
    rw [← action_eq]
    exact data.projection_rightAction p g |>.symm

/-- The right action based at any total-space point is injective, hence free. -/
theorem rightAction_injective (data : PrincipalBundleTorsorData G B P) (p : P) :
    Function.Injective (data.rightAction p) := by
  intro g h actionsEqual
  have sameFiber : data.projection p = data.projection (data.rightAction p g) :=
    (data.projection_rightAction p g).symm
  obtain ⟨witness, _, unique⟩ := data.fiber_unique p (data.rightAction p g) sameFiber
  calc
    g = witness := unique g rfl
    _ = h := (unique h actionsEqual.symm).symm

/-- A nonidentity element cannot fix a point of a fiber. -/
theorem rightAction_ne_of_ne_one (data : PrincipalBundleTorsorData G B P)
    (p : P) {g : G} (nonidentity : g ≠ 1) : data.rightAction p g ≠ p := by
  intro fixed
  apply nonidentity
  apply data.rightAction_injective p
  calc
    data.rightAction p g = p := fixed
    _ = data.rightAction p 1 := (data.right_one p).symm

/-- The product projection `B × G → B` with multiplication in the second coordinate is the trivial
fiberwise torsor. This is positive consistency evidence for the algebraic interface only. -/
def trivial (G : Type uG) (B : Type uB) [Group G] :
    PrincipalBundleTorsorData G B (B × G) where
  projection := Prod.fst
  rightAction p g := (p.1, p.2 * g)
  right_one p := by simp
  right_mul p g h := by simp [mul_assoc]
  projection_rightAction p g := rfl
  fiber_nonempty b := ⟨(b, 1), rfl⟩
  fiber_unique p q sameFiber := by
    refine ⟨p.2⁻¹ * q.2, ?_, ?_⟩
    · apply Prod.ext
      · exact sameFiber
      · simp
    · intro g action_eq
      apply eq_inv_mul_iff_mul_eq.mpr
      exact congrArg Prod.snd action_eq

end PrincipalBundleTorsorData

end YangMills.Geometry
