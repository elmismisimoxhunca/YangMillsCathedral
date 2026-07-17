/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalBundleTorsor
import YangMills.Mathematics.LieGroupAdjoint

/-!
# Set-level adjoint bundle

Freed identifies horizontal right-equivariant forms on a principal bundle with forms valued in the
adjoint bundle `g_P = P ×_G g`. This file constructs the set-level associated-bundle carrier as the
orbit quotient of `P × g` by the diagonal right action

`(p, X) · g = (p · g, Ad(g⁻¹) X)`.

The quotient retains the actual principal bundle and actual gauge-group carrier. Topology, smooth
vector-bundle charts, tangent-valued forms, and curvature descent are deliberately separate future
layers; no section, connection, curvature, or Yang--Mills field is constructed here.
-/

namespace YangMills.Geometry

open scoped Manifold ContDiff

universe uE uH uG uB uP

noncomputable section

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]
    (torsor : PrincipalBundleTorsorData G B P)

/-- Diagonal right action used to form the adjoint associated bundle. -/
def adjointBundleRightAction
    (z : P × GroupLieAlgebra I G) (g : G) : P × GroupLieAlgebra I G :=
  (torsor.rightAction z.1 g,
    YangMills.Mathematics.lieGroupAdjoint I g⁻¹ z.2)

@[simp]
theorem adjointBundleRightAction_one (z : P × GroupLieAlgebra I G) :
    adjointBundleRightAction torsor z 1 = z := by
  simp [adjointBundleRightAction, torsor.right_one,
    YangMills.Mathematics.lieGroupAdjoint_one]

/-- The diagonal action follows the same right-action multiplication order as the principal
bundle. -/
theorem adjointBundleRightAction_mul
    (z : P × GroupLieAlgebra I G) (g h : G) :
    adjointBundleRightAction torsor (adjointBundleRightAction torsor z g) h =
      adjointBundleRightAction torsor z (g * h) := by
  apply Prod.ext
  · exact torsor.right_mul z.1 g h
  · simp only [adjointBundleRightAction, mul_inv_rev]
    rw [YangMills.Mathematics.lieGroupAdjoint_mul]
    rfl

/-- Two representatives are equivalent exactly when they lie in the same diagonal right orbit. -/
def adjointBundleOrbitRelation
    (x y : P × GroupLieAlgebra I G) : Prop :=
  ∃ g : G, adjointBundleRightAction torsor x g = y

/-- The diagonal orbit relation is an equivalence relation. -/
def adjointBundleSetoid : Setoid (P × GroupLieAlgebra I G) where
  r := adjointBundleOrbitRelation torsor
  iseqv := {
    refl := fun x => ⟨1, adjointBundleRightAction_one torsor x⟩
    symm := by
      intro x y hxy
      obtain ⟨g, rfl⟩ := hxy
      refine ⟨g⁻¹, ?_⟩
      rw [adjointBundleRightAction_mul]
      simp
    trans := by
      intro x y z hxy hyz
      obtain ⟨g, rfl⟩ := hxy
      obtain ⟨h, rfl⟩ := hyz
      exact ⟨g * h, (adjointBundleRightAction_mul torsor x g h).symm⟩
  }

/-- Set-level total carrier of the adjoint associated bundle `P ×_G g`. -/
abbrev AdjointBundle := Quotient (adjointBundleSetoid (I := I) torsor)

/-- Class of one representative in the adjoint bundle. -/
def AdjointBundle.mk (p : P) (X : GroupLieAlgebra I G) : AdjointBundle (I := I) torsor :=
  Quotient.mk _ (p, X)

/-- The associated-bundle projection is well-defined because the diagonal action stays in one
principal fiber. -/
def AdjointBundle.projection : AdjointBundle (I := I) torsor → B :=
  Quotient.lift (fun z => torsor.projection z.1) (by
    intro x y hxy
    obtain ⟨g, rfl⟩ := hxy
    exact (torsor.projection_rightAction x.1 g).symm)

@[simp]
theorem AdjointBundle.projection_mk (p : P) (X : GroupLieAlgebra I G) :
    AdjointBundle.projection torsor (AdjointBundle.mk torsor p X) = torsor.projection p :=
  rfl

/-- Moving a representative by the defining diagonal action leaves its quotient class unchanged. -/
theorem AdjointBundle.mk_rightAction
    (p : P) (X : GroupLieAlgebra I G) (g : G) :
    AdjointBundle.mk torsor (torsor.rightAction p g)
        (YangMills.Mathematics.lieGroupAdjoint I g⁻¹ X) =
      AdjointBundle.mk torsor p X := by
  have sameOrbit : adjointBundleOrbitRelation torsor (p, X)
      (adjointBundleRightAction torsor (p, X) g) := ⟨g, rfl⟩
  exact (Quotient.sound sameOrbit).symm

/-- Equality of quotient classes is exactly the generated same-orbit relation. -/
theorem AdjointBundle.mk_eq_mk_iff
    (p q : P) (X Y : GroupLieAlgebra I G) :
    AdjointBundle.mk torsor p X = AdjointBundle.mk torsor q Y ↔
      ∃ g : G,
        torsor.rightAction p g = q ∧
          YangMills.Mathematics.lieGroupAdjoint I g⁻¹ X = Y := by
  change Quotient.mk _ (p, X) = Quotient.mk _ (q, Y) ↔ _
  rw [Quotient.eq]
  change adjointBundleOrbitRelation torsor (p, X) (q, Y) ↔ _
  constructor
  · rintro ⟨g, h⟩
    exact ⟨g, congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨g, hp, hX⟩
    exact ⟨g, Prod.ext hp hX⟩

end

end YangMills.Geometry
