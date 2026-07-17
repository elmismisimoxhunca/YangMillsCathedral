/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundle
import YangMills.Geometry.TopologicalPrincipalBundle

/-!
# Quotient topology on the adjoint bundle

This file equips the set-level adjoint bundle `P ×_G g` with the quotient topology induced by its
representative map. It proves continuity and quotientness of the associated projection to the base.
This is only the topological quotient layer: no local vector-bundle trivialization, smooth structure,
section, differential form, or curvature descent is asserted.
-/

namespace YangMills.Geometry

open scoped Manifold ContDiff

universe uE uH uG uB uP

noncomputable section

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}

namespace AdjointBundle

omit [TopologicalSpace B] [IsTopologicalGroup G] in
/-- The representative-class map is the defining topological quotient map. -/
theorem mk_isQuotientMap :
    Topology.IsQuotientMap
      (fun z : P × GroupLieAlgebra I G => AdjointBundle.mk torsor z.1 z.2) := by
  exact isQuotientMap_quot_mk

omit [TopologicalSpace B] [IsTopologicalGroup G] in
/-- In particular, taking the class of a representative is continuous. -/
theorem mk_continuous :
    Continuous (fun z : P × GroupLieAlgebra I G => AdjointBundle.mk torsor z.1 z.2) :=
  (mk_isQuotientMap (I := I) (torsor := torsor)).continuous

/-- The associated-bundle projection is continuous for the quotient topology. -/
theorem projection_continuous (bundle : TopologicalPrincipalBundleData torsor) :
    Continuous (AdjointBundle.projection torsor : AdjointBundle (I := I) torsor → B) := by
  rw [(mk_isQuotientMap (I := I) (torsor := torsor)).continuous_iff]
  simpa [Function.comp_def] using bundle.projection_continuous.comp continuous_fst

/-- The zero-vector class over a principal point, used only as a topological comparison map. -/
def zeroClass (torsor : PrincipalBundleTorsorData G B P) :
    P → AdjointBundle (I := I) torsor :=
  fun p => AdjointBundle.mk torsor p 0

omit [TopologicalSpace B] [IsTopologicalGroup G] in
/-- The zero-class comparison map is continuous. -/
theorem zeroClass_continuous (torsor : PrincipalBundleTorsorData G B P) :
    Continuous (zeroClass (I := I) torsor) := by
  exact (mk_continuous (I := I) (torsor := torsor)).comp
    (continuous_id.prodMk continuous_const)

omit [TopologicalSpace B] [TopologicalSpace P] [IsTopologicalGroup G] in
@[simp]
theorem projection_zeroClass (torsor : PrincipalBundleTorsorData G B P) (p : P) :
    AdjointBundle.projection torsor (zeroClass (I := I) torsor p) = torsor.projection p :=
  rfl

omit [TopologicalSpace B] [TopologicalSpace P] [IsTopologicalGroup G] in
/-- Every base point has an adjoint-bundle point above it. -/
theorem projection_surjective (torsor : PrincipalBundleTorsorData G B P) :
    Function.Surjective
      (AdjointBundle.projection torsor : AdjointBundle (I := I) torsor → B) := by
  intro b
  obtain ⟨p, hp⟩ := torsor.fiber_nonempty b
  exact ⟨zeroClass (I := I) torsor p, hp⟩

/-- The associated projection induces exactly the declared base topology. -/
theorem projection_isQuotientMap (bundle : TopologicalPrincipalBundleData torsor) :
    Topology.IsQuotientMap
      (AdjointBundle.projection torsor : AdjointBundle (I := I) torsor → B) := by
  apply Topology.IsQuotientMap.of_comp
    (zeroClass_continuous (I := I) (torsor := torsor))
    (projection_continuous (I := I) bundle)
  simpa [Function.comp_def] using bundle.projection_isQuotientMap

end AdjointBundle

end

end YangMills.Geometry
