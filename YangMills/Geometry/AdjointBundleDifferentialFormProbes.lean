/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleDifferentialForm

/-!
# Hostile probes for pointwise adjoint-bundle-valued differential forms
-/

namespace YangMills.Geometry.Probes

open Set
open scoped Manifold ContDiff Bundle Topology

universe uEG uHG uEB uHB uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B]
    {torsor : PrincipalBundleTorsorData G B P}
    (bundle : TopologicalPrincipalBundleData torsor)

/-- A value cannot lie over a base point different from its tangent-space input. -/
theorem base_moving_adjointBundle_differentialFormValue_blocked
    {k : ℕ} (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k)
    (b : B) (v : Fin k → TangentSpace IB b)
    (mismatch : AdjointBundle.projection torsor (((form b) v).1) ≠ b) : False :=
  mismatch (AdjointBundle.DifferentialForm.projection_apply form b v)

/-- A designated coordinate cannot be replaced by a map disconnected from the actual quotient
fiber coordinate. -/
theorem replacement_adjointBundle_differentialFormCoordinate_blocked
    {k : ℕ} (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k)
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet) (v : Fin k → TangentSpace IB b)
    (mismatch : AdjointBundle.DifferentialForm.inCoordinates form chart hb v ≠
      AdjointBundle.fiberModelEquiv (I := IG) bundle chart hb ((form b) v)) : False :=
  mismatch (AdjointBundle.DifferentialForm.inCoordinates_apply form chart hb v)

/-- Alternation cannot be dropped from a degree-two adjoint-bundle-valued form. -/
theorem nonalternating_adjointBundle_twoForm_blocked
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 2)
    (b : B) (v : TangentSpace IB b)
    (nonzero :
      letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberAddCommGroup (I := IG) bundle b
      letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberModule (I := IG) bundle b
      letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberTopology (I := IG) bundle b
      (form b) (fun _ => v) ≠ 0) : False := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  exact nonzero (AdjointBundle.DifferentialForm.evalTwo_same form b v)

/-- The named zero form cannot evaluate to a nonzero dependent fiber value. -/
theorem nonzero_adjointBundle_zeroDifferentialForm_blocked
    (k : ℕ) (b : B) (v : Fin k → TangentSpace IB b)
    (nonzero :
      letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberAddCommGroup (I := IG) bundle b
      letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberModule (I := IG) bundle b
      letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberTopology (I := IG) bundle b
      (AdjointBundle.DifferentialForm.zero (IG := IG) (IB := IB) bundle k b) v ≠ 0) : False := by
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  exact nonzero (AdjointBundle.DifferentialForm.zero_apply (IG := IG) (IB := IB) bundle k b v)

end

end YangMills.Geometry.Probes
