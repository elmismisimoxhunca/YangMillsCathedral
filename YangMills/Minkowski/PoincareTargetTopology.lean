/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.PoincareKinematics
import Mathlib.Topology.Covering.Basic

/-!
# Canonical coordinate topology on proper-orthochronous Poincaré kinematics

A genuine topological covering projection requires topology on the exact affine target. This module
uses the pointwise function topology on the Lorentz linear action and the product topology with the
translation coordinate. In finite dimension this is the direct coordinate topology needed for the
covering interface; no Lie-group, connectedness, matrix-exponential, or `SL(2,ℂ)` construction is
claimed.
-/

namespace YangMills.Minkowski

/-- Pointwise coordinate map for a proper-orthochronous Lorentz transformation. -/
def properOrthochronousLorentzCoordinate
    (d : EuclideanDimension) (L : ProperOrthochronousLorentzTransformation d) :
    Spacetime d → Spacetime d :=
  L.linear

/-- The Lorentz coordinate determines the proof-carrying transformation. -/
theorem properOrthochronousLorentzCoordinate_injective
    (d : EuclideanDimension) :
    Function.Injective (properOrthochronousLorentzCoordinate d) := by
  intro first second equality
  cases first with
  | mk firstLinear firstPreserves firstDet firstFuture =>
      cases second with
      | mk secondLinear secondPreserves secondDet secondFuture =>
          simp only [properOrthochronousLorentzCoordinate] at equality
          have linearEquality : firstLinear = secondLinear :=
            LinearEquiv.ext (fun x => congrFun equality x)
          subst secondLinear
          rfl

/-- Canonical pointwise coordinate topology on the Lorentz carrier. -/
instance properOrthochronousLorentzTopologicalSpace (d : EuclideanDimension) :
    TopologicalSpace (ProperOrthochronousLorentzTransformation d) :=
  TopologicalSpace.induced (properOrthochronousLorentzCoordinate d) inferInstance

/-- The Lorentz coordinate is a topological embedding for the canonical induced topology. -/
theorem properOrthochronousLorentzCoordinate_isEmbedding
    (d : EuclideanDimension) :
    Topology.IsEmbedding (properOrthochronousLorentzCoordinate d) :=
  ⟨Topology.IsInducing.induced _, properOrthochronousLorentzCoordinate_injective d⟩

/-- Exact affine coordinate: Lorentz pointwise action together with translation. -/
def properOrthochronousPoincareCoordinate
    (d : EuclideanDimension) (p : ProperOrthochronousPoincareTransformation d) :
    (Spacetime d → Spacetime d) × Spacetime d :=
  (properOrthochronousLorentzCoordinate d p.lorentz, p.translation)

/-- The affine coordinate determines the proof-carrying Poincaré transformation. -/
theorem properOrthochronousPoincareCoordinate_injective
    (d : EuclideanDimension) :
    Function.Injective (properOrthochronousPoincareCoordinate d) := by
  intro first second equality
  have lorentzEquality : first.lorentz = second.lorentz :=
    properOrthochronousLorentzCoordinate_injective d (congrArg Prod.fst equality)
  have translationEquality : first.translation = second.translation :=
    congrArg Prod.snd equality
  cases first
  cases second
  simp_all

/-- Canonical affine coordinate topology on the exact Poincaré target. -/
instance properOrthochronousPoincareTopologicalSpace (d : EuclideanDimension) :
    TopologicalSpace (ProperOrthochronousPoincareTransformation d) :=
  TopologicalSpace.induced (properOrthochronousPoincareCoordinate d) inferInstance

/-- The exact affine coordinate is a topological embedding. -/
theorem properOrthochronousPoincareCoordinate_isEmbedding
    (d : EuclideanDimension) :
    Topology.IsEmbedding (properOrthochronousPoincareCoordinate d) :=
  ⟨Topology.IsInducing.induced _, properOrthochronousPoincareCoordinate_injective d⟩

end YangMills.Minkowski
