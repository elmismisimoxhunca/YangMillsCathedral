/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.PoincareTargetTopology

/-!
# Hostile probes for the Poincaré target topology

These probes lock the exact Lorentz-action and translation coordinates and their induced topology.
They do not install an affine group structure or construct a cover.
-/

namespace YangMills.Minkowski.PoincareTargetTopology.Probes

open YangMills
open YangMills.Minkowski

/-- Lorentz coordinates are exactly the accepted linear action. -/
example (d : EuclideanDimension) (L : ProperOrthochronousLorentzTransformation d) :
    properOrthochronousLorentzCoordinate d L = L.linear :=
  rfl

/-- Equal pointwise Lorentz coordinates force equality of the proof-carrying transformations. -/
example (d : EuclideanDimension)
    (first second : ProperOrthochronousLorentzTransformation d)
    (equality : properOrthochronousLorentzCoordinate d first =
      properOrthochronousLorentzCoordinate d second) :
    first = second :=
  properOrthochronousLorentzCoordinate_injective d equality

/-- Affine coordinates retain both the exact Lorentz action and translation. -/
example (d : EuclideanDimension) (p : ProperOrthochronousPoincareTransformation d) :
    properOrthochronousPoincareCoordinate d p =
      (properOrthochronousLorentzCoordinate d p.lorentz, p.translation) :=
  rfl

/-- The exact affine coordinate map is a topological embedding. -/
example (d : EuclideanDimension) :
    Topology.IsEmbedding (properOrthochronousPoincareCoordinate d) :=
  properOrthochronousPoincareCoordinate_isEmbedding d

/-- In particular, the canonical affine coordinate map is continuous. -/
example (d : EuclideanDimension) :
    Continuous (properOrthochronousPoincareCoordinate d) :=
  (properOrthochronousPoincareCoordinate_isEmbedding d).continuous

/-- A disconnected translation coordinate cannot represent the same affine target. -/
theorem changed_translation_blocked
    (d : EuclideanDimension)
    (p q : ProperOrthochronousPoincareTransformation d)
    (sameCoordinate : properOrthochronousPoincareCoordinate d p =
      properOrthochronousPoincareCoordinate d q)
    (differentTranslation : p.translation ≠ q.translation) : False := by
  have equality := properOrthochronousPoincareCoordinate_injective d sameCoordinate
  exact differentTranslation (congrArg ProperOrthochronousPoincareTransformation.translation equality)

end YangMills.Minkowski.PoincareTargetTopology.Probes
