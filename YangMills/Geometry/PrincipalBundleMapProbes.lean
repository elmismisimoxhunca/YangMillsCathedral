/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalBundleMap

/-!
# Hostile probes for torsor maps and algebraic gauge transformations

These probes reject maps disconnected from their declared base map or group action, and reject
noninvertible, base-moving, or nonequivariant gauge candidates. Smoothness remains outside this
algebraic layer.
-/

namespace YangMills.Geometry.Probes

universe uG uB uP uB' uP'

variable {G : Type uG} [Group G]
variable {B : Type uB} {P : Type uP} {B' : Type uB'} {P' : Type uP'}
variable {source : PrincipalBundleTorsorData G B P}
variable {target : PrincipalBundleTorsorData G B' P'}

/-- A total-space map cannot be disconnected from its declared base map. -/
theorem bundleMap_projection_mismatch_blocked
    (map : PrincipalBundleTorsorMap source target) (p : P)
    (mismatch : target.projection (map.totalMap p) ≠ map.baseMap (source.projection p)) : False :=
  mismatch (map.projection_commutes p)

/-- A torsor map cannot violate right-action equivariance. -/
theorem nonequivariant_bundleMap_blocked
    (map : PrincipalBundleTorsorMap source target) (p : P) (g : G)
    (mismatch : map.totalMap (source.rightAction p g) ≠
      target.rightAction (map.totalMap p) g) : False :=
  mismatch (map.equivariant p g)

/-- The identity torsor map fixes every total-space point. -/
theorem identity_bundleMap_fixes (p : P) :
    (PrincipalBundleTorsorMap.id source).totalMap p = p :=
  rfl

/-- Composition of two identity torsor maps fixes every total-space point. -/
theorem identity_bundleMap_composition_fixes (p : P) :
    (PrincipalBundleTorsorMap.comp
      (PrincipalBundleTorsorMap.id source)
      (PrincipalBundleTorsorMap.id source)).totalMap p = p :=
  rfl

/-- An algebraic gauge transformation cannot move a point to another base fiber. -/
theorem base_moving_gaugeTransformation_blocked
    (gauge : TorsorGaugeTransformation source) (p : P)
    (movesBase : source.projection (gauge p) ≠ source.projection p) : False :=
  movesBase (gauge.projection_preserving p)

/-- An algebraic gauge transformation cannot violate right-action equivariance. -/
theorem nonequivariant_gaugeTransformation_blocked
    (gauge : TorsorGaugeTransformation source) (p : P) (g : G)
    (mismatch : gauge (source.rightAction p g) ≠ source.rightAction (gauge p) g) : False :=
  mismatch (gauge.equivariant p g)

/-- Gauge transformations are genuine equivalences, so distinct points cannot be identified. -/
theorem noninjective_gaugeTransformation_blocked
    (gauge : TorsorGaugeTransformation source) (p q : P)
    (distinct : p ≠ q) (identified : gauge p = gauge q) : False :=
  distinct (gauge.toEquiv.injective identified)

/-- Forgetting gauge invertibility preserves the same total map and identity base map. -/
theorem gaugeTransformation_toBundleMap_coherent
    (gauge : TorsorGaugeTransformation source) (p : P) :
    gauge.toTorsorMap.totalMap p = gauge p ∧
      gauge.toTorsorMap.baseMap (source.projection p) = source.projection p :=
  ⟨rfl, rfl⟩

/-- The gauge identity is concrete positive consistency evidence. -/
theorem identity_gaugeTransformation_fixes
    (p : P) : (1 : TorsorGaugeTransformation source) p = p :=
  rfl

/-- The inverse in the gauge-transformation group undoes the original transformation. -/
theorem inverse_gaugeTransformation_undoes
    (gauge : TorsorGaugeTransformation source) (p : P) :
    gauge⁻¹ (gauge p) = p := by
  exact gauge.toEquiv.symm_apply_apply p

end YangMills.Geometry.Probes
