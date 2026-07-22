/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.FourDimensionalContinuumCoreAcceptance

/-!
# Universally quantified current-strength four-dimensional acceptance target

The existing four-dimensional continuum core is indexed by already chosen classical and quantum
carriers. This module packages all such construction-specific carriers existentially while leaving
the exact compact-simple gauge-group input universally quantified.

The resulting proposition is deliberately named `CurrentStrength`: it exposes the correct outer
quantifier shape but is not the final Clay acceptance proposition. Completed OS source topology,
full observable/OPE grammar, concrete Poincare realizations, and other documented obligations remain
open. No theorem inhabits the proposition, and this module constructs no theory or mass gap.
-/

namespace YangMills.Dimensions

open scoped Manifold ContDiff

universe uEG uGauge uEP uHP uP uLift uH uLabel

noncomputable section

/-- All construction-specific carriers needed to instantiate the existing current-strength
four-dimensional core for one caller-supplied exact compact-simple gauge certificate.

The physical gauge group and its certificate remain external indices. In particular, they are not
silently replaced by an existentially selected group. -/
structure FourDimensionalCurrentStrengthTheoryWitness
    (EG : Type uEG) (GaugeGroup : Type uGauge)
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [Group GaugeGroup] [TopologicalSpace GaugeGroup] [T2Space GaugeGroup]
    [SecondCountableTopology GaugeGroup] [ChartedSpace EG GaugeGroup]
    [LieGroup (modelWithCornersSelf ℝ EG) ∞ GaugeGroup]
    (gauge : Geometry.CompactSimpleGaugeGroupData GaugeGroup EG) where
  /-- Additional topological-group compatibility required by the principal-bundle chain. -/
  [gaugeTopologicalGroup : IsTopologicalGroup GaugeGroup]
  /-- Principal total-space model and carrier. -/
  EP : Type uEP
  HP : Type uHP
  [epNormedAddCommGroup : NormedAddCommGroup EP]
  [epNormedSpace : NormedSpace ℝ EP]
  [hpTopologicalSpace : TopologicalSpace HP]
  P : Type uP
  [pTopologicalSpace : TopologicalSpace P]
  IP : ModelWithCorners ℝ EP HP
  [pChartedSpace : ChartedSpace HP P]
  [pIsManifold : IsManifold IP ∞ P]
  /-- Exact principal-bundle chain over coordinate four-space. -/
  torsor : Geometry.PrincipalBundleTorsorData GaugeGroup FourDimensionalEuclideanBase P
  bundle : Geometry.TopologicalPrincipalBundleData torsor
  smoothBundle : Geometry.SmoothPrincipalBundleData fourDimensionalEuclideanModel
    (modelWithCornersSelf ℝ EG) IP torsor bundle
  /-- Independent Poincare lift group and exact lift. -/
  PoincareLiftGroup : Type uLift
  [liftGroup : Group PoincareLiftGroup]
  [liftTopology : TopologicalSpace PoincareLiftGroup]
  [liftTopologicalGroup : IsTopologicalGroup PoincareLiftGroup]
  lift : Minkowski.ProperOrthochronousPoincareLiftData
    EuclideanDimension.four PoincareLiftGroup
  /-- Physical Hilbert-space and common-domain field chain. -/
  H : Type uH
  [hNormedAddCommGroup : NormedAddCommGroup H]
  [hInnerProductSpace : InnerProductSpace ℂ H]
  [hCompleteSpace : CompleteSpace H]
  [hSeparableSpace : TopologicalSpace.SeparableSpace H]
  U : Minkowski.StronglyContinuousUnitaryPoincareRepresentation lift H
  vacuumData : Minkowski.PoincareInvariantVacuumData U
  D : Minkowski.CommonInvariantDomainData vacuumData
  fieldData : Minkowski.ScalarWightmanFieldOnCommonDomainData D
  /-- Same-chain classical connection, first exterior datum, and curvature certificate. -/
  inner : Geometry.InvariantInnerProductData
    (I := modelWithCornersSelf ℝ EG) (G := GaugeGroup)
  connection : Geometry.PrincipalConnectionData smoothBundle
  exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection
  curvatureCertificate : Geometry.PrincipalCurvatureStructureCertificate
    smoothBundle connection exterior
  /-- The unchanged broad current-strength continuum core. -/
  core : FourDimensionalCurrentStrengthContinuumCoreAcceptanceData.{
    uEG, uEP, uHP, uGauge, uP, uLift, uH, uLabel}
    inner connection exterior curvatureCertificate fieldData
  /-- The core's compact-simple field is exactly the caller-supplied certificate. -/
  core_gauge_eq : core.compactSimpleGaugeGroup = gauge

/-- Preliminary universally quantified acceptance target at the repository's current source
strength. Every exact compact-simple input must receive one package of construction-specific
carriers instantiating the existing four-dimensional core.

This is only a proposition definition. There is intentionally no inhabitance theorem. -/
def FourDimensionalCurrentStrengthUniversalAcceptance : Prop :=
  ∀ (EG : Type uEG) (GaugeGroup : Type uGauge)
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [Group GaugeGroup] [TopologicalSpace GaugeGroup] [T2Space GaugeGroup]
    [SecondCountableTopology GaugeGroup] [ChartedSpace EG GaugeGroup]
    [LieGroup (modelWithCornersSelf ℝ EG) ∞ GaugeGroup]
    (gauge : Geometry.CompactSimpleGaugeGroupData GaugeGroup EG),
    Nonempty
      (FourDimensionalCurrentStrengthTheoryWitness.{uEG, uGauge, uEP, uHP, uP, uLift, uH, uLabel}
        EG GaugeGroup gauge)

end

end YangMills.Dimensions
