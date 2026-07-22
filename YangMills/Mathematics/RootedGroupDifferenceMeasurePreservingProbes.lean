/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.RootedGroupDifferenceMeasurePreserving

/-!
# Probes for Haar preservation of rooted group differences
-/

namespace YangMills.Mathematics.RootedGroupDifference.MeasurePreservingProbes

open MeasureTheory

universe uG

variable {G : Type uG} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  [Measure.IsInvInvariant μ]

/-- Both exact difference orientations preserve the unchanged finite product measure at every
arity. -/
theorem exact_forward_product_preservation (n : ℕ) :
    MeasurePreserving (upperForward : (Fin n → G) → (Fin n → G))
        (rootedProductMeasure μ n) (rootedProductMeasure μ n) ∧
      MeasurePreserving (lowerForward : (Fin n → G) → (Fin n → G))
        (rootedProductMeasure μ n) (rootedProductMeasure μ n) :=
  ⟨upperForward_measurePreserving μ, lowerForward_measurePreserving μ⟩

/-- Recursive recovery maps preserve the same product measure, not an unrelated target law. -/
theorem exact_recovery_product_preservation (n : ℕ) :
    MeasurePreserving (upperMeasurableEquiv (G := G) n).symm
        (rootedProductMeasure μ n) (rootedProductMeasure μ n) ∧
      MeasurePreserving (lowerMeasurableEquiv (G := G) n).symm
        (rootedProductMeasure μ n) (rootedProductMeasure μ n) :=
  ⟨upperRecover_measurePreserving μ n, lowerRecover_measurePreserving μ n⟩

/-- The pushed-forward upper product law is literally unchanged. -/
theorem exact_upper_map_eq (n : ℕ) :
    Measure.map (upperForward : (Fin n → G) → (Fin n → G))
        (rootedProductMeasure μ n) = rootedProductMeasure μ n :=
  (upperForward_measurePreserving μ).map_eq

/-- The pushed-forward lower product law is literally unchanged. -/
theorem exact_lower_map_eq (n : ℕ) :
    Measure.map (lowerForward : (Fin n → G) → (Fin n → G))
        (rootedProductMeasure μ n) = rootedProductMeasure μ n :=
  (lowerForward_measurePreserving μ).map_eq

end YangMills.Mathematics.RootedGroupDifference.MeasurePreservingProbes
