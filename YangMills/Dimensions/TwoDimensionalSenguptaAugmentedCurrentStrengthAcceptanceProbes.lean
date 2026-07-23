/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptance

/-!
# Signature probes for Sengupta-augmented current-strength acceptance

The projection signatures are intentionally checked directly: `heatFactors` depends on the exact
planar semigroup selected inside `current`, while `finiteLawSewing` depends on the exact Lévy sewing
field inside the same record. Substituting unrelated bridges changes these generated projection
signatures and fails elaboration.
-/

namespace YangMills.Dimensions.TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptance.Probes

#check TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData.current
#check TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData.finiteLaw
#check TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData.heatFactors
#check TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData.finiteLawSewing
#check TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData.exact_heatFactors
#check TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData.exact_finiteLawSewing
#check TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptanceData.exact_planarSemigroup

end YangMills.Dimensions.TwoDimensionalSenguptaAugmentedCurrentStrengthAcceptance.Probes
