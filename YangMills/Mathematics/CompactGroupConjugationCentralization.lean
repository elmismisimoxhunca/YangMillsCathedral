/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactGroupCharacterCentralizationBridge
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Conjugation-Haar centralization on compact groups

For a compact second-countable Hausdorff topological group, this file constructs Hall's actual
conjugation average

`P(f)(x) = ∫ h, f(h*x*h⁻¹) dμ_H(h)`

as a continuous linear map from `C(G, ℂ)` to the exact continuous-central carrier. It proves:

* continuity in `x` by Mathlib's compact parametric-integral theorem;
* conjugation invariance by normalized Haar right invariance;
* identity on central functions;
* operator norm at most one;
* surjectivity and idempotence.

Thus the only field of `CompactGroupCharacterCentralizationData` still not discharged is Hall's
finite Schur-to-character calculation on arbitrary selected coefficient syntheses. A constructor at
the end makes that remaining obligation exact.

Second countability is explicit because the available parametric Bochner-integral theorem uses it.
No character-density theorem is inferred without the remaining coefficient-to-character formula.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Pointwise probability-Haar average over inner conjugations. -/
noncomputable def compactGroupConjugationAverage (f : C(G, ℂ)) (x : G) : ℂ :=
  ∫ h, f (h * x * h⁻¹) ∂normalizedCompactHaarMeasure G

/-- The pointwise conjugation average is continuous under the explicit second-countability
hypothesis required by the parametric-integral theorem. -/
theorem continuous_compactGroupConjugationAverage
    [SecondCountableTopology G] (f : C(G, ℂ)) :
    Continuous (compactGroupConjugationAverage f) := by
  let μ := normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  have jointContinuous : Continuous
      (Function.uncurry (fun x h : G => f (h * x * h⁻¹))) := by
    fun_prop
  change Continuous (fun x => ∫ h, f (h * x * h⁻¹) ∂μ)
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous jointContinuous
      (μ := μ) (s := Set.univ) isCompact_univ)

omit [T2Space G] in
/-- The pointwise average is invariant under inner conjugation. -/
theorem compactGroupConjugationAverage_central
    [SecondCountableTopology G] (f : C(G, ℂ)) (x k : G) :
    compactGroupConjugationAverage f (k * x * k⁻¹) =
      compactGroupConjugationAverage f x := by
  let μ := normalizedCompactHaarMeasure G
  letI : Measure.IsMulRightInvariant μ :=
    normalizedCompactHaarMeasure_isMulRightInvariant G
  change (∫ h, f (h * (k * x * k⁻¹) * h⁻¹) ∂μ) =
    ∫ h, f (h * x * h⁻¹) ∂μ
  simpa only [mul_assoc, mul_inv_rev, inv_inv, inv_mul_cancel_right] using
    (integral_mul_right_eq_self (μ := μ) (fun h => f (h * x * h⁻¹)) k)

omit [T2Space G] in
/-- Averaging fixes every continuous central function pointwise. -/
theorem compactGroupConjugationAverage_fixes_central
    (f : continuousCentralFunctionStarSubalgebra G) (x : G) :
    compactGroupConjugationAverage (f : C(G, ℂ)) x = (f : C(G, ℂ)) x := by
  let μ := normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  change (∫ h, (f : C(G, ℂ)) (h * x * h⁻¹) ∂μ) = (f : C(G, ℂ)) x
  apply integral_eq_const
  filter_upwards with h
  exact f.property x h

/-- Conjugation averaging as a complex-linear map into the exact central carrier. -/
noncomputable def compactGroupConjugationCentralizationLinear
    [SecondCountableTopology G] :
    C(G, ℂ) →ₗ[ℂ] continuousCentralFunctionStarSubalgebra G where
  toFun f := ⟨⟨compactGroupConjugationAverage f,
    continuous_compactGroupConjugationAverage f⟩, by
      intro g h
      exact compactGroupConjugationAverage_central f g h⟩
  map_add' f g := by
    letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
      normalizedCompactHaarMeasure_isProbability G
    apply Subtype.ext
    ext x
    change (∫ h, f (h * x * h⁻¹) + g (h * x * h⁻¹)
      ∂normalizedCompactHaarMeasure G) =
      compactGroupConjugationAverage f x + compactGroupConjugationAverage g x
    rw [integral_add]
    · rfl
    · have hcont : Continuous (fun h => f (h * x * h⁻¹)) := by fun_prop
      simpa only [integrableOn_univ] using
        hcont.continuousOn.integrableOn_compact
          (μ := normalizedCompactHaarMeasure G) isCompact_univ
    · have hcont : Continuous (fun h => g (h * x * h⁻¹)) := by fun_prop
      simpa only [integrableOn_univ] using
        hcont.continuousOn.integrableOn_compact
          (μ := normalizedCompactHaarMeasure G) isCompact_univ
  map_smul' c f := by
    apply Subtype.ext
    ext x
    change (∫ h, c * f (h * x * h⁻¹) ∂normalizedCompactHaarMeasure G) =
      c * compactGroupConjugationAverage f x
    rw [integral_const_mul]
    rfl

/-- Conjugation averaging has operator norm at most one. -/
theorem compactGroupConjugationCentralizationLinear_norm
    [SecondCountableTopology G] (f : C(G, ℂ)) :
    ‖compactGroupConjugationCentralizationLinear f‖ ≤ ‖f‖ := by
  change ‖((compactGroupConjugationCentralizationLinear (G := G) f :
    continuousCentralFunctionStarSubalgebra G) : C(G, ℂ))‖ ≤ ‖f‖
  apply (ContinuousMap.norm_le (f :=
    ((compactGroupConjugationCentralizationLinear (G := G) f :
      continuousCentralFunctionStarSubalgebra G) : C(G, ℂ))) (norm_nonneg f)).2
  intro x
  change ‖∫ h, f (h * x * h⁻¹) ∂normalizedCompactHaarMeasure G‖ ≤ ‖f‖
  let μ := normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  calc
    _ ≤ ‖f‖ * μ.real Set.univ := norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall fun h =>
        ContinuousMap.norm_coe_le_norm f (h * x * h⁻¹))
    _ = ‖f‖ := by simp

/-- Hall conjugation centralization as a continuous complex-linear map. -/
noncomputable def compactGroupConjugationCentralization
    [SecondCountableTopology G] :
    C(G, ℂ) →L[ℂ] continuousCentralFunctionStarSubalgebra G :=
  LinearMap.mkContinuous (compactGroupConjugationCentralizationLinear (G := G)) 1 (by
    intro f
    simpa using compactGroupConjugationCentralizationLinear_norm f)

/-- The operator norm of conjugation centralization is at most one. -/
theorem compactGroupConjugationCentralization_norm_le_one
    [SecondCountableTopology G] :
    ‖compactGroupConjugationCentralization (G := G)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖compactGroupConjugationCentralizationLinear (G := G) f‖ ≤ 1 * ‖f‖
  simpa using compactGroupConjugationCentralizationLinear_norm f

/-- Exact pointwise formula for the bundled continuous centralization map. -/
@[simp]
theorem compactGroupConjugationCentralization_apply
    [SecondCountableTopology G] (f : C(G, ℂ)) (x : G) :
    ((compactGroupConjugationCentralization (G := G) f :
      continuousCentralFunctionStarSubalgebra G) : C(G, ℂ)) x =
      ∫ h, f (h * x * h⁻¹) ∂normalizedCompactHaarMeasure G :=
  rfl

/-- The bundled centralization map fixes every central function. -/
theorem compactGroupConjugationCentralization_fixes_central
    [SecondCountableTopology G]
    (f : continuousCentralFunctionStarSubalgebra G) :
    compactGroupConjugationCentralization (f : C(G, ℂ)) = f := by
  apply Subtype.ext
  ext x
  exact compactGroupConjugationAverage_fixes_central f x

/-- The constructed centralization map is surjective. -/
theorem compactGroupConjugationCentralization_surjective
    [SecondCountableTopology G] :
    Function.Surjective (compactGroupConjugationCentralization (G := G)) := by
  intro f
  exact ⟨(f : C(G, ℂ)), compactGroupConjugationCentralization_fixes_central f⟩

/-- The constructed centralization is idempotent after including its central output back into
`C(G, ℂ)`. -/
theorem compactGroupConjugationCentralization_idempotent
    [SecondCountableTopology G] (f : C(G, ℂ)) :
    compactGroupConjugationCentralization
      ((compactGroupConjugationCentralization f :
        continuousCentralFunctionStarSubalgebra G) : C(G, ℂ)) =
      compactGroupConjugationCentralization f :=
  compactGroupConjugationCentralization_fixes_central _

/-- Construct the full abstract centralization bridge once the remaining finite
coefficient-to-character formula is supplied for the actual Haar average. -/
noncomputable def compactGroupCharacterCentralizationDataOfMapsCoefficientSynthesis
    [SecondCountableTopology G]
    (mapsCoefficientSynthesis : ∀ A : UnitaryMatrixDualCoefficientSpace G,
      ∃ c : UnitaryMatrixDualCharacterCoefficients G,
        compactGroupConjugationCentralization
          (unitaryMatrixDualContinuousCoefficientSynthesis G A) =
            unitaryMatrixDualCentralCharacterSynthesis G c) :
    CompactGroupCharacterCentralizationData G where
  centralization := compactGroupConjugationCentralization
  fixes_central := compactGroupConjugationCentralization_fixes_central
  maps_coefficient_synthesis := mapsCoefficientSynthesis

end

end Mathematics
end YangMills
