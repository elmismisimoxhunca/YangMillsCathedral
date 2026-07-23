/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.LinearAlgebra.Finsupp.LSum
import YangMills.Mathematics.UnitaryMatrixDualL2Span
import YangMills.Mathematics.CompactUnitaryCharacterOrthogonality

/-!
# Algebraic character synthesis over the coordinate unitary dual

This file specializes the all-class coefficient theory to trace characters. A finitely supported
scalar family on `UnitaryMatrixDual G` synthesizes the central continuous function

`g ↦ ∑q c(q) tr(ρq(g))`.

Character orthogonality proves exact coefficient analysis, injectivity, and the finite-support
character pairing

`∫ conj(S(c)) S(d) dμ_H = ∑q conj(c(q)) d(q)`.

The resulting range is the algebraic central-character subspace. No density among all central
continuous or `L²` functions is asserted.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

/-- Finitely supported scalar coefficients indexed by every coordinate unitary-dual class. -/
abbrev UnitaryMatrixDualCharacterCoefficients
 (G:Type uG) [Group G] [TopologicalSpace G] := UnitaryMatrixDual G →₀ ℂ

/-- The exact trace character of the selected representative of a dual class. -/
def unitaryMatrixDualCharacter
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q:UnitaryMatrixDual G) : G→ℂ :=
 fun g => Matrix.trace (unitaryMatrixDualRepresentation q g)

def unitaryMatrixDualCharacterScalarMap
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q:UnitaryMatrixDual G) : ℂ →ₗ[ℂ] (G→ℂ) where
 toFun c := c • unitaryMatrixDualCharacter q
 map_add' a b := by ext g;simp [add_mul]
 map_smul' a b := by ext g;simp [mul_assoc]

/-- Linear finite-support synthesis of trace characters over the coordinate unitary dual. -/
def unitaryMatrixDualCharacterSynthesis
 (G:Type uG) [Group G] [TopologicalSpace G] :
 UnitaryMatrixDualCharacterCoefficients G →ₗ[ℂ] (G→ℂ) :=
 (Finsupp.lsum ℂ) fun q => unitaryMatrixDualCharacterScalarMap q

@[simp] theorem unitaryMatrixDualCharacterSynthesis_single
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q:UnitaryMatrixDual G) (c:ℂ) :
 unitaryMatrixDualCharacterSynthesis G (Finsupp.single q c) =
  c • unitaryMatrixDualCharacter q := by
 exact Finsupp.lsum_single ℂ _ q c

theorem continuous_unitaryMatrixDualCharacter
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q:UnitaryMatrixDual G) : Continuous (unitaryMatrixDualCharacter q) :=
 continuous_matrixRepresentation_trace _
  (continuous_unitaryMatrixDualRepresentation q)

theorem unitaryMatrixDualCharacter_conj
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q:UnitaryMatrixDual G) (g h:G) :
 unitaryMatrixDualCharacter q (h*g*h⁻¹)=unitaryMatrixDualCharacter q g :=
 matrixRepresentation_trace_conj _ g h

theorem continuous_unitaryMatrixDualCharacterSynthesis
 {G:Type uG} [Group G] [TopologicalSpace G]
 (c:UnitaryMatrixDualCharacterCoefficients G) :
 Continuous (unitaryMatrixDualCharacterSynthesis G c) := by
 classical
 induction c using Finsupp.induction with
 | zero => rw [map_zero];fun_prop
 | @single_add q a c hq ha hc =>
   rw [map_add,unitaryMatrixDualCharacterSynthesis_single]
   exact (continuous_unitaryMatrixDualCharacter q).const_smul a |>.add hc

theorem unitaryMatrixDualCharacterSynthesis_conj
 {G:Type uG} [Group G] [TopologicalSpace G]
 (c:UnitaryMatrixDualCharacterCoefficients G) (g h:G) :
 unitaryMatrixDualCharacterSynthesis G c (h*g*h⁻¹)=
 unitaryMatrixDualCharacterSynthesis G c g := by
 classical
 induction c using Finsupp.induction with
 | zero => rw [map_zero];rfl
 | @single_add q a c hq ha hc =>
   rw [map_add,unitaryMatrixDualCharacterSynthesis_single]
   change a*unitaryMatrixDualCharacter q (h*g*h⁻¹)+
      unitaryMatrixDualCharacterSynthesis G c (h*g*h⁻¹)=_
   rw [unitaryMatrixDualCharacter_conj, hc]
   rfl

/-- Haar analysis against one character recovers its exact finitely supported coefficient. -/
theorem normalizedCompactHaar_unitaryMatrixDualCharacter_analysis
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 (c:UnitaryMatrixDualCharacterCoefficients G) (q:UnitaryMatrixDual G) :
 (∫g,star (unitaryMatrixDualCharacter q g)*
   unitaryMatrixDualCharacterSynthesis G c g ∂normalizedCompactHaarMeasure G) =
 c q := by
 classical
 let μ := normalizedCompactHaarMeasure G
 letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
 induction c using Finsupp.induction with
 | zero => rw [map_zero];simp
 | @single_add r a c hr ha hc =>
   rw [map_add,unitaryMatrixDualCharacterSynthesis_single]
   have hIntSingle : Integrable (fun g =>
      star (unitaryMatrixDualCharacter q g)*(a*unitaryMatrixDualCharacter r g)) μ := by
    have hcont : Continuous (fun g =>
      star (unitaryMatrixDualCharacter q g)*(a*unitaryMatrixDualCharacter r g)) := by
      exact (continuous_unitaryMatrixDualCharacter q).star.mul
        ((continuous_unitaryMatrixDualCharacter r).const_mul a)
    simpa only [integrableOn_univ] using
     hcont.continuousOn.integrableOn_compact (μ:=μ) isCompact_univ
   have hIntRest : Integrable (fun g =>
      star (unitaryMatrixDualCharacter q g)*unitaryMatrixDualCharacterSynthesis G c g) μ := by
    have hcont : Continuous (fun g =>
      star (unitaryMatrixDualCharacter q g)*unitaryMatrixDualCharacterSynthesis G c g) := by
      exact (continuous_unitaryMatrixDualCharacter q).star.mul
       (continuous_unitaryMatrixDualCharacterSynthesis c)
    simpa only [integrableOn_univ] using
     hcont.continuousOn.integrableOn_compact (μ:=μ) isCompact_univ
   have hpoint : (fun g => star (unitaryMatrixDualCharacter q g)*
      ((a • unitaryMatrixDualCharacter r)+unitaryMatrixDualCharacterSynthesis G c) g) =
     fun g => star (unitaryMatrixDualCharacter q g)*(a*unitaryMatrixDualCharacter r g)+
      star (unitaryMatrixDualCharacter q g)*unitaryMatrixDualCharacterSynthesis G c g := by
    funext g
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
   rw [hpoint,integral_add hIntSingle hIntRest,hc]
   have hsingle : (∫g,star (unitaryMatrixDualCharacter q g)*
      (a*unitaryMatrixDualCharacter r g) ∂μ) = if r=q then a else 0 := by
    calc
     _ = a*(∫g,star (unitaryMatrixDualCharacter q g)*
       unitaryMatrixDualCharacter r g ∂μ) := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with g
      ring
     _ = if r=q then a else 0 := by
      by_cases hrq':r=q
      · subst r
        change a * (∫g, star (Matrix.trace
          (unitaryMatrixDualRepresentation q g)) * Matrix.trace
          (unitaryMatrixDualRepresentation q g) ∂normalizedCompactHaarMeasure G) = _
        rw [normalizedCompactHaar_character_normSq_integral
         (unitaryMatrixDualRepresentation q)
         (continuous_unitaryMatrixDualRepresentation q)
         (unitary_unitaryMatrixDualRepresentation q)
         (unitaryMatrixDualDimension_pos q)]
        simp
      · letI := unitaryMatrixDual_representative_inequivalent (Ne.symm hrq')
        change a * (∫g, star (Matrix.trace
          (unitaryMatrixDualRepresentation q g)) * Matrix.trace
          (unitaryMatrixDualRepresentation r g) ∂normalizedCompactHaarMeasure G) = _
        rw [normalizedCompactHaar_character_orthogonality_inequivalent
         (unitaryMatrixDualRepresentation q)
         (unitaryMatrixDualRepresentation r)
         (continuous_unitaryMatrixDualRepresentation q)
         (continuous_unitaryMatrixDualRepresentation r)
         (unitary_unitaryMatrixDualRepresentation q)]
        simp [hrq']
   rw [hsingle]
   by_cases hrq':r=q
   · subst r
     simp
   · simp [hrq']

/-- All-class finite-support character synthesis is injective. -/
theorem unitaryMatrixDualCharacterSynthesis_injective
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
 Function.Injective (unitaryMatrixDualCharacterSynthesis G) := by
 intro c d hcd
 ext q
 have h := congrArg (fun f:G→ℂ =>
  ∫g,star (unitaryMatrixDualCharacter q g)*f g ∂normalizedCompactHaarMeasure G) hcd
 rw [normalizedCompactHaar_unitaryMatrixDualCharacter_analysis c q,
  normalizedCompactHaar_unitaryMatrixDualCharacter_analysis d q] at h
 exact h

def unitaryMatrixDualCharacterCoefficientPairing
 {G:Type uG} [Group G] [TopologicalSpace G]
 (c d:UnitaryMatrixDualCharacterCoefficients G) : ℂ :=
 c.sum fun q a => star (a)*d q

/-- The normalized-Haar pairing of synthesized characters is the exact coordinate pairing. -/
theorem normalizedCompactHaar_unitaryMatrixDualCharacterSynthesis_pairing
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 (c d:UnitaryMatrixDualCharacterCoefficients G) :
 (∫g,star (unitaryMatrixDualCharacterSynthesis G c g)*
   unitaryMatrixDualCharacterSynthesis G d g ∂normalizedCompactHaarMeasure G) =
 unitaryMatrixDualCharacterCoefficientPairing c d := by
 classical
 let μ := normalizedCompactHaarMeasure G
 letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
 induction c using Finsupp.induction with
 | zero => rw [map_zero];simp [unitaryMatrixDualCharacterCoefficientPairing]
 | @single_add q a c hq ha hc =>
   rw [map_add,unitaryMatrixDualCharacterSynthesis_single]
   have hIntSingle : Integrable (fun g =>
     star (a*unitaryMatrixDualCharacter q g)*
      unitaryMatrixDualCharacterSynthesis G d g) μ := by
    have hcont : Continuous (fun g =>
     star (a*unitaryMatrixDualCharacter q g)*
      unitaryMatrixDualCharacterSynthesis G d g) :=
      ((continuous_unitaryMatrixDualCharacter q).const_mul a).star.mul
       (continuous_unitaryMatrixDualCharacterSynthesis d)
    simpa only [integrableOn_univ] using
     hcont.continuousOn.integrableOn_compact (μ:=μ) isCompact_univ
   have hIntRest : Integrable (fun g =>
     star (unitaryMatrixDualCharacterSynthesis G c g)*
      unitaryMatrixDualCharacterSynthesis G d g) μ := by
    have hcont : Continuous (fun g =>
     star (unitaryMatrixDualCharacterSynthesis G c g)*
      unitaryMatrixDualCharacterSynthesis G d g) :=
      (continuous_unitaryMatrixDualCharacterSynthesis c).star.mul
       (continuous_unitaryMatrixDualCharacterSynthesis d)
    simpa only [integrableOn_univ] using
     hcont.continuousOn.integrableOn_compact (μ:=μ) isCompact_univ
   have hpoint : (fun g =>
     star ((a • unitaryMatrixDualCharacter q+
       unitaryMatrixDualCharacterSynthesis G c) g)*
       unitaryMatrixDualCharacterSynthesis G d g) = fun g =>
      star (a*unitaryMatrixDualCharacter q g)*
       unitaryMatrixDualCharacterSynthesis G d g+
      star (unitaryMatrixDualCharacterSynthesis G c g)*
       unitaryMatrixDualCharacterSynthesis G d g := by
    funext g
    change (starRingEnd ℂ)
      (a * unitaryMatrixDualCharacter q g +
       unitaryMatrixDualCharacterSynthesis G c g) *
        unitaryMatrixDualCharacterSynthesis G d g =
      (starRingEnd ℂ) (a * unitaryMatrixDualCharacter q g) *
        unitaryMatrixDualCharacterSynthesis G d g +
      (starRingEnd ℂ) (unitaryMatrixDualCharacterSynthesis G c g) *
        unitaryMatrixDualCharacterSynthesis G d g
    rw [map_add]
    ring
   rw [hpoint,integral_add hIntSingle hIntRest,hc]
   have hsingle : (∫g,star (a*unitaryMatrixDualCharacter q g)*
      unitaryMatrixDualCharacterSynthesis G d g ∂μ) = star (a)*d q := by
    have ha' := normalizedCompactHaar_unitaryMatrixDualCharacter_analysis d q
    have hfactor : (fun g => star (a*unitaryMatrixDualCharacter q g)*
      unitaryMatrixDualCharacterSynthesis G d g) = fun g =>
      star (a)*(star (unitaryMatrixDualCharacter q g)*
       unitaryMatrixDualCharacterSynthesis G d g) := by
     funext g
     change (starRingEnd ℂ) (a * unitaryMatrixDualCharacter q g) *
       unitaryMatrixDualCharacterSynthesis G d g =
      (starRingEnd ℂ) a *
       ((starRingEnd ℂ) (unitaryMatrixDualCharacter q g) *
        unitaryMatrixDualCharacterSynthesis G d g)
     rw [map_mul]
     ring
    rw [hfactor,integral_const_mul,ha']
   rw [hsingle]
   unfold unitaryMatrixDualCharacterCoefficientPairing
   rw [Finsupp.sum_add_index]
   · simp
   · intro q _
     simp
   · intro q _ x y
     change (starRingEnd ℂ) (x+y)*d q=
       (starRingEnd ℂ) x*d q+(starRingEnd ℂ) y*d q
     rw [map_add]
     ring

/-- The algebraic finite-support central-character subspace of the full function carrier. -/
def unitaryMatrixDualAlgebraicCharacterSubspace
 (G:Type uG) [Group G] [TopologicalSpace G] : Submodule ℂ (G→ℂ) :=
 LinearMap.range (unitaryMatrixDualCharacterSynthesis G)

noncomputable def unitaryMatrixDualCharacterSynthesisEquiv
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
 UnitaryMatrixDualCharacterCoefficients G ≃ₗ[ℂ]
  unitaryMatrixDualAlgebraicCharacterSubspace G :=
 LinearEquiv.ofInjective (unitaryMatrixDualCharacterSynthesis G)
  unitaryMatrixDualCharacterSynthesis_injective

end

end Mathematics
end YangMills
