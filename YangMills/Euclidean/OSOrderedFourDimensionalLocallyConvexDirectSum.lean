/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalLocallyConvexFinalUniversal

/-!
# Exact locally convex direct sum of OS source spaces

OS-I, printed p. 87, equips finite source sequences with the direct-sum topology characterized by:
a linear map into a convex space is continuous exactly when its composite with every natural
coordinate injection is continuous. This module constructs the separate scalar injection and every
positive-arity source injection, proves them continuous through the corresponding empty/singleton
finite stages, decomposes every finite stage as their finite sum, and proves exactly this continuity
criterion for real-locally-convex topological complex-module targets.

Consequently the previously constructed Hausdorff locally convex final topology is now designated
the source-facing locally convex direct-sum topology. The raw topological final topology remains
separately named, and no equality with it is asserted. It also does not prove strict-carrier density/completion, construct
the distinct completed positive-half-space tensor product, state `(E2)`, supply OS-II growth, or
perform reconstruction.
-/

namespace YangMills

noncomputable section

noncomputable local instance sourceAddCommGroupForDirectSum (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.addCommGroup arity

noncomputable local instance sourceModuleForDirectSum (arity : PositiveArity) :
    Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.module arity

noncomputable local instance sourceTopologicalAddGroupForDirectSum (arity : PositiveArity) :
    IsTopologicalAddGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.isTopologicalAddGroup arity

noncomputable local instance sourceContinuousSMulForDirectSum (arity : PositiveArity) :
    ContinuousSMul ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.continuousSMul arity

noncomputable local instance sequenceAddCommGroupForDirectSum :
    AddCommGroup OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup

noncomputable local instance sequenceModuleForDirectSum :
    Module ℂ OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceModule

/-- Exact linear equivalence between source sequences and scalar-plus-dependent-finite-support
coordinates. -/
noncomputable def osPositiveTimeOrderedFourDimensionalSequenceCoordinatesLinearEquiv :
    OSPositiveTimeOrderedFourDimensionalTestSequence ≃ₗ[ℂ]
      OSPositiveTimeOrderedFourDimensionalSequenceCoordinates :=
  Equiv.linearEquiv ℂ osPositiveTimeOrderedFourDimensionalSequenceCoordinatesEquiv

/-- OS-I's natural injection of the separate scalar `f₀`. -/
noncomputable def osPositiveTimeOrderedFourDimensionalScalarNaturalInjection :
    ℂ →ₗ[ℂ] OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceCoordinatesLinearEquiv.symm.toLinearMap.comp
    (LinearMap.inl ℂ ℂ OSPositiveTimeOrderedFourDimensionalSourceDFinsupp)

/-- OS-I's natural injection of one exact positive-arity source component. -/
noncomputable def osPositiveTimeOrderedFourDimensionalSourceNaturalInjection
    (arity : PositiveArity) :
    OSPositiveTimeOrderedFourDimensionalSourceSpace arity →ₗ[ℂ]
      OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceCoordinatesLinearEquiv.symm.toLinearMap.comp
    ((LinearMap.inr ℂ ℂ OSPositiveTimeOrderedFourDimensionalSourceDFinsupp).comp
      (DFinsupp.lsingle arity))

/-- The scalar natural injection retains the scalar exactly. -/
@[simp]
theorem osPositiveTimeOrderedFourDimensionalScalarNaturalInjection_zeroPoint (c : ℂ) :
    (osPositiveTimeOrderedFourDimensionalScalarNaturalInjection c).zeroPoint = c :=
  rfl

/-- The scalar natural injection has zero underlying Schwartz test at every positive arity. -/
@[simp]
theorem osPositiveTimeOrderedFourDimensionalScalarNaturalInjection_component
    (c : ℂ) (arity : PositiveArity) :
    ((osPositiveTimeOrderedFourDimensionalScalarNaturalInjection c).component arity).toSchwartz =
      0 :=
  rfl

/-- A positive-arity natural injection has scalar zero. -/
@[simp]
theorem osPositiveTimeOrderedFourDimensionalSourceNaturalInjection_zeroPoint
    (arity : PositiveArity)
    (f : OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :
    (osPositiveTimeOrderedFourDimensionalSourceNaturalInjection arity f).zeroPoint = 0 :=
  rfl

/-- A positive-arity natural injection recovers the exact injected component. -/
@[simp]
theorem osPositiveTimeOrderedFourDimensionalSourceNaturalInjection_component_same
    (arity : PositiveArity)
    (f : OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :
    (osPositiveTimeOrderedFourDimensionalSourceNaturalInjection arity f).component arity = f := by
  change (osPositiveTimeOrderedFourDimensionalSequenceCoordinatesLinearEquiv
    (osPositiveTimeOrderedFourDimensionalSourceNaturalInjection arity f)).2 arity = f
  rw [show osPositiveTimeOrderedFourDimensionalSourceNaturalInjection arity f =
      osPositiveTimeOrderedFourDimensionalSequenceCoordinatesLinearEquiv.symm
        (0, DFinsupp.single arity f) from rfl,
    osPositiveTimeOrderedFourDimensionalSequenceCoordinatesLinearEquiv.apply_symm_apply]
  simp

/-- Coordinates of a finite-stage extension retain the exact scalar. -/
theorem osPositiveTimeOrderedFourDimensionalStage_coordinates_fst
    (s : Finset PositiveArity) (x : OSPositiveTimeOrderedFourDimensionalStage s) :
    (osPositiveTimeOrderedFourDimensionalSequenceCoordinatesLinearEquiv
      (osPositiveTimeOrderedFourDimensionalStageToSequence s x)).1 = x.1 :=
  rfl

/-- Coordinates of a finite-stage extension retain every zero-extended source component. -/
theorem osPositiveTimeOrderedFourDimensionalStage_coordinates_snd
    (s : Finset PositiveArity) (x : OSPositiveTimeOrderedFourDimensionalStage s)
    (arity : PositiveArity) :
    (osPositiveTimeOrderedFourDimensionalSequenceCoordinatesLinearEquiv
      (osPositiveTimeOrderedFourDimensionalStageToSequence s x)).2 arity =
        osPositiveTimeOrderedFourDimensionalStageComponent s x arity :=
  rfl

/-- Every exact finite-stage extension is the sum of its scalar natural injection and all natural
injections indexed by that finite stage. -/
theorem osPositiveTimeOrderedFourDimensionalStageToSequence_eq_sum_naturalInjections
    (s : Finset PositiveArity) (x : OSPositiveTimeOrderedFourDimensionalStage s) :
    osPositiveTimeOrderedFourDimensionalStageToSequence s x =
      osPositiveTimeOrderedFourDimensionalScalarNaturalInjection x.1 +
        ∑ arity : {a // a ∈ s},
          osPositiveTimeOrderedFourDimensionalSourceNaturalInjection arity.val (x.2 arity) := by
  apply osPositiveTimeOrderedFourDimensionalSequenceCoordinatesLinearEquiv.injective
  rw [map_add, map_sum,
    show osPositiveTimeOrderedFourDimensionalSequenceCoordinatesLinearEquiv
        (osPositiveTimeOrderedFourDimensionalScalarNaturalInjection x.1) =
      (x.1, (0 : OSPositiveTimeOrderedFourDimensionalSourceDFinsupp)) by
        exact osPositiveTimeOrderedFourDimensionalSequenceCoordinatesLinearEquiv.apply_symm_apply _]
  simp_rw [show ∀ arity : {a // a ∈ s},
    osPositiveTimeOrderedFourDimensionalSequenceCoordinatesLinearEquiv
        (osPositiveTimeOrderedFourDimensionalSourceNaturalInjection arity.val (x.2 arity)) =
      (0, DFinsupp.single arity.val (x.2 arity)) by
        intro arity
        exact osPositiveTimeOrderedFourDimensionalSequenceCoordinatesLinearEquiv.apply_symm_apply _]
  apply Prod.ext
  · rw [osPositiveTimeOrderedFourDimensionalStage_coordinates_fst]
    change x.1 = x.1 +
      (LinearMap.fst ℂ ℂ OSPositiveTimeOrderedFourDimensionalSourceDFinsupp)
        (∑ arity : {a // a ∈ s},
          (0, DFinsupp.single arity.val (x.2 arity)))
    rw [map_sum]
    simp
  · apply DFinsupp.ext
    intro arity
    rw [osPositiveTimeOrderedFourDimensionalStage_coordinates_snd]
    change osPositiveTimeOrderedFourDimensionalStageComponent s x arity =
      (LinearMap.snd ℂ ℂ OSPositiveTimeOrderedFourDimensionalSourceDFinsupp)
        ((x.1, 0) + ∑ a : {a // a ∈ s},
          (0, DFinsupp.single a.val (x.2 a))) arity
    rw [map_add, map_sum]
    simp only [LinearMap.snd_apply, zero_add]
    change osPositiveTimeOrderedFourDimensionalStageComponent s x arity =
      (DFinsupp.evalAddMonoidHom arity)
        (∑ a : {a // a ∈ s}, DFinsupp.single a.val (x.2 a))
    rw [map_sum]
    classical
    by_cases hmem : arity ∈ s
    · rw [osPositiveTimeOrderedFourDimensionalStageComponent]
      simp only [dif_pos hmem]
      rw [Finset.sum_eq_single (⟨arity, hmem⟩ : {a // a ∈ s})]
      · change x.2 ⟨arity, hmem⟩ =
          (DFinsupp.single arity (x.2 ⟨arity, hmem⟩)) arity
        simp
      · intro a _ hne
        change (DFinsupp.single a.val (x.2 a)) arity = 0
        rw [DFinsupp.single_apply]
        split_ifs with heq
        · exact False.elim (hne (Subtype.ext heq))
        · rfl
      · simp
    · rw [osPositiveTimeOrderedFourDimensionalStageComponent]
      simp only [dif_neg hmem]
      have hzero : zeroOSPositiveTimeOrderedFourDimensionalSourceTest arity = 0 := by
        apply Subtype.ext
        exact
          (OSPositiveTimeOrderedFourDimensionalSourceSpace.instance_zero_toSchwartz arity).symm
      rw [hzero]
      symm
      apply Finset.sum_eq_zero
      intro a _
      change (DFinsupp.single a.val (x.2 a)) arity = 0
      rw [DFinsupp.single_apply]
      split_ifs with heq
      · exact False.elim (hmem (heq ▸ a.property))
      · rfl

/-- Exact complex-linear map from the scalar into the empty positive-arity stage. -/
noncomputable def osPositiveTimeOrderedFourDimensionalScalarToEmptyStageLinearMap :
    ℂ →ₗ[ℂ] OSPositiveTimeOrderedFourDimensionalStage ∅ where
  toFun c := ⟨c, fun ⟨arity, hmem⟩ => False.elim (by
    have hall : ∀ a : PositiveArity, a ∈ (∅ : Finset PositiveArity) → False :=
      (Finset.forall_mem_empty_iff (fun _ : PositiveArity => False)).mpr trivial
    exact hall arity hmem)⟩
  map_add' _ _ := by
    apply Prod.ext
    · simp
    · funext ⟨arity, hmem⟩
      have hall : ∀ a : PositiveArity, a ∈ (∅ : Finset PositiveArity) → False :=
        (Finset.forall_mem_empty_iff (fun _ : PositiveArity => False)).mpr trivial
      exact False.elim (hall arity hmem)
  map_smul' _ _ := by
    apply Prod.ext
    · simp
    · funext ⟨arity, hmem⟩
      have hall : ∀ a : PositiveArity, a ∈ (∅ : Finset PositiveArity) → False :=
        (Finset.forall_mem_empty_iff (fun _ : PositiveArity => False)).mpr trivial
      exact False.elim (hall arity hmem)

/-- The scalar-to-empty-stage map is continuous. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalScalarToEmptyStage :
    Continuous osPositiveTimeOrderedFourDimensionalScalarToEmptyStageLinearMap := by
  apply Continuous.prodMk continuous_id
  apply continuous_pi
  intro arity
  exact False.elim (by
    have hall : ∀ a : PositiveArity, a ∈ (∅ : Finset PositiveArity) → False :=
      (Finset.forall_mem_empty_iff (fun _ : PositiveArity => False)).mpr trivial
    exact hall arity.val arity.property)

/-- Empty-stage extension is exactly the scalar natural injection. -/
theorem osPositiveTimeOrderedFourDimensionalScalarNaturalInjection_factor
    (c : ℂ) :
    osPositiveTimeOrderedFourDimensionalStageToSequence ∅
        (osPositiveTimeOrderedFourDimensionalScalarToEmptyStageLinearMap c) =
      osPositiveTimeOrderedFourDimensionalScalarNaturalInjection c := by
  apply osPositiveTimeOrderedFourDimensionalSequenceCoordinatesLinearEquiv.injective
  rw [show osPositiveTimeOrderedFourDimensionalSequenceCoordinatesLinearEquiv
      (osPositiveTimeOrderedFourDimensionalScalarNaturalInjection c) =
        (c, (0 : OSPositiveTimeOrderedFourDimensionalSourceDFinsupp)) by
    exact osPositiveTimeOrderedFourDimensionalSequenceCoordinatesLinearEquiv.apply_symm_apply _]
  apply Prod.ext
  · rfl
  · apply DFinsupp.ext
    intro arity
    rfl

/-- Exact complex-linear map from one source space into its singleton finite stage. -/
noncomputable def osPositiveTimeOrderedFourDimensionalSourceToSingletonStageLinearMap
    (arity : PositiveArity) :
    OSPositiveTimeOrderedFourDimensionalSourceSpace arity →ₗ[ℂ]
      OSPositiveTimeOrderedFourDimensionalStage {arity} where
  toFun f := ⟨0, fun a => by
    rcases a with ⟨a, ha⟩
    have h : a = arity := Finset.mem_singleton.mp ha
    subst a
    exact f⟩
  map_add' _ _ := by
    apply Prod.ext
    · simp
    · funext a
      rcases a with ⟨a, ha⟩
      have h : a = arity := Finset.mem_singleton.mp ha
      subst a
      rfl
  map_smul' _ _ := by
    apply Prod.ext
    · simp
    · funext a
      rcases a with ⟨a, ha⟩
      have h : a = arity := Finset.mem_singleton.mp ha
      subst a
      rfl

/-- The source-to-singleton-stage map is continuous. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalSourceToSingletonStage
    (arity : PositiveArity) :
    Continuous (osPositiveTimeOrderedFourDimensionalSourceToSingletonStageLinearMap arity) := by
  apply Continuous.prodMk continuous_const
  apply continuous_pi
  intro a
  rcases a with ⟨a, ha⟩
  have h : a = arity := Finset.mem_singleton.mp ha
  subst a
  exact continuous_id

/-- Singleton-stage extension is exactly the corresponding source natural injection. -/
theorem osPositiveTimeOrderedFourDimensionalSourceNaturalInjection_factor
    (arity : PositiveArity)
    (f : OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :
    osPositiveTimeOrderedFourDimensionalStageToSequence {arity}
        (osPositiveTimeOrderedFourDimensionalSourceToSingletonStageLinearMap arity f) =
      osPositiveTimeOrderedFourDimensionalSourceNaturalInjection arity f := by
  rw [osPositiveTimeOrderedFourDimensionalStageToSequence_eq_sum_naturalInjections]
  simp [osPositiveTimeOrderedFourDimensionalScalarNaturalInjection,
    osPositiveTimeOrderedFourDimensionalSourceNaturalInjection,
    osPositiveTimeOrderedFourDimensionalSourceToSingletonStageLinearMap]

/-- The scalar natural injection is continuous into the locally convex final topology. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalScalarNaturalInjection :
    @Continuous ℂ OSPositiveTimeOrderedFourDimensionalTestSequence inferInstance
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
      osPositiveTimeOrderedFourDimensionalScalarNaturalInjection := by
  letI : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
  rw [show osPositiveTimeOrderedFourDimensionalScalarNaturalInjection =
    osPositiveTimeOrderedFourDimensionalStageToSequence ∅ ∘
      osPositiveTimeOrderedFourDimensionalScalarToEmptyStageLinearMap by
    funext c
    exact (osPositiveTimeOrderedFourDimensionalScalarNaturalInjection_factor c).symm]
  exact (continuous_osPositiveTimeOrderedFourDimensionalStageToLocallyConvexFinal ∅).comp
    continuous_osPositiveTimeOrderedFourDimensionalScalarToEmptyStage

/-- Every positive-arity natural injection is continuous into the locally convex final topology. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalSourceNaturalInjection
    (arity : PositiveArity) :
    @Continuous (OSPositiveTimeOrderedFourDimensionalSourceSpace arity)
      OSPositiveTimeOrderedFourDimensionalTestSequence inferInstance
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
      (osPositiveTimeOrderedFourDimensionalSourceNaturalInjection arity) := by
  letI : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
  rw [show osPositiveTimeOrderedFourDimensionalSourceNaturalInjection arity =
    osPositiveTimeOrderedFourDimensionalStageToSequence {arity} ∘
      osPositiveTimeOrderedFourDimensionalSourceToSingletonStageLinearMap arity by
    funext f
    exact (osPositiveTimeOrderedFourDimensionalSourceNaturalInjection_factor arity f).symm]
  exact (continuous_osPositiveTimeOrderedFourDimensionalStageToLocallyConvexFinal {arity}).comp
    (continuous_osPositiveTimeOrderedFourDimensionalSourceToSingletonStage arity)

/-- Exact OS-I direct-sum continuity criterion: a complex-linear map is continuous exactly when its
scalar and every positive-arity natural-injection composite are continuous. -/
theorem continuous_linearMap_from_osPositiveTimeOrderedFourDimensionalDirectSum_iff
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℂ Y]
    [ContinuousAdd Y] [ContinuousSMul ℂ Y] [LocallyConvexSpace ℝ Y]
    (L : OSPositiveTimeOrderedFourDimensionalTestSequence →ₗ[ℂ] Y) :
    @Continuous OSPositiveTimeOrderedFourDimensionalTestSequence Y
        osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology inferInstance L ↔
      Continuous (L ∘ osPositiveTimeOrderedFourDimensionalScalarNaturalInjection) ∧
      ∀ arity : PositiveArity,
        Continuous (L ∘ osPositiveTimeOrderedFourDimensionalSourceNaturalInjection arity) := by
  letI : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
  constructor
  · intro h
    exact ⟨h.comp continuous_osPositiveTimeOrderedFourDimensionalScalarNaturalInjection,
      fun arity =>
        h.comp (continuous_osPositiveTimeOrderedFourDimensionalSourceNaturalInjection arity)⟩
  · rintro ⟨hscalar, hsource⟩
    apply
      (continuous_linearMap_from_osPositiveTimeOrderedFourDimensionalLocallyConvexFinal_iff L).mpr
    intro s
    rw [show L ∘ osPositiveTimeOrderedFourDimensionalStageToSequence s =
      fun x : OSPositiveTimeOrderedFourDimensionalStage s =>
        (L ∘ osPositiveTimeOrderedFourDimensionalScalarNaturalInjection) x.1 +
          ∑ arity : {a // a ∈ s},
            (L ∘ osPositiveTimeOrderedFourDimensionalSourceNaturalInjection arity.val)
              (x.2 arity) by
      funext x
      simp only [Function.comp_apply]
      rw [osPositiveTimeOrderedFourDimensionalStageToSequence_eq_sum_naturalInjections,
        map_add, map_sum]]
    exact (hscalar.comp continuous_fst).add
      (continuous_finsetSum Finset.univ fun arity _ =>
        (hsource arity.val).comp ((continuous_apply arity).comp continuous_snd))

/-- Source-facing name for the proved Hausdorff locally convex direct-sum topology. The raw
finite-stage final topology remains separately named; equality is not asserted. -/
@[reducible]
noncomputable def osPositiveTimeOrderedFourDimensionalLocallyConvexDirectSumTopology :
    TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology

end

end YangMills
