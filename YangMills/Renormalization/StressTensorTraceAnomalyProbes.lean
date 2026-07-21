/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Renormalization.StressTensorTraceAnomaly

namespace YangMills.Renormalization.StressTensorTraceAnomalyProbes

open YangMills.Minkowski

open scoped BigOperators Manifold ContDiff

noncomputable section

/-- Deliberately wrong four-dimensional Euclidean all-plus contraction, used only by a hostile
probe. -/
def euclideanAllPlusStressTraceOperator
    {liftGroup : Type*}
    [Group liftGroup] [TopologicalSpace liftGroup] [IsTopologicalGroup liftGroup]
    {lift : ProperOrthochronousPoincareLiftData EuclideanDimension.four liftGroup}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    (stress : LocalStressEnergyTensorData family)
    (f : ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four) (psi : D.domain) :
    D.domain :=
  ∑ mu, family.operator (stress.componentLabel mu mu) f psi

private theorem euclideanAllPlusStressTraceOperator_four_expansion
    {liftGroup : Type*}
    [Group liftGroup] [TopologicalSpace liftGroup] [IsTopologicalGroup liftGroup]
    {lift : ProperOrthochronousPoincareLiftData EuclideanDimension.four liftGroup}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    (stress : LocalStressEnergyTensorData family)
    (f : ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four) (psi : D.domain) :
    euclideanAllPlusStressTraceOperator stress f psi =
      family.operator (stress.componentLabel (⟨0, by decide⟩) (⟨0, by decide⟩)) f psi +
      family.operator (stress.componentLabel (⟨1, by decide⟩) (⟨1, by decide⟩)) f psi +
      family.operator (stress.componentLabel (⟨2, by decide⟩) (⟨2, by decide⟩)) f psi +
      family.operator (stress.componentLabel (⟨3, by decide⟩) (⟨3, by decide⟩)) f psi := by
  unfold euclideanAllPlusStressTraceOperator
  change (∑ mu : Fin 4, family.operator (stress.componentLabel mu mu) f psi) = _
  rw [Fin.sum_univ_four]
  rfl

/-- The mostly-minus definition cannot be replaced by all-plus on a test/vector whose spatial
trace is nonzero. -/
theorem euclidean_allPlus_contraction_blocked
    {liftGroup : Type*}
    [Group liftGroup] [TopologicalSpace liftGroup] [IsTopologicalGroup liftGroup]
    {lift : ProperOrthochronousPoincareLiftData EuclideanDimension.four liftGroup}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    (stress : LocalStressEnergyTensorData family)
    (f : ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four) (psi : D.domain)
    (spatial_nonzero :
      family.operator (stress.componentLabel (⟨1, by decide⟩) (⟨1, by decide⟩)) f psi +
      family.operator (stress.componentLabel (⟨2, by decide⟩) (⟨2, by decide⟩)) f psi +
      family.operator (stress.componentLabel (⟨3, by decide⟩) (⟨3, by decide⟩)) f psi ≠ 0) :
    stressTensorTraceOperator stress f psi ≠
      euclideanAllPlusStressTraceOperator stress f psi := by
  intro equality
  rw [stressTensorTraceOperator_four_expansion,
    euclideanAllPlusStressTraceOperator_four_expansion] at equality
  let T0 := family.operator (stress.componentLabel (⟨0, by decide⟩) (⟨0, by decide⟩)) f psi
  let T1 := family.operator (stress.componentLabel (⟨1, by decide⟩) (⟨1, by decide⟩)) f psi
  let T2 := family.operator (stress.componentLabel (⟨2, by decide⟩) (⟨2, by decide⟩)) f psi
  let T3 := family.operator (stress.componentLabel (⟨3, by decide⟩) (⟨3, by decide⟩)) f psi
  change T0 - T1 - T2 - T3 = T0 + T1 + T2 + T3 at equality
  change T1 + T2 + T3 ≠ 0 at spatial_nonzero
  apply spatial_nonzero
  have hneg : -(T1 + T2 + T3) = T1 + T2 + T3 := by
    calc
      -(T1 + T2 + T3) = (T0 - T1 - T2 - T3) - T0 := by abel
      _ = (T0 + T1 + T2 + T3) - T0 := by rw [equality]
      _ = T1 + T2 + T3 := by abel
  have doubledAdd : (T1 + T2 + T3) + (T1 + T2 + T3) = 0 := by
    calc
      (T1 + T2 + T3) + (T1 + T2 + T3) =
          -(T1 + T2 + T3) + (T1 + T2 + T3) :=
        congrArg (fun x => x + (T1 + T2 + T3)) hneg.symm
      _ = 0 := neg_add_cancel _
  have doubledScalar : (2 : ℂ) • (T1 + T2 + T3) = 0 := by
    simpa [two_smul ℂ] using doubledAdd
  exact (smul_eq_zero.mp doubledScalar).resolve_left (by norm_num)

universe uE uG uEB uHB uEP uHP uB uP uH

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {B : Type uB} {P : Type uP} [TopologicalSpace B] [TopologicalSpace P]
    {IB : ModelWithCorners ℝ EB HB} {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : Geometry.PrincipalBundleTorsorData G B P}
    {bundle : Geometry.TopologicalPrincipalBundleData torsor}
    {smoothBundle : Geometry.SmoothPrincipalBundleData
      IB (modelWithCornersSelf ℝ E) IP torsor bundle}
    [FiniteDimensional ℝ EB]
    {liftGroup : Type*} [Group liftGroup] [TopologicalSpace liftGroup]
    [IsTopologicalGroup liftGroup]
    {lift : ProperOrthochronousPoincareLiftData EuclideanDimension.four liftGroup}
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    {gaugeGroup : Geometry.CompactSimpleGaugeGroupData G E}
    {geometry : Classical.EuclideanMetricData (IB := IB) (B := B)}
    {innerData : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)}
    {connection : Geometry.PrincipalConnectionData smoothBundle}
    {exterior : Geometry.PrincipalConnectionExteriorDerivativeData connection}
    {certificate : Geometry.PrincipalCurvatureStructureCertificate smoothBundle connection exterior}
    {interpretation : Observables.CurvatureSquaredLocalObservableInterpretationData
      geometry innerData connection exterior certificate family}
    {stress : LocalStressEnergyTensorData family}
    {freedom : PureYangMillsAsymptoticFreedomData
      EuclideanDimension.four gaugeGroup}
    {normalizedBeta : GroupNormalizedOneLoopBetaData innerData freedom}
    {classicalCoupling : ℝ}
    {reference : ClassicalRunningCouplingReferenceData freedom classicalCoupling}
    {normalization : StressTensorTraceAnomalyNormalizationData
      normalizedBeta reference}
    {selection : PhysicalReducedTraceMatrixElementSelectionData interpretation}

omit [T2Space G] [SecondCountableTopology G] [FiniteDimensional ℝ EB] in
/-- An empty physical selection is impossible because the supplied selected triple is admissible. -/
theorem empty_selection_blocked
    (empty : ∀ f psi phi, ¬ selection.admissible f psi phi) : False :=
  empty selection.selectedTest selection.selectedBra selection.selectedKet
    selection.selected_admissible

omit [T2Space G] [SecondCountableTopology G] [FiniteDimensional ℝ EB] in
/-- The selected witness exposes every physical/on-shell/nonzero-momentum qualification. -/
theorem exact_selected_physical_reduction :
    selection.physicalBra selection.selectedBra ∧
      selection.onShellBra selection.selectedBra ∧
      selection.physicalKet selection.selectedKet ∧
      selection.onShellKet selection.selectedKet ∧
      selection.nonzeroMomentumInsertion selection.selectedTest :=
  selection.selected_physical_conjunction

omit [T2Space G] [SecondCountableTopology G] [FiniteDimensional ℝ EB] in
/-- A selection that declares every bra off shell is rejected by the selected admissible triple. -/
theorem all_bras_offShell_blocked
    (offShell : ∀ ψ, ¬ selection.onShellBra ψ) : False :=
  offShell selection.selectedBra selection.selected_physical_conjunction.2.1

omit [T2Space G] [SecondCountableTopology G] [FiniteDimensional ℝ EB] in
/-- A selection with no nonzero-momentum insertion is rejected. -/
theorem no_nonzeroMomentum_insertion_blocked
    (zeroMomentumOnly : ∀ f, ¬ selection.nonzeroMomentumInsertion f) : False :=
  zeroMomentumOnly selection.selectedTest selection.selected_physical_conjunction.2.2.2.2

omit [FiniteDimensional ℝ EB] in
/-- No unrestricted identity is exposed: if an inadmissible triple witnesses failure, any attempted
all-triples replacement is contradictory. -/
theorem unrestricted_equality_replacement_blocked
    (f : ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four) (psi phi : D.domain)
    (counterexample : ¬ selection.admissible f psi phi ∧
      @inner ℂ H _ psi.val (stressTensorTraceOperator stress f phi).val ≠
        (normalization.coefficient : ℂ) *
          @inner ℂ H _ psi.val
            (family.operator
              (interpretation.quantumLabel Observables.BasicCurvatureObservableTag.curvatureSquared)
              f phi).val)
    (unrestricted : ∀
      (f : ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four)
      (psi phi : D.domain),
      @inner ℂ H _ psi.val (stressTensorTraceOperator stress f phi).val =
        (normalization.coefficient : ℂ) *
          @inner ℂ H _ psi.val
            (family.operator
              (interpretation.quantumLabel Observables.BasicCurvatureObservableTag.curvatureSquared)
              f phi).val) : False :=
  counterexample.2 (unrestricted f psi phi)

omit [T2Space G] [SecondCountableTopology G] [FiniteDimensional ℝ EB] in
/-- The exact interpreted F-squared label cannot collapse to the same family's unit label. -/
theorem unit_curvatureSquared_label_blocked
    (collapse : interpretation.quantumLabel
      Observables.BasicCurvatureObservableTag.curvatureSquared = family.unitLabel) : False :=
  interpretation.curvatureSquaredLabel_ne_unit collapse

omit [FiniteDimensional ℝ EB] in
/-- The admissible identity is statically tied to the exact interpreted F-squared label. -/
theorem exact_curvatureSquared_label_used
    (data : StressTensorTraceAnomalyData interpretation stress normalization selection)
    (f : ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four) (psi phi : D.domain)
    (admissible : selection.admissible f psi phi) :
    @inner ℂ H _ psi.val (stressTensorTraceOperator stress f phi).val =
      (normalization.coefficient : ℂ) *
        @inner ℂ H _ psi.val
          (family.operator
            (interpretation.quantumLabel Observables.BasicCurvatureObservableTag.curvatureSquared)
            f phi).val :=
  data.admissible_weak_matrixElement_trace_anomaly f psi phi admissible

omit [FiniteDimensional ℝ EB] in
/-- A disconnected replacement label cannot satisfy the same admissible law when one admissible
weak matrix element distinguishes it from the exact F-squared operator. -/
theorem disconnected_curvatureSquared_label_blocked
    (data : StressTensorTraceAnomalyData interpretation stress normalization selection)
    (replacementLabel : family.Label)
    (replacementIdentity : ∀ f psi phi, selection.admissible f psi phi →
      @inner ℂ H _ psi.val (stressTensorTraceOperator stress f phi).val =
        (normalization.coefficient : ℂ) *
          @inner ℂ H _ psi.val (family.operator replacementLabel f phi).val)
    (f : ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four) (psi phi : D.domain)
    (admissible : selection.admissible f psi phi)
    (distinguished :
      @inner ℂ H _ psi.val
          (family.operator
            (interpretation.quantumLabel Observables.BasicCurvatureObservableTag.curvatureSquared)
            f phi).val ≠
        @inner ℂ H _ psi.val (family.operator replacementLabel f phi).val) : False := by
  apply distinguished
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr normalization.coefficient_ne_zero)
  exact (data.admissible_weak_matrixElement_trace_anomaly f psi phi admissible).symm.trans
    (replacementIdentity f psi phi admissible)

omit [FiniteDimensional ℝ EB] in
/-- The selected physical F-squared matrix element prevents collapse of the direct trace. -/
theorem nonzero_trace_collapse_blocked
    (data : StressTensorTraceAnomalyData interpretation stress normalization selection)
    (collapse : ∀ f phi, stressTensorTraceOperator stress f phi = 0) : False :=
  data.selected_traceOperator_ne_zero
    (collapse selection.selectedTest selection.selectedKet)

end

end YangMills.Renormalization.StressTensorTraceAnomalyProbes
