/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalFullQuery
public import LeanCanny.Encoding.CoefficientMarkedRecordFullRealization
public import LeanCanny.Encoding.CoefficientMarkedRecordRootBranches
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalIncidence
/-! # Literal installed whole critical scan at its own full tuple -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordCriticalFullSemantics
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem scalar_evaluation (r : ℕ) :
    (Int.castRingHom ℝ).comp (evalRingHom ((2 : ℤ)^r)) = SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^r) := by
  apply Polynomial.ringHom_ext
  · intro a; simp [SymbolicScaledSquarefree.scalarEvaluation]
  · simp [SymbolicScaledSquarefree.scalarEvaluation]

private theorem count_at (P : IntegralCriticalHistoryTask.Parameters) (T : IntegralMixedHeaderTablesBits.Tables)
    (key : List Bool → List Bool) (q : List Bool) :
    IntegralMixedFramedCriticalGuardBits.count P T key q =
      IntegralMixedFramedCriticalGuardBits.count P T (fun _ => key q) [] := rfl

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralMixedFramedCriticalGuardBits.atKey
  IntegralMixedFramedPhysicalIndex.prefixArity IntegralMixedFramedPhysicalIndex.scalarColumn
  UniformIntegralPowerSchedule.birth UniformIntegralPowerSchedule.physical

private theorem polynomial_at (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (key : List Bool → List Bool) (stage : List Bool → ℕ) (q : List Bool) :
    HEq (IntegralMixedFramedCriticalGuardBits.polynomial P D H T key stage q)
      (IntegralMixedFramedCriticalGuardBits.polynomial P D H T (fun _ => key q) (fun _ => stage q) []) :=
  (heq_of_eq (IntegralFramedPhysicalCriticalGuardTest.polynomial_reindex P D H T (fun _ => q) key stage [])).symm

private theorem polynomial_key (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (u v : List Bool) (h : u = v) (b : ℕ) :
    HEq (IntegralMixedFramedCriticalGuardBits.polynomial P D H T (fun _ => u) (fun _ => b) [])
      (IntegralMixedFramedCriticalGuardBits.polynomial P D H T (fun _ => v) (fun _ => b) []) := by
  cases h
  rfl

private theorem polynomial_stage (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (key : List Bool) (u v : ℕ) (h : u = v) :
    HEq (IntegralMixedFramedCriticalGuardBits.polynomial P D H T (fun _ => key) (fun _ => u) [])
      (IntegralMixedFramedCriticalGuardBits.polynomial P D H T (fun _ => key) (fun _ => v) []) := by
  cases h
  rfl

private theorem source_polynomial (S : SquareSampleInput.Inputs) (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (L F C : List Bool → ℕ)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (key : List Bool → List Bool)
    (hcount : ∀ c d, IntegralMixedFramedCriticalGuardBits.count P T
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum key) (pair c d) = S.count c) (c d : List Bool) :
    HEq ((IntegralFramedPhysicalCriticalGuardTest.source S P D H T L F C hs key
      IntegralFramedPhysicalCriticalGuardScan.stage hcount).polynomial c d)
      (IntegralMixedFramedCriticalGuardBits.polynomial P D H T
        (IntegralFramedPhysicalCriticalGuardTest.keyDatum key) IntegralFramedPhysicalCriticalGuardScan.stage (pair c d)) := HEq.rfl

private theorem point_heq {N M : ℕ} (h : 0 + N = M) (z : Fin M → ℝ) :
    HEq (fun j : Fin N => z (Fin.cast h (FixedWidthSuffixLiftBits.shift 0 j))) z := by
  have hc : N = M := (Nat.zero_add N).symm.trans h
  cases hc
  apply heq_of_eq
  funext j
  apply congrArg z
  apply Fin.ext
  change 0 + j.val = j.val
  exact Nat.zero_add _

private theorem eval_heq {N M : ℕ} (h : N = M)
    (p : MvPolynomial (Fin N) ℤ) (q : MvPolynomial (Fin M) ℤ) (hp : HEq p q)
    (z : Fin N → ℝ) (w : Fin M → ℝ) (hz : HEq z w) :
    p.eval₂ (Int.castRingHom ℝ) z = q.eval₂ (Int.castRingHom ℝ) w := by
  cases h
  cases eq_of_heq hp
  cases eq_of_heq hz
  rfl

private noncomputable def inputData (B : IntegralFramedBankQuery.Bank) (c : List Bool) :=
  CoefficientMarkedRecordRowBounds.samplerData B.parameters B.plan B.data (B.key c)

private theorem roots_of_data (B : IntegralFramedBankQuery.Bank) (c : List Bool)
    (E : CoefficientMarkedRecordRows.Data ℤ) (he : E = inputData B c)
    (w : List Bool) (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w) :
    ∃ z : Fin E.count → ℝ, (∀ i, (E.rows i).eval₂ (Int.castRingHom ℝ) z = 0) ∧
      HEq (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hv).val z := by
  cases he
  exact ⟨(SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hv).val,
    (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hv).property, HEq.rfl⟩

private theorem full_key (n : List Bool → ℕ) (ctx : List Bool) :
    CoefficientMarkedRecordRowLayout.key (n := n) ctx (IntegralMixedCausalRecordPlanBits.count ctx) [] =
      IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n (IntegralMixedPhysicalMarkedTest.sampleContext ctx) := by
  unfold CoefficientMarkedRecordRowLayout.key IntegralMixedAuxiliaryMarkedRecordPlan.bankKey
  rw [CoefficientMarkedPreludeActual.indices_length]
  simp only [IntegralMixedPhysicalMarkedTest.sampleContext, pairFst_pair]
  rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)

private theorem actual_metadata (ctx : List Bool) (b : ℕ) :
    CoefficientMarkedRecordCriticalQuery.metadata hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) [] b =
      CoefficientCriticalCorrelationQuery.nativeMetadata (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
        (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
        ((IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).key (IntegralMixedPhysicalMarkedTest.sampleContext ctx)) b := by
  have hh := CoefficientMarkedRecordCriticalQuery.metadata_eq hn ht ha ctx hR
    (IntegralMixedCausalRecordPlanBits.count ctx) [] b
  rw [full_key] at hh
  exact hh

private theorem native_input_count (ctx : List Bool) (b : ℕ) :
    (CoefficientCriticalCorrelationQuery.nativeMetadata (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
      (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
      ((IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).key (IntegralMixedPhysicalMarkedTest.sampleContext ctx)) b).count =
      (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false).count (IntegralMixedPhysicalMarkedTest.sampleContext ctx) := by
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  let T := IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false
  let c := IntegralMixedPhysicalMarkedTest.sampleContext ctx
  have hh := count_at B.parameters T (IntegralFramedPhysicalCriticalGuardTest.keyDatum B.key) (pair c [])
  simp only [IntegralFramedPhysicalCriticalGuardTest.keyDatum, pairFst_pair] at hh
  exact hh.symm.trans (IntegralMixedPhysicalGuardScan.count_eq hn ht ha hR false c [])

private theorem native_data_full (ctx : List Bool) :
    CoefficientMarkedRecordRowBounds.certifiedIndexed hn ht ha ctx hR (IntegralMixedCausalRecordPlanBits.count ctx) [] =
      inputData (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false) (IntegralMixedPhysicalMarkedTest.sampleContext ctx) := by
  change CoefficientMarkedRecordRowBounds.samplerData
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
    (CoefficientMarkedRecordRowLayout.key (n := n) ctx (IntegralMixedCausalRecordPlanBits.count ctx) []) =
    CoefficientMarkedRecordRowBounds.samplerData
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n (IntegralMixedPhysicalMarkedTest.sampleContext ctx))
  exact congrArg _ (full_key n ctx)

theorem full_count (ctx : List Bool) :
    (CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count =
      (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false).count (IntegralMixedPhysicalMarkedTest.sampleContext ctx) :=
  (CoefficientMarkedRecordCriticalFullQuery.count_eq hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] 0).symm.trans
    ((congrArg CoefficientCriticalCorrelationQuery.Metadata.count (actual_metadata hn ht ha hR ctx 0)).trans
      (native_input_count hn ht ha hR ctx 0))

theorem full_length (ctx : List Bool) :
    IntegralMixedFramedHistoryFamilyBits.prefixLength (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
      ((IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).key (IntegralMixedPhysicalMarkedTest.sampleContext ctx)) =
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx := by
  change IntegralMixedFramedHistoryFamilyBits.prefixLength
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
    (IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n (IntegralMixedPhysicalMarkedTest.sampleContext ctx)) = _
  have hh := IntegralMixedAuxiliaryMarkedRecordPlan.bank_count hn ht ha hR (IntegralMixedPhysicalMarkedTest.sampleContext ctx)
  rw [IntegralMixedFramedBankSnapshotBits.count_prefix] at hh
  simpa only [IntegralMixedPhysicalMarkedTest.sampleContext, pairFst_pair] using hh

noncomputable def Zeros (ctx : List Bool) (β : ℝ)
    (z : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count → ℝ) : Prop :=
  ∀ b < IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx,
    (CoefficientMarkedRecordCriticalFullQuery.polynomial hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] b).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation β) z = 0

noncomputable def nativeValue (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w) (b : ℕ) :=
  ((IntegralMixedPhysicalCriticalIncidence.source hn ht ha hR false).polynomial
    (IntegralMixedPhysicalMarkedTest.sampleContext ctx) (List.replicate b true)).eval₂ (Int.castRingHom ℝ)
    (fun j => (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hv).val
      (Fin.cast ((IntegralMixedPhysicalCriticalIncidence.source hn ht ha hR false).dimension
        (IntegralMixedPhysicalMarkedTest.sampleContext ctx) (List.replicate b true)) (FixedWidthSuffixLiftBits.shift 0 j)))

attribute [local irreducible] IntegralMixedFramedCriticalGuardBits.polynomial
  IntegralMixedSourceIntegerRecordAppend.plan CoefficientMarkedRecordRows.symbolic

private theorem source_raw (ctx : List Bool) (b : ℕ) :
    HEq ((IntegralMixedPhysicalCriticalIncidence.source hn ht ha hR false).polynomial
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) (List.replicate b true))
      (IntegralMixedFramedCriticalGuardBits.polynomial
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
        (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).plan (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).data
        (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
        (fun _ => (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).key (IntegralMixedPhysicalMarkedTest.sampleContext ctx))
        (fun _ => b) []) := by
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  let T := IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false
  let c := IntegralMixedPhysicalMarkedTest.sampleContext ctx
  let d := List.replicate b true
  let k := IntegralFramedPhysicalCriticalGuardTest.keyDatum B.key
  let j := IntegralFramedPhysicalCriticalGuardScan.stage
  have hk : k (pair c d) = B.key c := congrArg B.key (pairFst_pair c d)
  have hj : j (pair c d) = b := by
    simp only [j, IntegralFramedPhysicalCriticalGuardScan.stage, pairSnd_pair, d, List.length_replicate]
  have hp := source_polynomial (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
    B.parameters B.plan B.data T B.nodes B.factor B.seed B.bounds B.key
    (IntegralMixedPhysicalGuardScan.count_eq hn ht ha hR false) c d
  have hh := polynomial_at B.parameters B.plan B.data T k j (pair c d)
  have hkey := polynomial_key B.parameters B.plan B.data T (k (pair c d)) (B.key c) hk (j (pair c d))
  have hstage := polynomial_stage B.parameters B.plan B.data T (B.key c) (j (pair c d)) b hj
  exact hp.trans (hh.trans (hkey.trans hstage))

theorem value_eq (ctx : List Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx)
    (w : List Bool) (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w)
    (z : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count → ℝ)
    (hz : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hv).val z) (b : ℕ) :
    nativeValue hn ht ha hR ctx w hv b =
      (CoefficientMarkedRecordCriticalFullQuery.polynomial hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] b).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^R ctx)) z := by
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  let T := IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false
  let c := IntegralMixedPhysicalMarkedTest.sampleContext ctx
  let U := IntegralMixedPhysicalCriticalIncidence.source hn ht ha hR false
  have hs := CoefficientMarkedRecordCriticalFullQuery.specializes hn ht ha ctx hR
    (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] b hlarge
  have hk := polynomial_key B.parameters B.plan B.data T
    (CoefficientMarkedRecordRowLayout.key (n := n) ctx (IntegralMixedCausalRecordPlanBits.count ctx) [])
    (B.key c) (full_key n ctx) b
  have hp := hs.trans (hk.trans (source_raw hn ht ha hR ctx b).symm)
  have hd : 0 + U.arity c (List.replicate b true) = (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false).count c :=
    U.dimension c (List.replicate b true)
  have hc := (full_count hn ht ha hR ctx).trans ((Nat.zero_add _).symm.trans hd).symm
  have hpoint := (point_heq hd
    (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) c w hv).val).trans hz
  have he := eval_heq hc _ _ hp z _ hpoint.symm
  rw [MvPolynomial.eval₂_map, scalar_evaluation] at he
  exact he.symm

theorem packet_iff (ctx : List Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx)
    (w : List Bool) (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w)
    (z : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count → ℝ)
    (hz : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hv).val z) :
    pair ctx w ∈ IntegralMixedPhysicalGuardScan.language hn ht ha hR false ↔ Zeros hn ht ha ctx ((2 : ℝ)^R ctx) z := by
  rw [IntegralMixedPhysicalCriticalIncidence.packet_iff hn ht ha hR false ctx w hv]
  change (∀ b < IntegralMixedFramedHistoryFamilyBits.prefixLength
    (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
    ((IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).key (IntegralMixedPhysicalMarkedTest.sampleContext ctx)),
      nativeValue hn ht ha hR ctx w hv b = 0) ↔ _
  rw [full_length]
  unfold Zeros
  exact forall_congr' (fun b => forall_congr' (fun _ => by rw [value_eq hn ht ha hR ctx hlarge w hv z hz b]))

/-- Every valid installed word belongs to the actual symbolic root system;
the formal tuple and ALL raw readbacks are derived, not supplied. -/
theorem rows_of_word (ctx : List Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx)
    (w : List Bool) (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w) :
    ∃ z : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count → ℝ,
      CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl ((2 : ℝ)^R ctx) z ∧
      HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
        (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hv).val z := by
  have hd := (CoefficientMarkedRecordRowBounds.map_certified hn ht ha ctx hR
    (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl [] hlarge).trans (native_data_full hn ht ha hR ctx)
  obtain ⟨z, hz, he⟩ := roots_of_data (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false)
    (IntegralMixedPhysicalMarkedTest.sampleContext ctx)
    (CoefficientMarkedRecordRows.map (evalRingHom ((2 : ℤ)^R ctx))
      (CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl)) hd w hv
  change Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count → ℝ at z
  refine ⟨z, ?_, he⟩
  intro i
  have hi := hz i
  change (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))
    ((CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).rows i)).eval₂
      (Int.castRingHom ℝ) z = 0 at hi
  rw [MvPolynomial.eval₂_map, scalar_evaluation] at hi
  exact hi

theorem exists_scan_word (ctx : List Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx)
    (z : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl).count → ℝ)
    (hrow : CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl
      ((2 : ℝ)^R ctx) z) (hzero : Zeros hn ht ha ctx ((2 : ℝ)^R ctx) z) :
    ∃ w, ∃ hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w,
      w.length = SquareSampleCompleteVertices.width (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
        (IntegralMixedPhysicalMarkedTest.sampleContext ctx) ∧
      HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
        (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hv).val z ∧
      pair ctx w ∈ IntegralMixedPhysicalGuardScan.language hn ht ha hR false := by
  obtain ⟨w, hv, hl, he⟩ := CoefficientMarkedRecordFullRealization.exists_word hn ht ha ctx hR hlarge z hrow
  exact ⟨w, hv, hl, he, (packet_iff hn ht ha hR ctx hlarge w hv z he).mpr hzero⟩

end LeanCanny.Encoding.CoefficientMarkedRecordCriticalFullSemantics
