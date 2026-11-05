/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalFullQuery
public import LeanCanny.Encoding.CoefficientMarkedCriticalIntervalQuery
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalCorrelation
/-! # Last critical-correlation truth on the SAME prepared child tuple -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedCriticalCorrelationIncidence
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
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum key) (pair c d) = S.count c) (stage : List Bool → ℕ) (c d : List Bool) :
    HEq ((IntegralFramedPhysicalCriticalGuardTest.source S P D H T L F C hs key
      stage hcount).polynomial c d)
      (IntegralMixedFramedCriticalGuardBits.polynomial P D H T
        (IntegralFramedPhysicalCriticalGuardTest.keyDatum key) stage (pair c d)) := HEq.rfl

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

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)

noncomputable def polynomial (q : List Bool) :=
  CoefficientMarkedRecordCriticalFullQuery.polynomial hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
    (IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) le_rfl q
    (IntegralMixedPhysicalCriticalPrefixes.birth n false false q)

private theorem actual_metadata (q : List Bool) (b : ℕ) :
    CoefficientMarkedRecordCriticalQuery.metadata hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) q b =
      CoefficientCriticalCorrelationQuery.nativeMetadata (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
        (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
        (IntegralMixedPhysicalCriticalPrefixes.key n false true q) b := by
  have hh := CoefficientMarkedRecordCriticalQuery.metadata_eq hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) hR
    (IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) q b
  rw [← CoefficientMarkedCriticalIntervalQuery.child_key n q] at hh
  exact hh

private theorem native_input_count (q : List Bool) (b : ℕ) :
    (CoefficientCriticalCorrelationQuery.nativeMetadata (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false).parameters
      (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
      (IntegralMixedPhysicalCriticalPrefixes.key n false true q) b).count =
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false true).count q := by
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  let T := IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false
  let key := IntegralMixedPhysicalCriticalPrefixes.key n false true
  have hh := count_at B.parameters T (IntegralFramedPhysicalCriticalGuardTest.keyDatum key) (pair q [])
  simp only [IntegralFramedPhysicalCriticalGuardTest.keyDatum, pairFst_pair] at hh
  exact hh.symm.trans (IntegralMixedPhysicalCriticalInterval.guard_count hn ht ha hR false q [])

private theorem full_count (q : List Bool) :
    (CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) le_rfl).count =
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false true).count q := by
  have hc := CoefficientMarkedRecordCriticalFullQuery.count_eq hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
    (IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) le_rfl q 0
  have hm := congrArg CoefficientCriticalCorrelationQuery.Metadata.count (actual_metadata hn ht ha hR q 0)
  exact hc.symm.trans (hm.trans (native_input_count hn ht ha hR q 0))

attribute [local irreducible] IntegralMixedFramedCriticalGuardBits.polynomial
  IntegralMixedSourceIntegerRecordAppend.plan CoefficientMarkedRecordRows.symbolic polynomial

private theorem source_raw (q : List Bool) :
    let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
    let S := IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false true
    let T := IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false
    let key := IntegralMixedPhysicalCriticalPrefixes.key n false true
    let stage := IntegralMixedPhysicalCriticalInterval.stage n false
    HEq ((IntegralFramedPhysicalCriticalGuardTest.source S B.parameters B.plan B.data T B.nodes B.factor B.seed B.bounds
      key stage (IntegralMixedPhysicalCriticalInterval.guard_count hn ht ha hR false)).polynomial q [])
      (IntegralMixedFramedCriticalGuardBits.polynomial B.parameters B.plan B.data T
        (fun _ => key q) (fun _ => IntegralMixedPhysicalCriticalPrefixes.birth n false false q) []) := by
  dsimp only
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  let T := IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false
  let key := IntegralMixedPhysicalCriticalPrefixes.key n false true
  let k := IntegralFramedPhysicalCriticalGuardTest.keyDatum key
  let j := IntegralMixedPhysicalCriticalInterval.stage n false
  have hk : k (pair q []) = key q := congrArg key (pairFst_pair q [])
  have hj : j (pair q []) = IntegralMixedPhysicalCriticalPrefixes.birth n false false q :=
    congrArg (IntegralMixedPhysicalCriticalPrefixes.birth n false false) (pairFst_pair q [])
  have hp := source_polynomial (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false true)
    B.parameters B.plan B.data T B.nodes B.factor B.seed B.bounds key
    (IntegralMixedPhysicalCriticalInterval.guard_count hn ht ha hR false) j q []
  have hh := polynomial_at B.parameters B.plan B.data T k j (pair q [])
  have hkey := polynomial_key B.parameters B.plan B.data T (k (pair q [])) (key q) hk (j (pair q []))
  have hstage := polynomial_stage B.parameters B.plan B.data T (key q) (j (pair q []))
    (IntegralMixedPhysicalCriticalPrefixes.birth n false false q) hj
  exact hp.trans (hh.trans (hkey.trans hstage))

/-- The appended-stage native test evaluates the constructed actual query at
the SAME complete child raw tuple. No Active or geometric premise is supplied. -/
theorem value_eq (q : List Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root q) ≤ R (IntegralMixedPhysicalCriticalQuery.root q))
    (w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false true) q w)
    (z : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) le_rfl).count → ℝ)
    (hz : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false true) q w hw).val z) :
    IntegralMixedPhysicalCriticalInterval.correlation hn ht ha hR false (pair q w) =
      InfinitesimalSign.encode (SignType.sign ((polynomial hn ht ha q).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation ((2 : ℝ)^R (IntegralMixedPhysicalCriticalQuery.root q))) z)) := by
  let B := IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
  let T := IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false
  let S := IntegralMixedPhysicalCriticalPrefixes.input hn ht ha hR false true
  let key := IntegralMixedPhysicalCriticalPrefixes.key n false true
  let stage := IntegralMixedPhysicalCriticalInterval.stage n false
  let U := IntegralFramedPhysicalCriticalGuardTest.source S B.parameters B.plan B.data T B.nodes B.factor B.seed B.bounds
    key stage (IntegralMixedPhysicalCriticalInterval.guard_count hn ht ha hR false)
  have hs := CoefficientMarkedRecordCriticalFullQuery.specializes hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) hR
    (IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) le_rfl q
    (IntegralMixedPhysicalCriticalPrefixes.birth n false false q) hlarge
  have hk := polynomial_key B.parameters B.plan B.data T
    (CoefficientMarkedRecordRowLayout.key (n := n) (IntegralMixedPhysicalCriticalQuery.root q)
      (IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) q)
    (key q) (CoefficientMarkedCriticalIntervalQuery.child_key n q).symm (IntegralMixedPhysicalCriticalPrefixes.birth n false false q)
  have hp := hs.trans (hk.trans (source_raw hn ht ha hR q).symm)
  have hd : 0 + U.arity q [] = S.count q := U.dimension q []
  have hc := (full_count hn ht ha hR q).trans ((Nat.zero_add _).symm.trans hd).symm
  have hpoint := (point_heq hd (SquareSampleCompleteVertices.candidate S q w hw).val).trans hz
  have he := eval_heq hc _ _ hp z _ hpoint.symm
  rw [MvPolynomial.eval₂_map, scalar_evaluation] at he
  have hh := IntegralFramedPhysicalCriticalGuardTest.packet S B.parameters B.plan B.data T
    B.nodes B.factor B.seed B.bounds key stage (IntegralMixedPhysicalCriticalInterval.guard_count hn ht ha hR false)
    q w [] hw
  unfold IntegralMixedPhysicalCriticalInterval.correlation
  simp only [Function.comp_apply, IntegralMixedPhysicalCriticalInterval.probe]
  unfold polynomial
  exact hh.trans (congrArg (fun v : ℝ => InfinitesimalSign.encode (SignType.sign v)) he.symm)

end LeanCanny.Encoding.CoefficientMarkedCriticalCorrelationIncidence
