/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualMonomialCoefficientTransport
public import LeanCanny.Algebra.IntegralMixedVirtualMonomialHeightTransport
public import LeanCanny.Algebra.IntegralMixedVirtualDenominatorValue
public import LeanCanny.Algebra.IntegralMixedVirtualNativeFactorPower
public import LeanCanny.Algebra.IntegralMixedVirtualMonomialRequests
public import LeanCanny.Algebra.IntegralMixedVirtualLowerCanonical
/-! # Actual guarded replies for charged virtual monomial factors -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits NativeControllerBranch
open IntegralMonomialTermBits (position packet coefficientQuery heightQuery)
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev monomialProgram (P : Parameters) (F : Family) :=
  IntegralMixedVirtualMonomialRequestBits.program (monomialSource P F)
    (IntegralCriticalFlatGenericMonomialBits.coefficientTask P)
    (IntegralCriticalFlatFactorQuery.writer P .clearedHeight) (IntegralMixedScalarQueryBits.commonDenominator P)
noncomputable abbrev monomialInput (P : Parameters) (F : Family) :=
  IntegralCriticalFlatGenericMonomialBits.input P (monomialSource P F)

abbrev MonomialRepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  (position (monomialInput P F q) = 0 →
    reply (IntegralCriticalFlatGenericMonomialBits.coefficientTask P (coefficientQuery (monomialInput P F q))) =
      IntegralMixedVirtualMonomialLeafBits.coefficient P F
        (IntegralCriticalFlatGenericMonomialBits.coefficientTask P (coefficientQuery (monomialInput P F q)))) ∧
  (IntegralMixedVirtualMonomialRequestBits.heightRequest (monomialSource P F) (monomialInput P F q) →
    reply (IntegralCriticalFlatFactorQuery.writer P .clearedHeight (heightQuery (monomialInput P F q))) =
      height P F (IntegralCriticalFlatFactorQuery.writer P .clearedHeight (heightQuery (monomialInput P F q)))) ∧
  (IntegralMixedVirtualMonomialRequestBits.denominatorRequest (monomialSource P F) (monomialInput P F q) →
    reply (IntegralMixedScalarQueryBits.commonDenominator P q) =
      IntegralMixedVirtualDenominatorBits.value P F (IntegralMixedScalarQueryBits.commonDenominator P q))

theorem monomial_value_at (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (he : MonomialRepliesAt P F reply q) :
    (monomialProgram P F).value reply (monomialInput P F q) = IntegralMixedVirtualFactorBits.monomial P F q := by
  let r := IntegralCriticalFlatGenericMonomialBits.index P (monomialSource P F) .row q
  let t := IntegralCriticalFlatGenericMonomialBits.index P (monomialSource P F) .col q
  let s := get P .slot8 q
  have HC : position (packet q s r.val t.val) = 0 →
      reply (IntegralCriticalFlatGenericMonomialBits.coefficientTask P (coefficientQuery (packet q s r.val t.val))) =
        (monomialAccess P a F h).coefficient (coefficientQuery (packet q s r.val t.val)) := by
    intro hz
    have HS : get P .slot8 q = 0 := by simpa only [IntegralMonomialTermBits.position_packet] using hz
    refine (he.1 hz).trans ?_
    change IntegralMixedVirtualMonomialLeafBits.coefficient P F
      (IntegralCriticalFlatGenericMonomialBits.coefficientTask P (coefficientQuery (packet q s r.val t.val))) = _
    rw [IntegralMonomialTermBits.coefficientQuery_packet]
    exact IntegralMixedVirtualMonomialLeafBits.coefficient_child P a F h g q hv r t HS
  have HH : IntegralMixedVirtualMonomialRequestBits.heightRequest (monomialSource P F) (packet q s r.val t.val) →
      reply (IntegralCriticalFlatFactorQuery.writer P .clearedHeight (heightQuery (packet q s r.val t.val))) =
        (monomialAccess P a F h).height (heightQuery (packet q s r.val t.val)) := by
    intro hh
    refine (he.2.1 hh).trans ?_
    change height P F (IntegralCriticalFlatFactorQuery.writer P .clearedHeight
      (heightQuery (packet q s r.val t.val))) = _
    rw [IntegralMonomialTermBits.heightQuery_packet]
    exact IntegralMixedVirtualMonomialHeightBits.height_child P a F h g q hv (s - 2) r t
      ((Nat.sub_le _ _).trans (get_le P .slot8 q))
  have HD : IntegralMixedVirtualMonomialRequestBits.denominatorRequest (monomialSource P F) (packet q s r.val t.val) →
      reply (IntegralMixedScalarQueryBits.commonDenominator P (pairFst (packet q s r.val t.val))) =
        (monomialAccess P a F h).denominator (pairFst (packet q s r.val t.val)) := by
    intro hd
    simp only [packet, pairFst_pair]
    exact (he.2.2 hd).trans ((IntegralMixedVirtualDenominatorBits.scalar_child P F q).trans
      (IntegralMixedVirtualDenominatorBits.monomial_value P a F h q))
  have H := IntegralMixedVirtualMonomialRequestBits.actual_value_at (monomialSource P F) (monomialAccess P a F h)
    (IntegralCriticalFlatGenericMonomialBits.coefficientTask P) (IntegralCriticalFlatFactorQuery.writer P .clearedHeight)
    (IntegralMixedScalarQueryBits.commonDenominator P) reply q s r t HC HH HD
  exact H.trans (IntegralCriticalActualLowMatrixModel.entryBits_fin
    (IntegralCriticalActualFactorModel.factorMatrix (monomialSource P F) q s) r t).symm

noncomputable def monomialMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  ofPreparedSingleCall (monomialProgram P F)
    ((monomialProgram P F).certificates (IntegralMixedVirtualMonomialRequestBits.controls _ (monomialAccess P a F h) _ _ _
      (IntegralCriticalFlatGenericMonomialBits.coefficientTask_FP P a)
      (IntegralCriticalFlatFactorQuery.writer_FP P a .clearedHeight)
      (IntegralMixedScalarQueryBits.scalarQuery_FP P a .derivativeCoefficient)))
    (monomialInput P F) (IntegralCriticalFlatGenericMonomialBits.input_FP P a (monomialSource P F) (monomialAccess P a F h))
    (selectedValid P .monomialFactor) (selectedValid_FP P a .monomialFactor)
    (IntegralMixedVirtualFactorBits.monomial P F) (heightBound P) (heightBound_unary P a)

theorem monomial_factor_frame (P : Parameters) (p : Phase) (z : List Bool) (hp : p.code < phase (pairFst z)) :
    IntegralMixedRoutineTaskBits.Frame P (pairFst z) (IntegralCriticalFlatFactorQuery.writer P p z) := by
  apply IntegralMixedMatrixFrames.frame_of_ordinary
  · unfold IntegralMixedRoutineTaskBits.routine
    rw [IntegralCriticalFlatFactorQuery.writer_other P p z .slot14 (by decide) (by decide) (by decide)]
  · exact ⟨IntegralCriticalFlatFactorQuery.writer_root P p z, IntegralCriticalFlatFactorQuery.writer_length P p z,
      IntegralCriticalFlatFactorQuery.writer_lower_rank P p z hp⟩

theorem monomial_requests_frame (P : Parameters) (S : IntegralMonomialTermBits.Source)
    (reply : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 1) (hp : isPhase .monomialFactor q)
    (hc : ((IntegralMixedVirtualMonomialRequestBits.program S
      (IntegralCriticalFlatGenericMonomialBits.coefficientTask P) (IntegralCriticalFlatFactorQuery.writer P .clearedHeight)
      (IntegralMixedScalarQueryBits.commonDenominator P)).controller.prepare
        (IntegralCriticalFlatGenericMonomialBits.input P S)).Requests reply budget q c) :
    IntegralMixedRoutineTaskBits.Frame P q c := by
  let C := IntegralMixedVirtualMonomialRequestBits.program S
    (IntegralCriticalFlatGenericMonomialBits.coefficientTask P) (IntegralCriticalFlatFactorQuery.writer P .clearedHeight)
    (IntegralMixedScalarQueryBits.commonDenominator P)
  let I := IntegralCriticalFlatGenericMonomialBits.input P S
  have H0 : C.controller.Requests reply (fun _ => budget q) (I q) c :=
    (RecursiveController.Controller.prepare_requests_iff C.controller I reply budget q c).mp hc
  have H1 := (IntegralMixedVirtualMonomialRequestBits.requests_iff S _ _ _ reply (fun _ => budget q) (I q) c).mp H0
  have HO : pairFst (I q) = q := IntegralCriticalFlatGenericMonomialBits.input_parent P S q
  have HCQ : pairFst (coefficientQuery (I q)) = q := IntegralCriticalFlatGenericMonomialBits.coefficientQuery_parent P S q
  have HHQ : pairFst (heightQuery (I q)) = q := IntegralCriticalFlatGenericMonomialBits.heightQuery_parent P S q
  change phase q = 3 at hp
  rw [H1.2]
  split_ifs with hz hd
  · unfold IntegralCriticalFlatGenericMonomialBits.coefficientTask
    split_ifs
    · have H := IntegralMixedMatrixFrames.matrix_frame P .derivativeCoefficient (coefficientQuery (I q))
        (by rw [HCQ]; change 1 < phase q; omega)
      rw [HCQ] at H
      exact H
    · have H := IntegralMixedMatrixFrames.matrix_frame P .originalCoefficient (coefficientQuery (I q))
        (by rw [HCQ]; change 0 < phase q; omega)
      rw [HCQ] at H
      exact H
  · rw [HO]
    exact IntegralMixedScalarQueryBits.scalar_frame P .derivativeCoefficient q (by rw [hr]; decide)
  · have H := monomial_factor_frame P .clearedHeight (heightQuery (I q))
      (by rw [HHQ]; change 2 < phase q; omega)
    rw [HHQ] at H
    exact H

theorem monomial_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (he : ∀ q, selectedValid P .monomialFactor q = true → MonomialRepliesAt P F reply q) :
    Correct (monomialMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofPreparedSingleCall_correct
  · intro q hq
    exact monomial_value_at P a F h g reply q ((selectedValid_iff P .monomialFactor q).mp hq).1 (he q hq)
  · intro q hq hr
    have HV := monomial_value_at P a F h g reply q ((selectedValid_iff P .monomialFactor q).mp hq).1 (he q hq)
    simp only [SingleCall.Program.value, hr, ite_true] at HV
    change pairSnd (pair _ _) = _ at HV
    rw [pairSnd_pair] at HV
    change (reply ((monomialProgram P F).query (monomialInput P F q))).length ≤ heightBound P q
    rw [HV]
    obtain ⟨z, hz⟩ := IntegralMixedVirtualCanonicalBits.monomial_canonical P F q
    rw [← hz]
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact residueBits_length_le _ _
  · intro q c budget hq hc
    have HQ := (selectedValid_iff P .monomialFactor q).mp hq
    exact monomial_requests_frame P (monomialSource P F) reply budget q c HQ.2.1 HQ.2.2 hc
end LeanCanny.Algebra.IntegralMixedVirtualNativeLowerBits
