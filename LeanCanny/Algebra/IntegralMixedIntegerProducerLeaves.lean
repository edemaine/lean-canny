/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedIntegerProducerAccess
public import LeanCanny.Algebra.IntegralMixedCoefficientQuery
public import LeanCanny.Algebra.IntegralMixedNormalizationValueBranches
public import LeanCanny.Computation.NativeSingleCallBranch
/-! # Integer producer leaves read original coefficients, with no leading-value premise -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedIntegerProducerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure OriginalCells (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) : Prop where
  coefficient : rawScalar P D ∈ FP

noncomputable def leadingPacket (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : List Bool :=
  pair q (pair (BinaryNatCode.encode (polynomial P D (IntegralMixedVirtualTaskBits.saved P q)).natDegree) (pair [] []))

noncomputable def leadingRead (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) : List Bool → List Bool :=
  IntegralMixedCoefficientQueryBits.writer P .companion .criticalCoefficient ∘ leadingPacket P D

theorem leadingRead_FP (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Metadata P D) :
    leadingRead P D ∈ FP := by
  have HD : BinaryFn (fun q => (polynomial P D (IntegralMixedVirtualTaskBits.saved P q)).natDegree) :=
    h.degree.comp (IntegralMixedVirtualTaskBits.saved_FP P a)
  exact mem_FP_comp (mem_FP_pair id_mem_FP (mem_FP_pair HD.bits_mem_FP (constFn_mem_FP (pair [] []))))
    (IntegralMixedCoefficientQueryBits.writer_FP P a .companion .criticalCoefficient)

noncomputable def leadingValue (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : List Bool :=
  residueBits (leadingInteger P D q : ZMod (modulus P q))

theorem degree_task_cap (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    (polynomial P D (IntegralMixedVirtualTaskBits.saved P q)).natDegree ≤ numericCap P (RankedHistoryTask.root q) := by
  have HB := degree_cap P D (IntegralMixedVirtualTaskBits.saved P q)
  have HR : pairFst (IntegralMixedVirtualTaskBits.saved P q) = RankedHistoryTask.root q := pairFst_pair _ _
  rw [HR] at HB
  exact HB.trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.2.2.2.1

theorem leadingRead_value (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    rawScalar P D (leadingRead P D q) = leadingValue P D q := by
  have HP : pairFst (leadingPacket P D q) = q := pairFst_pair _ _
  have HS : IntegralMixedVirtualTaskBits.saved P (leadingRead P D q) = IntegralMixedVirtualTaskBits.saved P q :=
    (IntegralMixedCoefficientQueryBits.writer_saved P .companion .criticalCoefficient (leadingPacket P D q)).trans
      (congrArg (IntegralMixedVirtualTaskBits.saved P) HP)
  have HM : modulus P (leadingRead P D q) = modulus P q :=
    (IntegralMixedCoefficientQueryBits.writer_modulus P .companion .criticalCoefficient (leadingPacket P D q)).trans (congrArg (modulus P) HP)
  have HK : get P .coefficient (leadingRead P D q) = (polynomial P D (IntegralMixedVirtualTaskBits.saved P q)).natDegree := by
    unfold leadingRead
    rw [Function.comp_apply, IntegralMixedCoefficientQueryBits.writer_get]
    simp only [leadingPacket, IntegralPowerProductBits.factorWord, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, reduceCtorEq, ite_false, ite_true]
    exact min_eq_left (degree_task_cap P D q)
  unfold rawScalar
  rw [HS, HK, HM, Polynomial.coeff_natDegree]
  rfl

theorem leadingValue_FP (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Metadata P D) (c : OriginalCells P D) : leadingValue P D ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (leadingRead_FP P a D h) c.coefficient) (leadingRead_value P D)

noncomputable def coefficientValue (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : List Bool :=
  if get P .row q % oldRank P D q = get P .col q % oldRank P D q then rawScalar P D q else []

theorem coefficientValue_FP (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (c : OriginalCells P D) : coefficientValue P D ∈ FP := by
  have H := ((get_binary P a .row).mod (oldRank_binary P a D)).eq ((get_binary P a .col).mod (oldRank_binary P a D))
  exact mem_FP_of_eq (H.ite_mem_FP c.coefficient (constFn_mem_FP [])) (fun q => by simp only [coefficientValue])

noncomputable def selected (P : Parameters) (p : Phase) (q : List Bool) : Bool :=
  decide (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 6 ∧ isPhase p q ∧ get P .slot15 q = 0)

theorem selected_FP (P : Parameters) (a : Access P) (p : Phase) : (fun q => [selected P p q]) ∈ FP :=
  ((IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 6)).and
      ((isPhase_FP p).and ((get_binary P a .slot15).eq (BinaryFn.const 0))))).flag_mem_FP

theorem selected_iff (P : Parameters) (p : Phase) (q : List Bool) : selected P p q = true ↔
    IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 6 ∧ isPhase p q ∧ get P .slot15 q = 0 := by
  simp only [selected, decide_eq_true_eq]

def leafProgram (f : List Bool → List Bool) : SingleCall.Program where
  request _ := false
  query := id
  immediate := f
  finish := id

noncomputable def leaf (P : Parameters) (p : Phase) (a : Access P) (f : List Bool → List Bool) (hf : f ∈ FP) : Machine :=
  ofSingleCall (leafProgram f) ((leafProgram f).certificates ⟨constFn_mem_FP [false], id_mem_FP, hf, id_mem_FP⟩)
    (selected P p) (selected_FP P a p) f (fun _ => 0) (UnaryFn.const 0)

theorem leaf_correct (P : Parameters) (p : Phase) (a : Access P) (f : List Bool → List Bool) (hf : f ∈ FP)
    (answer : List Bool → List Bool) : Correct (leaf P p a f hf) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro _ _
    rfl
  · intro _ _ hr
    cases hr
  · intro q child budget _ hc
    obtain ⟨hr, _⟩ := ((leafProgram f).requests_iff answer budget q child).mp hc
    cases hr

noncomputable def leadingMachine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Metadata P D) (c : OriginalCells P D) : Machine := leaf P .originalCoefficient a (leadingValue P D) (leadingValue_FP P a D h c)

noncomputable def coefficientMachine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (c : OriginalCells P D) : Machine := leaf P .criticalCoefficient a (coefficientValue P D) (coefficientValue_FP P a D c)

end LeanCanny.Algebra.IntegralMixedIntegerProducerBits
