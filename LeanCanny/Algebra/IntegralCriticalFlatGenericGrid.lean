/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatMonomialSource
/-! # Flat cleared-grid stages for arbitrary actual Euler sources -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatGenericGridBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalFlatGridBits
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks
noncomputable def source (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) :=
  IntegralCriticalFlatGridSourceBits.source P F
noncomputable def access (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralEulerBits.Source) (h : IntegralEulerBits.Access F) : IntegralClearedCoefficientBits.Access (source P F) :=
  IntegralCriticalFlatGridSourceBits.access P a F h

noncomputable def program (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) : RecursiveFold.Program :=
  IntegralClearedCoefficientBits.RecursiveStage.program (source P F) (writer P .originalGridTerm)

noncomputable def budget (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) := IntegralClearedCoefficientBits.RecursiveStage.count (source P F)

theorem budget_binary (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralEulerBits.Source)
    (h : IntegralEulerBits.Access F) : BinaryFn (budget P F) :=
  IntegralClearedCoefficientBits.RecursiveStage.count_binary (source P F) (access P a F h)

theorem certificates (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralEulerBits.Source)
    (h : IntegralEulerBits.Access F) :
    (program P F).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  IntegralClearedCoefficientBits.RecursiveStage.certificates (source P F) (access P a F h)
    (writer P .originalGridTerm) (writer_FP P a .originalGridTerm)

theorem partial_value (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (he : ∀ c i, i < budget P F c → answer (writer P .originalGridTerm (pair c (BinaryNatCode.encode i))) =
      IntegralClearedCoefficientBits.maskedProgram (source P F) (pair c (BinaryNatCode.encode i)))
    (c : List Bool) (k : ℕ) (hk : k ≤ budget P F c) :
    (program P F).partialValue answer c k = residueBits
      (∑ i ∈ Finset.range k, ((source P F).summand c i : ZMod ((source P F).modulus c))) :=
  ModularFold.RecursiveStage.sum_partialValueWithModulus (budget P F)
    (fun c => BinaryNatCode.encode ((source P F).modulus c)) (writer P .originalGridTerm) answer
    (source P F).modulus (funext (fun _ => Nat.fromBitsLE_bits _)) c
    (fun i => ((source P F).summand c i : ZMod ((source P F).modulus c)))
    (Nat.pos_of_ne_zero ((source P F).modulus_ne_zero c))
    (fun i hi => (he c i hi).trans (IntegralClearedCoefficientBits.masked_packet (source P F) c i hi)) k hk

theorem value (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (he : ∀ c i, i < budget P F c → answer (writer P .originalGridTerm (pair c (BinaryNatCode.encode i))) =
      IntegralClearedCoefficientBits.maskedProgram (source P F) (pair c (BinaryNatCode.encode i)))
    (c : List Bool) : (program P F).value answer c = (source P F).value c :=
  (partial_value P F answer he c _ le_rfl).trans (IntegralClearedCoefficientBits.sum_value (source P F) c)

theorem halted_after (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool) (c : List Bool) :
    (program P F).controller.halted
      (((program P F).controller.reference answer)^[budget P F c] ((program P F).initial c)) = true :=
  (program P F).halted_after answer c

noncomputable def stateBound (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (c : List Bool) : ℕ :=
  2 * c.length + 2 * (budget P F c).size + ((source P F).modulus c).size + 2

theorem stateBound_unary (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralEulerBits.Source)
    (h : IntegralEulerBits.Access F) : UnaryFn (stateBound P F) := by
  have HB : UnaryFn (fun c => (budget P F c).size) :=
    (UnaryFn.length (budget_binary P a F h).bits_mem_FP).of_eq (fun c => BinaryNatCode.length_encode _)
  have HM : UnaryFn (fun c => ((source P F).modulus c).size) :=
    (UnaryFn.length (access P a F h).modulus.bits_mem_FP).of_eq (fun c => BinaryNatCode.length_encode _)
  exact (((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add ((UnaryFn.const 2).mul HB)).add HM |>.add (UnaryFn.const 2)

theorem state_length (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (he : ∀ c i, i < budget P F c → answer (writer P .originalGridTerm (pair c (BinaryNatCode.encode i))) =
      IntegralClearedCoefficientBits.maskedProgram (source P F) (pair c (BinaryNatCode.encode i)))
    (c : List Bool) (t : ℕ) :
    (RecursiveFold.encState (((program P F).controller.reference answer)^[t]
      ((program P F).initial c))).length ≤ stateBound P F c := by
  have H : (RecursiveFold.encState (((program P F).controller.reference answer)^[t]
      ((program P F).initial c))).length ≤
      2 * c.length + 2 * (Turing.MultiTapeTM.encNat (budget P F c)).length +
        (BinaryNatCode.encode ((source P F).modulus c)).length + 2 := by
    apply (program P F).orbit_length
    intro k hk
    rw [partial_value P F answer he c k hk]
    let : NeZero ((source P F).modulus c) := ⟨(source P F).modulus_ne_zero c⟩
    apply ModularFold.bits_length_le (fun c => BinaryNatCode.encode ((source P F).modulus c)) c
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using ZMod.val_lt
      (∑ i ∈ Finset.range k, ((source P F).summand c i : ZMod ((source P F).modulus c)))
  simpa only [stateBound, Turing.MultiTapeTM.encNat_apply, Nat.size_eq_bits_len, BinaryNatCode.length_encode] using H

theorem requests_iff (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool) (c child : List Bool) :
    (program P F).controller.Requests answer (budget P F) c child ↔
      ∃ i < budget P F c, child = writer P .originalGridTerm (pair c (BinaryNatCode.encode i)) :=
  IntegralClearedCoefficientBits.RecursiveStage.requests_iff (source P F) (writer P .originalGridTerm) answer c child

theorem requests_rank (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool) (c child : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .clearedGridSum c)
    (hc : (program P F).controller.Requests answer (budget P F) c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  obtain ⟨i, _, he⟩ := (requests_iff P F answer c child).mp hc
  rw [he]
  have H : (7 : ℕ) < IntegralCriticalHistoryTask.phase (pairFst (pair c (BinaryNatCode.encode i))) := by
    simp only [pairFst_pair]
    change IntegralCriticalHistoryTask.phase c = 8 at hp
    omega
  simpa only [pairFst_pair] using writer_lower_rank P .originalGridTerm (pair c (BinaryNatCode.encode i)) H

theorem requests_tasks (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool) (r c child : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P r c)
    (hc : (program P F).controller.Requests answer (budget P F) c child) :
    IntegralCriticalHistoryTask.Tasks P r child := by
  obtain ⟨i, _, he⟩ := (requests_iff P F answer c child).mp hc
  rw [he]
  exact writer_tasks P .originalGridTerm r (pair c (BinaryNatCode.encode i)) (by simpa only [pairFst_pair] using ht)

noncomputable def termProgram (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) : SingleCall.Program :=
  IntegralClearedCoefficientBits.RecursiveStage.term (source P F) (writer P .productPower)

noncomputable def termController (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) :=
  (termProgram P F).controller.prepare (termInput P)

theorem term_controls (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralEulerBits.Source)
    (h : IntegralEulerBits.Access F) : (termProgram P F).Controls :=
  IntegralClearedCoefficientBits.RecursiveStage.term_controls (source P F) (access P a F h)
    (writer P .productPower) (writer_FP P a .productPower)

theorem term_request_iff (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (c : List Bool) :
    (termProgram P F).request (termInput P c) = true ↔
      ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F)) (termInput P c) := by
  change decide (ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F)) (termInput P c)) = true ↔ _
  simp only [decide_eq_true_eq]

theorem term_certificates (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralEulerBits.Source)
    (h : IntegralEulerBits.Access F) :
    (termController P F).Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState) :=
  (termProgram P F).controller.prepare_certificates (termInput P)
    ((termProgram P F).certificates (term_controls P a F h)) (FP.computable (termInput_FP P a))

noncomputable def termValue (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (c : List Bool) :=
  IntegralClearedCoefficientBits.maskedProgram (source P F) (termInput P c)

theorem term_value (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (he : ∀ c, ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F)) (termInput P c) →
      answer (writer P .productPower (termInput P c)) =
        (IntegralClearedCoefficientBits.termSource (source P F)).value (termInput P c))
    (c : List Bool) : (termProgram P F).value answer (termInput P c) = termValue P F c := by
  by_cases hm : ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F)) (termInput P c)
  · simpa only [SingleCall.Program.value, termProgram, IntegralClearedCoefficientBits.RecursiveStage.term,
      termValue, IntegralClearedCoefficientBits.maskedProgram, hm, decide_true, ite_true, pairSnd_pair] using he c hm
  · simp only [SingleCall.Program.value, termProgram, IntegralClearedCoefficientBits.RecursiveStage.term,
      termValue, IntegralClearedCoefficientBits.maskedProgram, hm, decide_false, Bool.false_eq_true, ite_false]

theorem term_halted_after (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool) (c : List Bool) :
    (termController P F).halted
      (((termController P F).reference answer)^[1] ((termController P F).initial c)) = true :=
  (termProgram P F).halted_after answer (termInput P c)

theorem term_output_when_halted (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (he : ∀ c, ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F)) (termInput P c) →
      answer (writer P .productPower (termInput P c)) =
        (IntegralClearedCoefficientBits.termSource (source P F)).value (termInput P c))
    (c : List Bool) (t : ℕ)
    (hh : (termController P F).halted
      (((termController P F).reference answer)^[t] ((termController P F).initial c)) = true) :
    (termController P F).output
      (((termController P F).reference answer)^[t] ((termController P F).initial c)) = termValue P F c :=
  ((termProgram P F).output_when_halted answer (termInput P c) t hh).trans (term_value P F answer he c)

theorem monomial_value_length (S : IntegralClearedCoefficientBits.Source) (p : List Bool) :
    ((IntegralClearedCoefficientBits.termSource S).value p).length ≤ (S.modulus (pairFst p)).size := by
  let := S.ring (pairFst p)
  let : NeZero (S.modulus (pairFst p)) := ⟨S.modulus_ne_zero (pairFst p)⟩
  rw [IntegralClearedCoefficientBits.term_value]
  exact residueBits_length_le _ _

noncomputable def termStateBound (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (c : List Bool) : ℕ :=
  2 * (termInput P c).length + 4 + ((source P F).modulus c).size

theorem termStateBound_unary (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralEulerBits.Source)
    (h : IntegralEulerBits.Access F) : UnaryFn (termStateBound P F) := by
  have HM : UnaryFn (fun c => ((source P F).modulus c).size) :=
    (UnaryFn.length (access P a F h).modulus.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  exact (((UnaryFn.const 2).mul (UnaryFn.length (termInput_FP P a))).add (UnaryFn.const 4)).add HM

theorem term_state_length (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (he : ∀ c, ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F)) (termInput P c) →
      answer (writer P .productPower (termInput P c)) =
        (IntegralClearedCoefficientBits.termSource (source P F)).value (termInput P c))
    (c : List Bool) (t : ℕ) :
    (SingleCall.encState (((termController P F).reference answer)^[t] ((termController P F).initial c))).length ≤
      termStateBound P F c := by
  apply (termProgram P F).state_length_of_bound answer (termInput P c) t
  intro hr
  have hm : ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F)) (termInput P c) :=
    of_decide_eq_true hr
  change (answer (writer P .productPower (termInput P c))).length ≤ _
  rw [he c hm]
  simpa only [termInput_parent] using monomial_value_length (source P F) (termInput P c)

theorem term_requests_iff (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool) (c child : List Bool) :
    (termController P F).Requests answer (fun _ => 1) c child ↔
      ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F)) (termInput P c) ∧
        child = writer P .productPower (termInput P c) := by
  rw [termController, RecursiveController.Controller.prepare_requests_iff]
  exact IntegralClearedCoefficientBits.RecursiveStage.term_requests_iff (source P F)
    (writer P .productPower) answer (fun _ => 1) (termInput P c) child

theorem term_requests_rank (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool) (c child : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .originalGridTerm c)
    (hc : (termController P F).Requests answer (fun _ => 1) c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  obtain ⟨_, he⟩ := (term_requests_iff P F answer c child).mp hc
  rw [he]
  have H : (6 : ℕ) < IntegralCriticalHistoryTask.phase (pairFst (termInput P c)) := by
    rw [termInput_parent]
    change IntegralCriticalHistoryTask.phase c = 7 at hp
    omega
  simpa only [termInput_parent] using writer_lower_rank P .productPower (termInput P c) H

theorem term_requests_tasks (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool) (r c child : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P r c)
    (hc : (termController P F).Requests answer (fun _ => 1) c child) : IntegralCriticalHistoryTask.Tasks P r child := by
  obtain ⟨_, he⟩ := (term_requests_iff P F answer c child).mp hc
  rw [he]
  exact writer_tasks P .productPower r (termInput P c) (by simpa only [termInput_parent] using ht)

theorem partial_value_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (c : List Bool)
    (he : ∀ i, i < budget P F c → answer (writer P .originalGridTerm (pair c (BinaryNatCode.encode i))) =
      IntegralClearedCoefficientBits.maskedProgram (source P F) (pair c (BinaryNatCode.encode i)))
    (k : ℕ) (hk : k ≤ budget P F c) :
    (program P F).partialValue answer c k = residueBits
      (∑ i ∈ Finset.range k, ((source P F).summand c i : ZMod ((source P F).modulus c))) :=
  ModularFold.RecursiveStage.sum_partialValueWithModulus (budget P F)
    (fun c => BinaryNatCode.encode ((source P F).modulus c)) (writer P .originalGridTerm) answer
    (source P F).modulus (funext (fun _ => Nat.fromBitsLE_bits _)) c
    (fun i => ((source P F).summand c i : ZMod ((source P F).modulus c)))
    (Nat.pos_of_ne_zero ((source P F).modulus_ne_zero c))
    (fun i hi => (he i hi).trans (IntegralClearedCoefficientBits.masked_packet (source P F) c i hi)) k hk

theorem value_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (c : List Bool)
    (he : ∀ i, i < budget P F c → answer (writer P .originalGridTerm (pair c (BinaryNatCode.encode i))) =
      IntegralClearedCoefficientBits.maskedProgram (source P F) (pair c (BinaryNatCode.encode i)))
    : (program P F).value answer c = (source P F).value c :=
  (partial_value_at P F answer c he _ le_rfl).trans (IntegralClearedCoefficientBits.sum_value (source P F) c)

theorem state_length_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (c : List Bool)
    (he : ∀ i, i < budget P F c → answer (writer P .originalGridTerm (pair c (BinaryNatCode.encode i))) =
      IntegralClearedCoefficientBits.maskedProgram (source P F) (pair c (BinaryNatCode.encode i)))
    (t : ℕ) :
    (RecursiveFold.encState (((program P F).controller.reference answer)^[t]
      ((program P F).initial c))).length ≤ stateBound P F c := by
  have H : (RecursiveFold.encState (((program P F).controller.reference answer)^[t]
      ((program P F).initial c))).length ≤
      2 * c.length + 2 * (Turing.MultiTapeTM.encNat (budget P F c)).length +
        (BinaryNatCode.encode ((source P F).modulus c)).length + 2 := by
    apply (program P F).orbit_length
    intro k hk
    rw [partial_value_at P F answer c he k hk]
    let : NeZero ((source P F).modulus c) := ⟨(source P F).modulus_ne_zero c⟩
    apply ModularFold.bits_length_le (fun c => BinaryNatCode.encode ((source P F).modulus c)) c
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using ZMod.val_lt
      (∑ i ∈ Finset.range k, ((source P F).summand c i : ZMod ((source P F).modulus c)))
  simpa only [stateBound, Turing.MultiTapeTM.encNat_apply, Nat.size_eq_bits_len, BinaryNatCode.length_encode] using H

theorem term_value_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (c : List Bool)
    (he : ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F)) (termInput P c) →
      answer (writer P .productPower (termInput P c)) =
        (IntegralClearedCoefficientBits.termSource (source P F)).value (termInput P c))
    : (termProgram P F).value answer (termInput P c) = termValue P F c := by
  by_cases hm : ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F)) (termInput P c)
  · simpa only [SingleCall.Program.value, termProgram, IntegralClearedCoefficientBits.RecursiveStage.term,
      termValue, IntegralClearedCoefficientBits.maskedProgram, hm, decide_true, ite_true, pairSnd_pair] using he hm
  · simp only [SingleCall.Program.value, termProgram, IntegralClearedCoefficientBits.RecursiveStage.term,
      termValue, IntegralClearedCoefficientBits.maskedProgram, hm, decide_false, Bool.false_eq_true, ite_false]

theorem term_output_when_halted_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (c : List Bool)
    (he : ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F)) (termInput P c) →
      answer (writer P .productPower (termInput P c)) =
        (IntegralClearedCoefficientBits.termSource (source P F)).value (termInput P c))
    (t : ℕ)
    (hh : (termController P F).halted
      (((termController P F).reference answer)^[t] ((termController P F).initial c)) = true) :
    (termController P F).output
      (((termController P F).reference answer)^[t] ((termController P F).initial c)) = termValue P F c :=
  ((termProgram P F).output_when_halted answer (termInput P c) t hh).trans (term_value_at P F answer c he)

theorem term_state_length_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (c : List Bool)
    (he : ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F)) (termInput P c) →
      answer (writer P .productPower (termInput P c)) =
        (IntegralClearedCoefficientBits.termSource (source P F)).value (termInput P c))
    (t : ℕ) :
    (SingleCall.encState (((termController P F).reference answer)^[t] ((termController P F).initial c))).length ≤
      termStateBound P F c := by
  apply (termProgram P F).state_length_of_bound answer (termInput P c) t
  intro hr
  have hm : ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F)) (termInput P c) :=
    of_decide_eq_true hr
  change (answer (writer P .productPower (termInput P c))).length ≤ _
  rw [he hm]
  simpa only [termInput_parent] using monomial_value_length (source P F) (termInput P c)

noncomputable def monomialSource (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) :=
  (IntegralClearedCoefficientBits.termSource (source P F)).requery (termInput P)
noncomputable def monomialAccess (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralEulerBits.Source) (h : IntegralEulerBits.Access F) : IntegralMonomialTermBits.Access (monomialSource P F) :=
  (IntegralClearedCoefficientBits.termAccess (source P F) (access P a F h)).requery _ (termInput P) (termInput_FP P a)
end LeanCanny.Algebra.IntegralCriticalFlatGenericGridBits
