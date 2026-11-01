/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualNativeAccess
public import LeanCanny.Algebra.IntegralCriticalFlatGenericMonomial
/-! # Recursive denominator leaves in actual monomial factors

Every scalar denominator factor requests a child when its matrix indices
agree. Coefficient and retained-height requests keep their existing forms.
The local controller never evaluates the mixed common denominator.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualMonomialRequestBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open IntegralMonomialTermBits
set_option backward.isDefEq.respectTransparency false

def denominatorRequest (S : Source) (p : List Bool) : Prop :=
  position p ≠ 0 ∧ (position p = 1 ∨ (valid S p ∧ freeIndex S p)) ∧ sameIndex p
instance (S : Source) (p : List Bool) : Decidable (denominatorRequest S p) := inferInstanceAs (Decidable (_ ∧ _))

def heightRequest (S : Source) (p : List Bool) : Prop :=
  position p ≠ 0 ∧ position p ≠ 1 ∧ valid S p ∧ ¬freeIndex S p
instance (S : Source) (p : List Bool) : Decidable (heightRequest S p) := inferInstanceAs (Decidable (_ ∧ _))

theorem denominatorRequest_FP (S : Source) (a : Access S) : FPPred (denominatorRequest S) :=
  ((position_binary.eq (BinaryFn.const 0)).not).and
    (((position_binary.eq (BinaryFn.const 1)).or ((valid_fppred S a).and (freeIndex_fppred S a))).and sameIndex_fppred)

theorem heightRequest_FP (S : Source) (a : Access S) : FPPred (heightRequest S) :=
  ((position_binary.eq (BinaryFn.const 0)).not).and
    (((position_binary.eq (BinaryFn.const 1)).not).and ((valid_fppred S a).and (freeIndex_fppred S a).not))

noncomputable def program (S : Source) (coefficientTask heightTask denominatorTask : List Bool → List Bool) : SingleCall.Program where
  request p := decide (position p = 0 ∨ denominatorRequest S p ∨ heightRequest S p)
  query p := if position p = 0 then coefficientTask (coefficientQuery p)
    else if denominatorRequest S p then denominatorTask (pairFst p) else heightTask (heightQuery p)
  immediate p := if position p = 1 ∨ valid S p then [] else unitProgram S p
  finish := pairSnd

theorem controls (S : Source) (a : Access S) (coefficientTask heightTask denominatorTask : List Bool → List Bool)
    (hc : coefficientTask ∈ FP) (hh : heightTask ∈ FP) (hd : denominatorTask ∈ FP) :
    (program S coefficientTask heightTask denominatorTask).Controls := by
  refine ⟨?_, ?_, ?_, pairSnd_mem_FP⟩
  · exact ((position_binary.eq (BinaryFn.const 0)).or ((denominatorRequest_FP S a).or (heightRequest_FP S a))).flag_mem_FP
  · exact (position_binary.eq (BinaryFn.const 0)).ite_mem_FP
      (mem_FP_comp coefficientQuery_FP hc) ((denominatorRequest_FP S a).ite_mem_FP
        (mem_FP_comp pairFst_mem_FP hd) (mem_FP_comp heightQuery_FP hh))
  · exact ((position_binary.eq (BinaryFn.const 1)).or (valid_fppred S a)).ite_mem_FP
      (constFn_mem_FP []) (unitProgram_FP S a)

theorem value_at (S : Source) (a : Access S) (coefficientTask heightTask denominatorTask reply : List Bool → List Bool)
    (p : List Bool)
    (hc : position p = 0 → reply (coefficientTask (coefficientQuery p)) = a.coefficient (coefficientQuery p))
    (hh : heightRequest S p → reply (heightTask (heightQuery p)) = a.height (heightQuery p))
    (hd : denominatorRequest S p → reply (denominatorTask (pairFst p)) = a.denominator (pairFst p)) :
    (program S coefficientTask heightTask denominatorTask).value reply p = entryProgram S a p := by
  by_cases h0 : position p = 0 <;> by_cases h1 : position p = 1 <;>
    by_cases hv : valid S p <;> by_cases hf : freeIndex S p <;> by_cases hs : sameIndex p <;>
    simp_all [SingleCall.Program.value, program, denominatorRequest, heightRequest,
      entryProgram, scalarProgram]

theorem actual_value_at (S : Source) (a : Access S)
    (coefficientTask heightTask denominatorTask reply : List Bool → List Bool)
    (q : List Bool) (s : ℕ) (r t : Fin (S.rank q))
    (hc : position (packet q s r.val t.val) = 0 →
      reply (coefficientTask (coefficientQuery (packet q s r.val t.val))) = a.coefficient (coefficientQuery (packet q s r.val t.val)))
    (hh : heightRequest S (packet q s r.val t.val) →
      reply (heightTask (heightQuery (packet q s r.val t.val))) = a.height (heightQuery (packet q s r.val t.val)))
    (hd : denominatorRequest S (packet q s r.val t.val) →
      reply (denominatorTask (pairFst (packet q s r.val t.val))) = a.denominator (pairFst (packet q s r.val t.val))) :
    letI := S.ring q
    (program S coefficientTask heightTask denominatorTask).value reply (packet q s r.val t.val) =
      residueBits ((Algebra.leftMulMatrix (S.basis q) (factor S q s) r t : ℤ) : ZMod (S.modulus q)) :=
  (value_at S a coefficientTask heightTask denominatorTask reply (packet q s r.val t.val) hc hh hd).trans
    (entry_correct S a q s r t)

theorem requests_iff (S : Source) (coefficientTask heightTask denominatorTask reply : List Bool → List Bool)
    (budget : List Bool → ℕ) (p child : List Bool) :
    (program S coefficientTask heightTask denominatorTask).controller.Requests reply budget p child ↔
      (position p = 0 ∨ denominatorRequest S p ∨ heightRequest S p) ∧
        child = if position p = 0 then coefficientTask (coefficientQuery p)
          else if denominatorRequest S p then denominatorTask (pairFst p) else heightTask (heightQuery p) := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

theorem halted_after (S : Source) (coefficientTask heightTask denominatorTask reply : List Bool → List Bool) (p : List Bool) :
    (program S coefficientTask heightTask denominatorTask).controller.halted
      (((program S coefficientTask heightTask denominatorTask).controller.reference reply)^[1]
        ((program S coefficientTask heightTask denominatorTask).controller.initial p)) = true :=
  (program S coefficientTask heightTask denominatorTask).halted_after reply p

theorem state_length_packet (S : Source) (a : Access S)
    (coefficientTask heightTask denominatorTask reply : List Bool → List Bool)
    (q : List Bool) (s : ℕ) (r t : Fin (S.rank q))
    (hc : position (packet q s r.val t.val) = 0 →
      reply (coefficientTask (coefficientQuery (packet q s r.val t.val))) = a.coefficient (coefficientQuery (packet q s r.val t.val)))
    (hh : heightRequest S (packet q s r.val t.val) →
      reply (heightTask (heightQuery (packet q s r.val t.val))) = a.height (heightQuery (packet q s r.val t.val)))
    (hd : denominatorRequest S (packet q s r.val t.val) →
      reply (denominatorTask (pairFst (packet q s r.val t.val))) = a.denominator (pairFst (packet q s r.val t.val)))
    (i : ℕ) :
    (SingleCall.encState (((program S coefficientTask heightTask denominatorTask).controller.reference reply)^[i]
      ((program S coefficientTask heightTask denominatorTask).controller.initial (packet q s r.val t.val)))).length ≤
        2 * (packet q s r.val t.val).length + 4 + (S.modulus q).size := by
  apply (program S coefficientTask heightTask denominatorTask).state_length_of_bound
    reply (packet q s r.val t.val) i (S.modulus q).size
  intro hr
  have HV := actual_value_at S a coefficientTask heightTask denominatorTask reply q s r t hc hh hd
  rw [SingleCall.Program.value, hr, ite_eq_left rfl] at HV
  rw [show (program S coefficientTask heightTask denominatorTask).finish = pairSnd from rfl,
    pairSnd_pair] at HV
  rw [HV]
  let : NeZero (S.modulus q) := ⟨S.modulus_ne_zero q⟩
  exact residueBits_length_le _ _

noncomputable abbrev virtualProgram (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralMixedCutSource.Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (coefficientTask heightTask denominatorTask : List Bool → List Bool) :=
  program (IntegralCriticalFlatGenericGridBits.monomialSource P (IntegralMixedVirtualNativeBits.arithmetic F I))
    coefficientTask heightTask denominatorTask
end LeanCanny.Algebra.IntegralMixedVirtualMonomialRequestBits
