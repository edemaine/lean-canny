/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCanonicalPaddingSeed
public import LeanCanny.Encoding.IntegralMixedSourceIntegerLastCode
/-! # Actual chronological canonical seed padding before the reserved probe

The source is constant at all creating births. The prospective final probe is
not executed in either prefix. Every padding instruction is derived from the
literal original table and existing decoder at its own actual saved prefix.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerPaddingPrefix
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (P : Parameters) (R : (root : List Bool)→SpatialSource (P.ambient root))
 (hn : ∀root,0<P.ambient root) (hd : ∀root,(R root).degree=P.degree root)
 (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)

noncomputable def seedInstruction (root : List Bool) : Instruction (P.ambient root) (P.width root) :=
 IntegralMixedCanonicalPaddingSeed.instruction (R root)
   (IntegralMixedCausalUnitRecordBits.record (R root) (hn root) 0
     (IntegralMixedChronologicalFrameCode.code (P.ambient root) [] 0 0) (by rw [hd];exact hcap root)).source_cap

variable (N : List Bool→ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
 (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
 (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
local notation "D"=>IntegralMixedSourceIntegerRecordAppend.plan P (fun root _=>R root) hn (fun root _=>hd root) hcap N T hz hT hroom
attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan

theorem padding_code (root : List Bool) (oldCodes : List (List Bool)) (k : ℕ) (probe : List Bool)
    (ht : IntegralMixedCausalRecordPlanBits.records root=WordList.encode
      (oldCodes++List.replicate k (IntegralMixedChronologicalFrameCode.code (P.ambient root) [] 0 0)++[probe]))
    (i : ℕ) (hi : i<k) :
    IntegralMixedCausalRecordPlanBits.code root (oldCodes.length+i)=IntegralMixedChronologicalFrameCode.code (P.ambient root) [] 0 0 :=by
  unfold IntegralMixedCausalRecordPlanBits.code
  rw [ht,WordList.get_encode,List.getElem?_append_left (by simp only [List.length_append,List.length_replicate];omega)]
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  simp only [List.getElem?_replicate,hi,ite_true,Option.getD_some]

include hroom in
theorem prefix_bound (root : List Bool) (oldCodes : List (List Bool)) (k : ℕ) (probe : List Bool)
    (ht : IntegralMixedCausalRecordPlanBits.records root=WordList.encode
      (oldCodes++List.replicate k (IntegralMixedChronologicalFrameCode.code (P.ambient root) [] 0 0)++[probe]))
    (i : ℕ) (hi : i≤k) : N root+(oldCodes.length+i)≤P.cap root+1 :=by
  have HC : IntegralMixedCausalRecordPlanBits.count root=oldCodes.length+k+1:=by
    simp only [IntegralMixedCausalRecordPlanBits.count,ht,WordListRecords.count_encode,
      List.length_append,List.length_replicate,List.length_singleton]
  have HR:=hroom root
  rw [HC] at HR
  omega

variable (H : IntegralMixedFramedHistoryFamilyBits.Data P
 (IntegralMixedSourceIntegerRecordAppend.plan P (fun root _=>R root) hn (fun root _=>hd root) hcap N T hz hT hroom))

include H in
theorem instruction_at (key : List Bool) (oldCodes : List (List Bool)) (k : ℕ) (probe : List Bool)
    (ht : IntegralMixedCausalRecordPlanBits.records (pairFst key)=WordList.encode
      (oldCodes++List.replicate k (IntegralMixedChronologicalFrameCode.code (P.ambient (pairFst key)) [] 0 0)++[probe]))
    (i : ℕ) (hi : i<k) (hk : prefixLength P key=N (pairFst key)+(oldCodes.length+i)) :
    instruction P D key=seedInstruction P R hn hd hcap (pairFst key) :=by
  have HB : oldCodes.length+i<IntegralMixedCausalRecordPlanBits.count (pairFst key):=by
    simp only [IntegralMixedCausalRecordPlanBits.count,ht,WordListRecords.count_encode,
      List.length_append,List.length_replicate,List.length_singleton]
    omega
  rw [IntegralMixedSourceIntegerRecordAppend.instruction_at_bank P (fun root _=>R root) hn
    (fun root _=>hd root) hcap N T hz hT hroom H key (oldCodes.length+i) HB hk]
  unfold IntegralMixedSourceIntegerRecordAppend.step
  rw [padding_code P _ oldCodes k probe ht i hi]
  exact IntegralMixedCanonicalPaddingSeed.instantiate _ (R _) (hn _) _

include H in
theorem past_padding (root aux : List Bool) (oldCodes : List (List Bool)) (k : ℕ) (probe : List Bool)
    (ht : IntegralMixedCausalRecordPlanBits.records root=WordList.encode
      (oldCodes++List.replicate k (IntegralMixedChronologicalFrameCode.code (P.ambient root) [] 0 0)++[probe])) :
    paddedPast (defaultInstruction P D root) ((D).rules root) (N root+(oldCodes.length+k))=
      List.replicate k (seedInstruction P R hn hd hcap root)++
        paddedPast (defaultInstruction P D root) ((D).rules root) (N root+oldCodes.length) :=by
  have HP (i : ℕ) (hi : i≤k) : prefixLength P (keyAt root (N root+(oldCodes.length+i)) aux)=N root+(oldCodes.length+i):=
    keyAt_prefix P root _ aux (prefix_bound P N hroom root oldCodes k probe ht i hi)
  have HI (i : ℕ) (hi : i<k) :
      (chronological ((D).rules root) (N root+(oldCodes.length+i))).getD (defaultInstruction P D root)=
        seedInstruction P R hn hd hcap root :=by
    have HT : IntegralMixedCausalRecordPlanBits.records (pairFst (keyAt root (N root+(oldCodes.length+i)) aux))=
        WordList.encode (oldCodes++List.replicate k
          (IntegralMixedChronologicalFrameCode.code (P.ambient (pairFst (keyAt root (N root+(oldCodes.length+i)) aux))) [] 0 0)++[probe]) :=by
      simpa only [pairFst_pair] using ht
    have HE:=instruction_at P R hn hd hcap N T hz hT hroom H
      (keyAt root (N root+(oldCodes.length+i)) aux) oldCodes k probe HT i hi
      (by simpa only [pairFst_pair] using HP i hi.le)
    unfold instruction at HE
    have HT' (root' : List Bool) (b : ℕ)
        (HE' : (chronological ((D).rules root') b).getD (defaultInstruction P D root')=
          seedInstruction P R hn hd hcap root')
        (HR : root'=root) (HB : b=N root+(oldCodes.length+i)) :
        (chronological ((D).rules root) (N root+(oldCodes.length+i))).getD (defaultInstruction P D root)=
          seedInstruction P R hn hd hcap root :=by
      cases HR
      cases HB
      exact HE'
    exact HT' _ _ HE (pairFst_pair _ _) (HP i hi.le)
  have HC (i : ℕ) (hi : i≤k) :
      paddedPast (defaultInstruction P D root) ((D).rules root) (N root+(oldCodes.length+i))=
        List.replicate i (seedInstruction P R hn hd hcap root)++
          paddedPast (defaultInstruction P D root) ((D).rules root) (N root+oldCodes.length) :=by
    induction i with
    | zero=>simp only [Nat.add_zero,List.replicate_zero,List.nil_append]
    | succ i ih=>
      rw [show N root+(oldCodes.length+(i+1))=(N root+(oldCodes.length+i))+1 by omega,
        paddedPast_succ,HI i (by omega),ih (by omega),List.replicate_succ,List.cons_append]
  exact HC k le_rfl

end LeanCanny.Encoding.IntegralMixedSourceIntegerPaddingPrefix
