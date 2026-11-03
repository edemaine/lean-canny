/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerPaddingRealization
/-! # A terminal canonical seed is executed as part of the real history

Unlike a reserved query probe, the last record is an ordinary seed birth.
The entire actual program, including that last record, is a seed extension.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerSeedTail
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (P : Parameters) (R : (root : List Bool)→SpatialSource (P.ambient root))
 (hn : ∀root,0<P.ambient root) (hd : ∀root,(R root).degree=P.degree root)
 (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
 (N : List Bool→ℕ) (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
 (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
 (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
local notation "D"=>IntegralMixedSourceIntegerRecordAppend.plan P (fun root _=>R root) hn (fun root _=>hd root) hcap N T hz hT hroom
attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan
variable (H : IntegralMixedFramedHistoryFamilyBits.Data P
 (IntegralMixedSourceIntegerRecordAppend.plan P (fun root _=>R root) hn (fun root _=>hd root) hcap N T hz hT hroom))

include H in
private theorem instruction_of_seed (key : List Bool) (j : ℕ)
    (hj : j<IntegralMixedCausalRecordPlanBits.count (pairFst key))
    (hk : prefixLength P key=N (pairFst key)+j)
    (hc : IntegralMixedCausalRecordPlanBits.code (pairFst key) j=
      IntegralMixedChronologicalFrameCode.code (P.ambient (pairFst key)) [] 0 0) :
    instruction P D key=IntegralMixedSourceIntegerPaddingPrefix.seedInstruction P R hn hd hcap (pairFst key) :=by
  rw [IntegralMixedSourceIntegerRecordAppend.instruction_at_bank P (fun root _=>R root) hn
    (fun root _=>hd root) hcap N T hz hT hroom H key j hj hk]
  unfold IntegralMixedSourceIntegerRecordAppend.step
  rw [hc]
  exact IntegralMixedCanonicalPaddingSeed.instantiate _ (R _) (hn _) _

include H in
theorem full_seed_tail (root aux : List Bool) (codes : List (List Bool)) (k : ℕ)
    (ht : IntegralMixedCausalRecordPlanBits.records root=WordList.encode
      (codes++List.replicate k (IntegralMixedChronologicalFrameCode.code (P.ambient root) [] 0 0))) :
    (D).rules root=List.replicate k (IntegralMixedSourceIntegerPaddingPrefix.seedInstruction P R hn hd hcap root)++
      paddedPast (defaultInstruction P D root) ((D).rules root) (N root+codes.length) :=by
  have HC : IntegralMixedCausalRecordPlanBits.count root=codes.length+k:=by
    simp only [IntegralMixedCausalRecordPlanBits.count,ht,WordListRecords.count_encode,List.length_append,List.length_replicate]
  have HL : ((D).rules root).length=N root+(codes.length+k):=by
    unfold IntegralMixedSourceIntegerRecordAppend.plan
    rw [IntegralMixedSourceIntegerPrelude.extended_length,IntegralMixedSourceIntegerRecordAppend.later_length,HC]
    omega
  have HB (i : ℕ) (hi : i≤k) : N root+(codes.length+i)≤P.cap root+1:=by
    have HH:=hroom root
    rw [HC] at HH
    omega
  have HI (i : ℕ) (hi : i<k) :
      (chronological ((D).rules root) (N root+(codes.length+i))).getD (defaultInstruction P D root)=
        IntegralMixedSourceIntegerPaddingPrefix.seedInstruction P R hn hd hcap root :=by
    let key:=keyAt root (N root+(codes.length+i)) aux
    have HK : prefixLength P key=N root+(codes.length+i):=keyAt_prefix P root _ aux (HB i hi.le)
    have HH:=instruction_of_seed P R hn hd hcap N T hz hT hroom H key (codes.length+i)
      (by simp only [key,pairFst_pair,HC];omega)
      (by simpa only [key,pairFst_pair] using HK)
      (by
        simp only [key,pairFst_pair,IntegralMixedCausalRecordPlanBits.code,ht,WordList.get_encode]
        rw [List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left]
        simp only [List.getElem?_replicate,hi,ite_true,Option.getD_some])
    unfold instruction at HH
    have HT' (root' : List Bool) (b : ℕ)
        (HE' : (chronological ((D).rules root') b).getD (defaultInstruction P D root')=
          IntegralMixedSourceIntegerPaddingPrefix.seedInstruction P R hn hd hcap root')
        (HR : root'=root) (HB' : b=N root+(codes.length+i)) :
        (chronological ((D).rules root) (N root+(codes.length+i))).getD (defaultInstruction P D root)=
          IntegralMixedSourceIntegerPaddingPrefix.seedInstruction P R hn hd hcap root :=by
      cases HR
      cases HB'
      exact HE'
    exact HT' _ _ HH (pairFst_pair _ _) HK
  have HA (i : ℕ) (hi : i≤k) :
      paddedPast (defaultInstruction P D root) ((D).rules root) (N root+(codes.length+i))=
        List.replicate i (IntegralMixedSourceIntegerPaddingPrefix.seedInstruction P R hn hd hcap root)++
          paddedPast (defaultInstruction P D root) ((D).rules root) (N root+codes.length) :=by
    induction i with
    | zero=>simp only [Nat.add_zero,List.replicate_zero,List.nil_append]
    | succ i ih=>
      rw [show N root+(codes.length+(i+1))=(N root+(codes.length+i))+1 by omega,
        paddedPast_succ,HI i (by omega),ih (by omega),List.replicate_succ,List.cons_append]
  have HH:=HA k le_rfl
  rw [←HL,paddedPast_full] at HH
  exact HH

private theorem realizes_list_iff {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) (v : ℕ→ℝ) :
    IntegralMixedIntegerRealization.Realizes (run x cs hc) v↔
      IntegralMixedIntegerRealization.Realizes (run x ds hd) v:=by cases he;rfl

include hroom in
theorem before_bound (root : List Bool) (codes : List (List Bool)) (k : ℕ)
    (ht : IntegralMixedCausalRecordPlanBits.records root=WordList.encode
      (codes++List.replicate k (IntegralMixedChronologicalFrameCode.code (P.ambient root) [] 0 0))) :
    N root+codes.length≤P.cap root+1 :=by
  have HC : IntegralMixedCausalRecordPlanBits.count root=codes.length+k:=by
    simp only [IntegralMixedCausalRecordPlanBits.count,ht,WordListRecords.count_encode,List.length_append,List.length_replicate]
  have HH:=hroom root
  rw [HC] at HH
  omega

include H in
theorem full_realizes (root aux : List Bool) (codes : List (List Bool)) (k : ℕ)
    (ht : IntegralMixedCausalRecordPlanBits.records root=WordList.encode
      (codes++List.replicate k (IntegralMixedChronologicalFrameCode.code (P.ambient root) [] 0 0)))
    (charge : ℕ) (hcharge : (R root).degree=BoundedZeroSource.powerDegree charge)
    (v : ℕ→ℝ)
    (hv : IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedFamilyRunView.runAt P D root (N root+codes.length)
        (before_bound P N hroom root codes k ht)) v)
    (p : Fin (P.ambient root+1)→ℝ)
    (hp : (FermatCriticalHomogenization.polynomial (R root).low (R root).leading (R root).degree).eval₂
      (Int.castRingHom ℝ) p=0)
    (hg : ∀i,i≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (R root).low (R root).leading (R root).degree)).eval₂
        (Int.castRingHom ℝ) p=0) :
    IntegralMixedIntegerRealization.Realizes
      (run (initial P D root) ((D).rules root) (by have HH:=(D).room root;omega))
      (IntegralMixedCanonicalPadding.values (p 0) v k) :=by
  let cs:=paddedPast (defaultInstruction P D root) ((D).rules root) (N root+codes.length)
  have HB : cs.length≤(P.cap root+1)+1:=by
    rw [paddedPast_length]
    exact (before_bound P N hroom root codes k ht).trans (Nat.le_succ _)
  have HE:=full_seed_tail P R hn hd hcap N T hz hT hroom H root aux codes k ht
  have HC : IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (R root).degree≤2^P.width root:=by
    rw [hd]
    exact hcap root
  have HA : (List.replicate k (IntegralMixedSourceIntegerPaddingPrefix.seedInstruction P R hn hd hcap root)++cs).length≤(P.cap root+1)+1:=by
    rw [←HE]
    have HH:=(D).room root
    omega
  have HR:=IntegralMixedCanonicalPadding.run_realizes (initial P D root) cs HB (R root)
    (IntegralMixedCausalUnitRecordBits.record (R root) (hn root) 0
      (IntegralMixedChronologicalFrameCode.code (P.ambient root) [] 0 0) HC).source_cap
    (hn root) charge hcharge HC v hv p hp hg k HA
  exact (realizes_list_iff (initial P D root) _ _ _ _ HE
    (IntegralMixedCanonicalPadding.values (p 0) v k)).mpr HR

end LeanCanny.Encoding.IntegralMixedSourceIntegerSeedTail
