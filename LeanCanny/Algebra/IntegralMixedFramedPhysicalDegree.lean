/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalDegreeBlock
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalDegreeValues

/-! # Every full saved physical row has its native original-header degree -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalDegree
open LeanCanny LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryScript (Instruction run paddedPast paddedPast_length chronological)
open IntegralMixedFramedHistoryFamilyBits (Plan commands prefixLength initial defaultInstruction keyAt)
open IntegralMixedFramedPhysicalIndex (arity enumerate prefixArity)
open IntegralMixedFramedPhysicalRowSelector
open IntegralMixedFramedPhysicalRowDegree
open IntegralMixedFramedPhysicalDegreeSemantics
open IntegralMixedFramedPhysicalDegreeValues
open IntegralMixedFramedPhysicalDegreeBlock
open IntegralMixedHeaderTablesBits (Tables)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def sourceDegreeAt (P : Parameters) (D : Plan P) (root : List Bool) (b : ℕ) :=
  ((chronological (D.rules root) b).getD (defaultInstruction P D root)).source.degree

theorem sourceDegreeAt_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (root : List Bool) (b : ℕ) (hb : b≤P.cap root+1) :
    sourceDegreeAt P D root b=P.degree root := by
  have HD : sourceDegreeAt P D (pairFst (keyAt root b [])) (prefixLength P (keyAt root b []))=
      P.degree (pairFst (keyAt root b [])) :=H.degree_eq _
  rw [IntegralMixedFramedHistoryFamilyBits.keyAt_root,IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P root b [] hb] at HD
  exact HD

theorem values_eq_native (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (ht : IntegralMixedFramedHeaderBits.Represents P D H T) (key : List Bool) (r : ℕ)
    (hr : r<arity (commands P D key)) :
    values (initial P D (pairFst key)) (commands P D key)
      (by rw [commands,paddedPast_length]; exact (min_le_right _ _).trans (Nat.le_succ _)) r=
      degree P T (pair key (BinaryNatCode.encode r)) := by
  let root:=pairFst key
  let m:=prefixLength P key
  let fallback:=defaultInstruction P D root
  let cs:=D.rules root
  let x:=initial P D root
  let b:=rowBirth P T (pair key (BinaryNatCode.encode r))
  have HM : m≤P.cap root+1:=min_le_right _ _
  have HA (j : ℕ) : prefixArity P T (pair key (List.replicate j true))=arity (paddedPast fallback cs j) :=
    IntegralMixedFramedPhysicalIndex.prefixArity_packet P D H T ht key j
  change r<arity (paddedPast fallback cs m) at hr
  have HR : r<fullArity P T (pair key (BinaryNatCode.encode r)) := by
    simpa only [fullArity,pairFst_pair,HA] using hr
  have HB : b<m ∧ prefixArity P T (pair key (List.replicate b true))≤r ∧
      r<prefixArity P T (pair key (List.replicate (b+1) true)) :=
    rowBirth_interval P T key r HR
  obtain ⟨hb,hl,hu⟩:=HB
  have HBO : b+1≤m:=Nat.succ_le_of_lt hb
  have HRO : r<arity (paddedPast fallback cs (b+1)):=by rw [←HA]; exact hu
  have HLO : arity (paddedPast fallback cs b)≤r:=by rw [←HA]; exact hl
  have HV:=values_padded_older x fallback cs m (b+1) (HM.trans (Nat.le_succ _)) HBO r HRO
  let past:=paddedPast fallback cs b
  let c:=(chronological cs b).getD fallback
  have HE : paddedPast fallback cs (b+1)=c::past :=IntegralMixedFramedHistoryScript.paddedPast_succ fallback cs b
  have HC : (c::past).length≤(P.cap root+1)+1 :=by
    rw [←HE,paddedPast_length]
    exact HBO.trans (HM.trans (Nat.le_succ _))
  have HRC : r<arity (c::past):=by rw [←HE]; exact HRO
  have HD : c.source.degree=P.degree root:=sourceDegreeAt_eq P D H root b (hb.le.trans HM)
  have HH : IntegralMixedCommandHeaderBits.lookup (T.commands root) b=IntegralMixedCommandHeaderBits.command c.command := by
    rw [ht.commands,IntegralMixedFramedHeaderBits.lookup_words _ fallback (by rfl)]
  have HX:=values_cons_new x c past HC r HLO HRC
  have HLen : past.length=b:=paddedPast_length fallback cs b
  rw [HLen,HD,←HA b] at HX
  have HNative:=native_block P T key r b hb hl hu c.command HH
  exact HV.trans ((values_congr x _ _ HE _ HC r).trans (HX.trans HNative.symm))

theorem degree_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (ht : IntegralMixedFramedHeaderBits.Represents P D H T) (key : List Bool)
    (i : Fin (arity (commands P D key))) :
    degree P T (pair key (BinaryNatCode.encode i.val))=
      ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).sampler.degrees ((enumerate (commands P D key)).symm i) := by
  have HV:=values_eq_native P D H T ht key i.val i.isLt
  rw [values,dite_eq_left i.isLt] at HV
  exact HV.symm

end LeanCanny.Algebra.IntegralMixedFramedPhysicalDegree
