/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalDegreeSemantics

/-! # Native row-degree programs agree with the literal creating block -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalDegreeBlock
open LeanCanny LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedPhysicalIndex (span prefixArity added block)
open IntegralMixedFramedPhysicalRowSelector
open IntegralMixedFramedPhysicalRowDegree
open IntegralMixedFramedPhysicalDegreeSemantics
open IntegralMixedHeaderTablesBits (Tables)
open IntegralMixedFramedHistoryFamilyBits (prefixLength)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem header_span {n B : ℕ} {Q : SpatialSource n}
    (c : IntegralMixedFullHistoryScript.Command Q B) :
    (if (IntegralMixedCommandHeaderBits.command c).context=1 then block n+1 else 1)=added c := by
  cases c with
  | integer=>rfl
  | critical=>rfl
  | cut r k=>cases k <;> rfl

theorem native_block (P : Parameters) (T : Tables) (key : List Bool) (r b : ℕ)
    (hb : b<prefixLength P key)
    (hl : prefixArity P T (pair key (List.replicate b true))≤r)
    (hu : r<prefixArity P T (pair key (List.replicate (b+1) true)))
    {Q : SpatialSource (P.ambient (pairFst key))}
    (c : IntegralMixedFullHistoryScript.Command Q (P.width (pairFst key)))
    (hc : IntegralMixedCommandHeaderBits.lookup (T.commands (pairFst key)) b=
      IntegralMixedCommandHeaderBits.command c) :
    degree P T (pair key (BinaryNatCode.encode r))=
      blockDegree (P.ambient (pairFst key)) (P.degree (pairFst key))
        (IntegralMixedCommandHeaderBits.command c).offset (P.cap (pairFst key)+1) (P.width (pairFst key)) b
        c.isCritical (r-prefixArity P T (pair key (List.replicate b true))) := by
  let q:=pair key (BinaryNatCode.encode r)
  let j:=r-prefixArity P T (pair key (List.replicate b true))
  have HB : rowBirth P T q=b:=rowBirth_packet P T key r b hb hl hu
  have HL : localRow P T q=j:=localRow_packet P T key r b hb hl hu
  have HV : Nat.fromBitsLE (pairSnd q)<fullArity P T q := by
    have HN:=(IntegralMixedFramedPhysicalRowSelector.prefix_strictMono P T key).monotone
    have HF:=hu.trans_le (HN (by omega : b+1≤prefixLength P key))
    simpa only [q,fullArity,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using HF
  have HH : header P T q=IntegralMixedCommandHeaderBits.command c := by
    unfold header
    rw [HB]
    simpa only [q,pairFst_pair] using hc
  have HP : physicalPower P T q=UniformIntegralPowerSchedule.physical (P.cap (pairFst key)+1)
      (2^P.width (pairFst key)) b := by
    unfold physicalPower
    rw [HB]
    simp only [q,pairFst_pair]
  have HS : scalarDegree P T q=2^P.width (pairFst key)*
      UniformIntegralPowerSchedule.birth (P.cap (pairFst key)+1) (2^P.width (pairFst key)) b := by
    unfold scalarDegree
    rw [HB]
    simp only [q,pairFst_pair]
  have HT : span P T (birthPacket P T q)=added c := by
    unfold span birthPacket
    rw [HB]
    simp only [q,pairFst_pair,pairSnd_pair,List.length_replicate,hc]
    exact header_span c
  have HI : IsScalar P T q ↔j=(if c.isCritical then block (P.ambient (pairFst key)) else 0) := by
    simp only [IsScalar,HV,true_and,HL,HT,added]
    cases c.isCritical <;> simp only [ite_true,ite_false,Bool.false_eq_true] <;> omega
  change degree P T q=_
  simp only [degree,ite_eq_left HV,HI,HS,HP,Frozen,HL,HH,q,pairFst_pair,blockDegree]
  rfl

end LeanCanny.Algebra.IntegralMixedFramedPhysicalDegreeBlock
