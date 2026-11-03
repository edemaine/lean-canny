/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval
/-! # Literal strict-interval sign readback for the appended probe -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank tables represents)
open IntegralMixedPhysicalCriticalPrefixes (birth key input)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

attribute [local irreducible] bank tables

theorem value_packet (upper : Bool) (q v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer true) q v) :
    value hn ht ha hR outer upper (pair q v)=InfinitesimalSign.encode
      (SignType.sign ((term n outer upper (IntegralMixedPhysicalCriticalQuery.root q)).eval
        (IntegralFramedPhysicalBankTerm.env (childBank hn ht ha hR outer)
          (tables hn ht ha hR outer) (represents hn ht ha hR outer) q v hv))) :=by
  have HP:=IntegralFramedPhysicalBankTerm.packet (childBank hn ht ha hR outer)
    (tables hn ht ha hR outer) (represents hn ht ha hR outer) q v hv (word n outer upper) []
  simpa only [value,Function.comp_apply,probe,IntegralMixedFramedBankTermBits.source,
    RationalSubstitutionBits.Source.syntax,RationalSubstitutionBits.Source.ofTerm,
    IntegralMixedFramedBankTermBits.wordAt,word,TermView.term_toBits,childBank,key,
    IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair] using HP

theorem interval_iff (q v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer true) q v)
    (hg : Guard n outer q) :
    (value hn ht ha hR outer false (pair q v)=InfinitesimalSign.encode 1 ∧
      value hn ht ha hR outer true (pair q v)=InfinitesimalSign.encode 1) ↔
    (let env:=IntegralFramedPhysicalBankTerm.env (childBank hn ht ha hR outer)
      (tables hn ht ha hR outer) (represents hn ht ha hR outer) q v hv
     env (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.leftWord q))<env (birth n outer false q) ∧
      env (birth n outer false q)<env (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.rightWord q))) :=by
  rw [value_packet hn ht ha hR outer false q v hv,value_packet hn ht ha hR outer true q v hv]
  have HB : IntegralMixedPhysicalCriticalPrefixes.birth n outer false
      (pair (IntegralMixedPhysicalCriticalQuery.root q) [])=birth n outer false q :=by
    simp only [IntegralMixedPhysicalCriticalPrefixes.birth,IntegralMixedPhysicalCriticalQuery.root,pairFst_pair]
  have HL : IntegralMixedPhysicalCriticalQuery.leftWord (pair (IntegralMixedPhysicalCriticalQuery.root q) [])=
      IntegralMixedPhysicalCriticalQuery.leftWord q :=by
    simp only [IntegralMixedPhysicalCriticalQuery.leftWord,IntegralMixedPhysicalCriticalQuery.root,pairFst_pair]
  have HR : IntegralMixedPhysicalCriticalQuery.rightWord (pair (IntegralMixedPhysicalCriticalQuery.root q) [])=
      IntegralMixedPhysicalCriticalQuery.rightWord q :=by
    simp only [IntegralMixedPhysicalCriticalQuery.rightWord,IntegralMixedPhysicalCriticalQuery.root,pairFst_pair]
  simp only [term,Bool.false_eq_true,ite_false,ite_true,clipped,endpoint,
    HB,HL,HR,
    min_eq_left hg.2.1.le,min_eq_left hg.2.2.le,Term.eval,Int.cast_neg,Int.cast_one,
    neg_one_mul,SquareSampleTestSign.encode_eq_iff,sign_eq_one_iff,←sub_eq_add_neg,sub_pos]

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval
