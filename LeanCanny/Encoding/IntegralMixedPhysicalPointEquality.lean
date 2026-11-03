/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalPointEqualityTest
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedNative
public import LeanCanny.Encoding.IntegralMixedPhysicalGuardScan
/-! # Original-only physical point comparisons retain their full context

The indexed datum contains unary creating births and a binary ambient index.
No query replaces the full sampler context or its complete-root word.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalPointEquality
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank native tables tables_native represents)
open IntegralFramedPhysicalCriticalGuardTest (keyDatum)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] bank native tables IntegralMixedFramedHistoryFamilyBits.family
  IntegralFramedPhysicalPointEqualityTest.value
  IntegralMixedFramedPhysicalIndex.prefixArity UniformIntegralPowerSchedule.physical

def datum (a b i : ℕ) :=pair (List.replicate a true) (pair (List.replicate b true) (BinaryNatCode.encode i))
def left (r : List Bool) :=(pairFst (pairSnd r)).length
def right (r : List Bool) :=(pairFst (pairSnd (pairSnd r))).length
def coordinate (r : List Bool) :=Nat.fromBitsLE (pairSnd (pairSnd (pairSnd r)))
theorem left_unary : UnaryFn left:=UnaryFn.length (by polytime)
theorem right_unary : UnaryFn right:=UnaryFn.length (by polytime)
theorem coordinate_binary : BinaryFn coordinate:=BinaryFn.fromBits (by polytime)
def context (q : List Bool) :=pair (pairFst (pairFst q)) (pairSnd q)
theorem context_FP : context∈FP:=by polytime [context]
theorem datum_fields (c : List Bool) (a b i : ℕ) :
    left (pair c (datum a b i))=a ∧ right (pair c (datum a b i))=b ∧ coordinate (pair c (datum a b i))=i :=by
  simp only [left,right,coordinate,datum,pairFst_pair,pairSnd_pair,List.length_replicate,
    BinaryNatCode.encode,Nat.fromBitsLE_bits,and_self]
def canonical (q : List Bool) :=pair (pair (pairFst (pairFst q)) (pairSnd (pairFst q)))
  (datum (left (context q)) (right (context q)) (coordinate (context q)))
theorem canonical_FP : canonical∈FP:=by
  have HI : BinaryFn (coordinate∘context):=coordinate_binary.comp context_FP
  exact mem_FP_pair (by polytime) (mem_FP_pair (left_unary.comp context_FP).mem_FP
    (mem_FP_pair (right_unary.comp context_FP).mem_FP HI.bits_mem_FP))
def Wellformed (q : List Bool) :=q=canonical q
theorem wellformed_FP : FPPred Wellformed:=Brackets.stringEq_fppred id_mem_FP canonical_FP
theorem wellformed_packet (c w : List Bool) (a b i : ℕ) :Wellformed (pair (pair c w) (datum a b i)) :=by
  simp only [Wellformed,canonical,context,left,right,coordinate,datum,pairFst_pair,pairSnd_pair,
    List.length_replicate,BinaryNatCode.encode,Nat.fromBitsLE_bits]

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)
local notation "B" => bank hn ht ha hR outer
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "T" => tables hn ht ha hR outer
local notation "S" => IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer
local notation "HC" => IntegralMixedPhysicalGuardScan.count_eq hn ht ha hR outer

noncomputable def value:=IntegralFramedPhysicalPointEqualityTest.value S P T (B).key left right coordinate HC
theorem evaluator : SpaceFunction (value hn ht ha hR outer) :=by
  unfold value
  exact IntegralFramedPhysicalPointEqualityTest.evaluator S P T (B).key left right coordinate HC
    (IntegralMixedPhysicalMarkedNative.access hn ht ha hR outer) (native hn ht ha hR outer).parameters
    (tables_native hn ht ha hR outer) (native hn ht ha hR outer).key left_unary right_unary coordinate_binary

noncomputable def Admissible (q : List Bool) :=IntegralMixedFramedPointEqualityBits.Admissible P T
  (keyDatum (B).key) left right coordinate (context q)
theorem admissible_FP : FPPred (Admissible hn ht ha hR outer) :=
  (IntegralMixedFramedPointEqualityBits.admissible_FP P T (keyDatum (B).key) left right coordinate
    (native hn ht ha hR outer).parameters (tables_native hn ht ha hR outer)
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum_FP (B).key (native hn ht ha hR outer).key)
    left_unary right_unary coordinate_binary).comp context_FP
noncomputable def Accepted (q : List Bool) :=Wellformed q ∧ Admissible hn ht ha hR outer q ∧
  value hn ht ha hR outer q=InfinitesimalSign.encode 0
theorem accepted_evaluator : SpaceFunction (fun q=>[decide (Accepted hn ht ha hR outer q)]) :=by
  have EA:SpaceFunction (fun q=>[decide (Wellformed q ∧ Admissible hn ht ha hR outer q)]):=
    SpaceFunction.ofFP _ (wellformed_FP.and (admissible_FP hn ht ha hR outer)).flag_mem_FP
  have EZ:=(evaluator hn ht ha hR outer).postcompose (fun v=>[decide (v=InfinitesimalSign.encode 0)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  exact (EA.andFlags EZ).congr (funext fun q=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Accepted,Function.comp_apply,List.cons.injEq,and_true,decide_eq_true_eq,and_assoc])

noncomputable def block (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (b i : ℕ) : ℝ :=
  let col:=IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key c) (List.replicate b true))+i
  if hc : col<(S).count c then (SquareSampleCompleteVertices.candidate S c w hv).val ⟨col,hc⟩^
    IntegralMixedFramedCriticalGuardBits.physicalPower P (B).key (fun _=>b) c else 0

theorem zero_iff_block (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (a b i : ℕ)
    (h : Admissible hn ht ha hR outer (pair (pair c w) (datum a b i))) :
    value hn ht ha hR outer (pair (pair c w) (datum a b i))=InfinitesimalSign.encode 0 ↔
      block hn ht ha hR outer c w hv a i=block hn ht ha hR outer c w hv b i :=by
  have h':=h
  simp only [Admissible,context,pairFst_pair,pairSnd_pair] at h'
  have HE:=IntegralFramedPhysicalPointEqualityTest.zero_iff S P T (B).key left right coordinate HC c w
    (datum a b i) hv h'
  have HL:=IntegralMixedFramedPointEqualityBits.column_lt P T (keyDatum (B).key) coordinate left
    (pair c (datum a b i)) h'.1 h'.2.2
  have HR:=IntegralMixedFramedPointEqualityBits.column_lt P T (keyDatum (B).key) coordinate right
    (pair c (datum a b i)) h'.2.1 h'.2.2
  have HN:=HC c (datum a b i)
  have HL' : IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key c) (List.replicate a true))+i<(S).count c :=by
    simpa only [IntegralMixedFramedPointEqualityBits.column,IntegralMixedFramedCriticalGuardBits.packet,
      keyDatum,left,coordinate,datum,pairFst_pair,pairSnd_pair,List.length_replicate,BinaryNatCode.encode,
      Nat.fromBitsLE_bits] using HL.trans_eq HN
  have HR' : IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key c) (List.replicate b true))+i<(S).count c :=by
    simpa only [IntegralMixedFramedPointEqualityBits.column,IntegralMixedFramedCriticalGuardBits.packet,
      keyDatum,right,coordinate,datum,pairFst_pair,pairSnd_pair,List.length_replicate,BinaryNatCode.encode,
      Nat.fromBitsLE_bits] using HR.trans_eq HN
  simpa only [value,IntegralMixedFramedPointEqualityBits.point,IntegralFramedPhysicalPointEqualityTest.tuple,
    block,left,right,coordinate,datum,IntegralMixedFramedCriticalGuardBits.packet,keyDatum,
    pairFst_pair,pairSnd_pair,List.length_replicate,BinaryNatCode.encode,Nat.fromBitsLE_bits,
    dite_eq_left HL',dite_eq_left HR',Fin.cast,IntegralMixedFramedCriticalGuardBits.physicalPower] using HE

end LeanCanny.Encoding.IntegralMixedPhysicalPointEquality
