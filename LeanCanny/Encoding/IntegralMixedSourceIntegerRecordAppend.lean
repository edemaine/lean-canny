/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSourceIntegerCausalAppend
public import LeanCanny.Encoding.IntegralMixedCausalRecordPlan
/-! # Raw causal records start at the actual post-prelude scalar birth

The raw table is chronological. Its relative row b uses absolute birth N+b
for both source selection and retained-reference decoding. The integer
prelude remains charged through its original polynomial source.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedCausalRecordBits IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (N : List Bool→ℕ)

noncomputable def step (root : List Bool) (b : ℕ) : Record (P.ambient root) (P.width root) :=
  IntegralMixedCausalUnitRecordBits.record (S root (N root+b)) (hn root) (N root+b)
    (IntegralMixedCausalRecordPlanBits.code root b) (by rw [hd]; exact hcap root)
noncomputable def later (root : List Bool) :=
  ((List.range (IntegralMixedCausalRecordPlanBits.count root)).map (step P S hn hd hcap N root)).reverse

theorem later_length (root : List Bool) :
    (later P S hn hd hcap N root).length=IntegralMixedCausalRecordPlanBits.count root := by
  simp only [later,List.length_reverse,List.length_map,List.length_range]

theorem later_noninteger (root : List Bool) : ∀r∈later P S hn hd hcap N root,
    IntegralMixedSourceIntegerPrelude.templatePolynomial r.template=Polynomial.X := by
  intro r hr
  rw [later,List.mem_reverse] at hr
  obtain ⟨b,_,rfl⟩:=List.mem_map.mp hr
  unfold step IntegralMixedCausalUnitRecordBits.record
  cases IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code root b) <;> rfl

variable (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
  (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)

noncomputable def plan : Plan P :=
  IntegralMixedSourceIntegerPrelude.extendedPlan P (fun root=>S root 0) (fun root=>hd root 0) hcap T N hz hT
    (later P S hn hd hcap N) (fun root=>by rw [later_length]; exact hroom root)

theorem integerOriginal (a : Access P) (hA : IntegerPolynomialRootQueriesBits.Access T) (hN : UnaryFn N) :
    IntegralMixedIntegerFamilyBits.Original P (IntegralMixedFramedIntegerBits.polynomial P
      (plan P S hn hd hcap N T hz hT hroom)) :=
  IntegralMixedSourceIntegerPrelude.extended_original P (fun root=>S root 0) (fun root=>hd root 0) hcap T N hz hT
    (later P S hn hd hcap N) (fun root=>by rw [later_length]; exact hroom root) a hA hN
    (later_noninteger P S hn hd hcap N)

def selectedCode (key : List Bool) :=
  let b:=prefixLength P key
  let root:=pairFst key
  if N root≤b ∧ b<N root+IntegralMixedCausalRecordPlanBits.count root then
    IntegralMixedCausalRecordPlanBits.code root (b-N root) else []

theorem selectedCode_FP (a : Access P) (hN : UnaryFn N) : selectedCode P N∈FP := by
  have HB:=IntegralMixedFullHistoryFamilyBits.prefix_unary P a
  have HN:=hN.comp pairFst_mem_FP
  have HC:=IntegralMixedCausalRecordPlanBits.count_unary.comp pairFst_mem_FP
  have HP:=((BinaryFn.ofUnary HN).le (BinaryFn.ofUnary HB)).and
    ((BinaryFn.ofUnary HB).lt (BinaryFn.ofUnary (HN.add HC)))
  have HI : BinaryFn (fun key=>prefixLength P key-N (pairFst key)) :=
    (BinaryFn.ofUnary HB).sub (BinaryFn.ofUnary HN)
  have HR:=mem_FP_comp (g:=WordList.reader) (mem_FP_pair
    (mem_FP_comp pairFst_mem_FP IntegralMixedCausalRecordPlanBits.records_FP) HI.bits_mem_FP) WordList.reader_FP
  exact mem_FP_of_eq (HP.ite_mem_FP HR (constFn_mem_FP [])) (fun key=>by
    simp only [selectedCode,Function.comp_apply,WordList.reader,pairFst_pair,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits,IntegralMixedCausalRecordPlanBits.code])

theorem step_source (root : List Bool) (b : ℕ) : (step P S hn hd hcap N root b).source=S root (N root+b) := rfl

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
