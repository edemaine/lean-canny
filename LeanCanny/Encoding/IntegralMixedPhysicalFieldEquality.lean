/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankEquality
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedNative
/-! # Cross-context equality reads one old integer polynomial on both words

The two full sampler contexts and words remain literal. Only an indexed test
datum transports the LEFT integer polynomial to the right evaluation.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalFieldEquality
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank native tables tables_native represents)
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def sample (right : Bool) (z : List Bool) :=if right then pairFst (pairSnd z) else pairFst z
def context (right : Bool) (z : List Bool) :=pairFst (sample right z)
def word (right : Bool) (z : List Bool) :=pairSnd (sample right z)
def labelWord (right : Bool) (z : List Bool) :=
  if right then pairSnd (pairSnd (pairSnd z)) else pairFst (pairSnd (pairSnd z))
def label (right : Bool) (z : List Bool) :=Nat.fromBitsLE (labelWord right z)
theorem sample_FP (right : Bool) : sample right∈FP:=by cases right <;> polytime [sample]
theorem context_FP (right : Bool) : context right∈FP:=mem_FP_comp (sample_FP right) pairFst_mem_FP
theorem word_FP (right : Bool) : word right∈FP:=mem_FP_comp (sample_FP right) pairSnd_mem_FP
theorem labelWord_FP (right : Bool) : labelWord right∈FP:=by cases right <;> polytime [labelWord]
theorem label_binary (right : Bool) : BinaryFn (label right):=BinaryFn.fromBits (labelWord_FP right)
def packet (cL wL cR wR : List Bool) (a b : ℕ) :=pair (pair cL wL)
  (pair (pair cR wR) (pair (BinaryNatCode.encode a) (BinaryNatCode.encode b)))
def canonical (z : List Bool) :=packet (context false z) (word false z) (context true z) (word true z)
  (label false z) (label true z)
theorem canonical_FP : canonical∈FP:=mem_FP_pair
  (mem_FP_pair (context_FP false) (word_FP false))
  (mem_FP_pair (mem_FP_pair (context_FP true) (word_FP true))
    (mem_FP_pair (label_binary false).bits_mem_FP (label_binary true).bits_mem_FP))
def Wellformed (z : List Bool) :=z=canonical z
theorem wellformed_FP : FPPred Wellformed:=Brackets.stringEq_fppred id_mem_FP canonical_FP
theorem packet_fields (cL wL cR wR : List Bool) (a b : ℕ) :
    context false (packet cL wL cR wR a b)=cL ∧ word false (packet cL wL cR wR a b)=wL ∧
    context true (packet cL wL cR wR a b)=cR ∧ word true (packet cL wL cR wR a b)=wR ∧
    label false (packet cL wL cR wR a b)=a ∧ label true (packet cL wL cR wR a b)=b :=by
  simp only [context,word,sample,label,labelWord,packet,Bool.false_eq_true,ite_false,ite_true,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,and_self]

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)
local notation "B" => bank hn ht ha hR false
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "D" => IntegralFramedBankQuery.Bank.plan B
local notation "H" => IntegralFramedBankQuery.Bank.data B
local notation "G" => family P D H
local notation "S" => IntegralMixedPhysicalMarkedTest.input hn ht ha hR false
attribute [local irreducible] bank native tables family

noncomputable def count (c : List Bool) :=(G).birth ((B).key c)
theorem count_unary : UnaryFn (count hn ht ha hR) :=
  (IntegralMixedFramedBankSnapshotBits.count_unary P (native hn ht ha hR false).parameters D H).comp
    (native hn ht ha hR false).key
theorem count_pos (c : List Bool) : 0<count hn ht ha hR c :=(B).positive c
def newest (birth chronological : ℕ) :=birth-1-min chronological (birth-1)
theorem newest_lt (birth chronological : ℕ) (hb : 0<birth) : newest birth chronological<birth :=by
  unfold newest
  omega
noncomputable def selected (right : Bool) (z : List Bool) :=newest (count hn ht ha hR (context right z)) (label right z)
theorem selected_unary (right : Bool) : UnaryFn (selected hn ht ha hR right) :=
  let HC:=((count_unary hn ht ha hR).comp (context_FP right)).sub (UnaryFn.const 1)
  HC.sub (UnaryFn.fromBitsLE_min (labelWord_FP right) HC)
theorem selected_val (right : Bool) (z : List Bool)
    (hb : label right z<count hn ht ha hR (context right z)) :
    selected hn ht ha hR right z=count hn ht ha hR (context right z)-1-label right z :=by
  unfold selected newest
  rw [min_eq_left (by omega)]

noncomputable def originalSource:=IntegralMixedPhysicalCriticalBankEquality.originalSource hn ht ha hR false
theorem originalAccess : IntegerPolynomialRootQueriesBits.Access (originalSource hn ht ha hR):=
  IntegralMixedPhysicalCriticalBankEquality.originalAccess hn ht ha hR false
def derivativePacket (p : List Bool) :=pair (pairFst (pairSnd p)) (pairSnd (pairSnd (pairSnd p)))
theorem derivativePacket_FP : derivativePacket∈FP:=by polytime [derivativePacket]
noncomputable def derivatives:=IntegerPolynomialSourceChoice.reindex
  (IntegerPolynomialIteratedDerivativeBits.source (originalSource hn ht ha hR)) derivativePacket
theorem derivatives_access : IntegerPolynomialRootQueriesBits.Access (derivatives hn ht ha hR):=
  IntegerPolynomialSourceChoice.reindex_access _
    (IntegerPolynomialIteratedDerivativeBits.access (originalAccess hn ht ha hR)) derivativePacket_FP

noncomputable def coordinate (c d : List Bool) : Fin ((G).birth ((B).key c)) :=
  ⟨min (Nat.fromBitsLE (pairFst (pairSnd d))) (count hn ht ha hR c-1),by
    change min (Nat.fromBitsLE (pairFst (pairSnd d))) (count hn ht ha hR c-1)<count hn ht ha hR c
    have HB:=count_pos hn ht ha hR c
    exact lt_of_le_of_lt (min_le_right _ _) (by omega)⟩
noncomputable def value:=IntegralFramedPhysicalUnivariateTest.value P D H (B).nodes (B).factor (B).seed
  (B).bounds (B).key (B).positive (coordinate hn ht ha hR) (derivatives hn ht ha hR)
attribute [local irreducible] coordinate derivatives originalSource value
theorem evaluator : SpaceFunction (value hn ht ha hR) :=by
  have HI0 : UnaryFn (fun z=>min (Nat.fromBitsLE (pairFst (pairSnd (pairSnd z))))
      (count hn ht ha hR (pairFst z)-1)):=
    UnaryFn.fromBitsLE_min (by polytime)
      (((count_unary hn ht ha hR).comp pairFst_mem_FP).sub (UnaryFn.const 1))
  have HI : UnaryFn (IntegralFramedPhysicalUnivariateTest.selected P D H (B).key (coordinate hn ht ha hR)) :=
    HI0.of_eq (fun z=>by simp only [IntegralFramedPhysicalUnivariateTest.selected,coordinate])
  unfold value
  exact IntegralFramedPhysicalUnivariateTest.evaluator P (native hn ht ha hR false).parameters D H
    (tables hn ht ha hR false) (tables_native hn ht ha hR false) (represents hn ht ha hR false)
    (B).key (native hn ht ha hR false).key (coordinate hn ht ha hR) HI
    (native hn ht ha hR false).liftedData (native hn ht ha hR false).controls (native hn ht ha hR false).bounds
    (native hn ht ha hR false).nodes (native hn ht ha hR false).factor (native hn ht ha hR false).seed
    (B).bounds _ (derivatives_access hn ht ha hR) (B).positive (IntegralMixedPhysicalMarkedNative.row_evaluator hn ht ha hR false)

noncomputable def oldArgument (z : List Bool) :=pair ((B).key (context false z))
  (BinaryNatCode.encode (selected hn ht ha hR false z))
theorem oldArgument_FP : oldArgument hn ht ha hR∈FP:=mem_FP_pair
  (mem_FP_comp (context_FP false) (native hn ht ha hR false).key)
  (BinaryFn.ofUnary (selected_unary hn ht ha hR false)).bits_mem_FP
noncomputable def probe (right : Bool) (r : List Bool) :=pair (sample right (pairFst r))
  (pair (oldArgument hn ht ha hR (pairFst r))
    (pair (BinaryNatCode.encode (selected hn ht ha hR right (pairFst r))) (pairSnd r)))
theorem probe_FP (right : Bool) : probe hn ht ha hR right∈FP:=mem_FP_pair
  (mem_FP_comp pairFst_mem_FP (sample_FP right))
  (mem_FP_pair (mem_FP_comp pairFst_mem_FP (oldArgument_FP hn ht ha hR))
    (mem_FP_pair (BinaryFn.ofUnary ((selected_unary hn ht ha hR right).comp pairFst_mem_FP)).bits_mem_FP pairSnd_mem_FP))
noncomputable def degree (z : List Bool) :=(originalSource hn ht ha hR).degree (oldArgument hn ht ha hR z)
theorem degree_binary : BinaryFn (degree hn ht ha hR):=
  (originalAccess hn ht ha hR).degree.comp (oldArgument_FP hn ht ha hR)
noncomputable def agrees (z : List Bool) : Prop :=∀k<degree hn ht ha hR z+1,
  value hn ht ha hR (probe hn ht ha hR false (pair z (BinaryNatCode.encode k)))=
    value hn ht ha hR (probe hn ht ha hR true (pair z (BinaryNatCode.encode k)))
theorem agrees_evaluator : SpaceFunction (fun z=>[decide (agrees hn ht ha hR z)]) :=by
  have EL:=(evaluator hn ht ha hR).precompose (probe hn ht ha hR false) (probe_FP hn ht ha hR false)
  have ER:=(evaluator hn ht ha hR).precompose (probe hn ht ha hR true) (probe_FP hn ht ha hR true)
  have E:=(EL.pairOutputs ER).postcompose (fun p=>[decide (pairFst p=pairSnd p)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  exact (E.forall_binary ((degree_binary hn ht ha hR).add (BinaryFn.const 1))).congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [agrees,Function.comp_apply,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq])

noncomputable def Labels (z : List Bool) :=label false z<count hn ht ha hR (context false z) ∧
  label true z<count hn ht ha hR (context true z)
theorem labels_FP : FPPred (Labels hn ht ha hR):=
  ((label_binary false).lt (BinaryFn.ofUnary ((count_unary hn ht ha hR).comp (context_FP false)))).and
    ((label_binary true).lt (BinaryFn.ofUnary ((count_unary hn ht ha hR).comp (context_FP true))))
noncomputable def language : Language:={z |Wellformed z ∧
  SquareSampleCompleteVertices.Valid S (context false z) (word false z) ∧
  SquareSampleCompleteVertices.Valid S (context true z) (word true z) ∧Labels hn ht ha hR z ∧agrees hn ht ha hR z}
theorem decider : SpaceDecider (language hn ht ha hR) :=by
  have EV (right : Bool):=((SquareSampleCompleteVertices.decider (IntegralMixedPhysicalMarkedNative.access hn ht ha hR false)).precompose
    (sample right) (sample_FP right)).flagEvaluator
  have EW:=SpaceFunction.ofFP _ wellformed_FP.flag_mem_FP
  have EB:=SpaceFunction.ofFP _ (labels_FP hn ht ha hR).flag_mem_FP
  apply (EW.andFlags ((EV false).andFlags ((EV true).andFlags (EB.andFlags (agrees_evaluator hn ht ha hR))))).decider
    (fun v=>decide (v=[true])) (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [language,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,Set.mem_preimage,context,word,
    List.cons.injEq,and_true,decide_eq_true_eq]
theorem mem_PSPACE : language hn ht ha hR∈PSPACE:=(decider hn ht ha hR).mem_PSPACE

end LeanCanny.Encoding.IntegralMixedPhysicalFieldEquality
