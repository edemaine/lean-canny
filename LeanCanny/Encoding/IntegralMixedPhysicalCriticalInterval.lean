/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankEquality
public import LeanCanny.Encoding.IntegralFramedPhysicalBankTermPoint
public import LeanCanny.Encoding.IntegralFramedPhysicalCriticalGuardTest
public import LeanCanny.Geometry.IntegralMixedFramedCriticalGuard
public import LeanCanny.Computation.SpaceFunctionWordExistence
/-! # Native exhaustive full-joint search for a parent-correlated critical probe

Every complete child word is considered, including singular roots. The fixed
parent word and both interval endpoints belong to the same prepared target cap.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank native tables tables_native represents)
open IntegralMixedPhysicalCriticalPrefixes (birth key key_birth positive input)
open IntegralMixedPhysicalCriticalQuery (parentWord leftWord rightWord)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

noncomputable def childBank : IntegralFramedBankQuery.Bank :=
  {bank hn ht ha hR outer with
    key:=key n outer true
    positive:=positive hn ht ha hR outer true
    coordinate q:=⟨0,positive hn ht ha hR outer true q⟩}

noncomputable def childAccess : IntegralFramedBankQuery.Access (childBank hn ht ha hR outer) :=
  {native hn ht ha hR outer with
    key:=IntegralMixedPhysicalCriticalPrefixes.key_FP hn outer true
    coordinate:=UnaryFn.const 0}

def tail (saved : List Bool) :=pairSnd (pairSnd saved)
def endpoint (right : Bool) (q : List Bool) :=if right then rightWord q else leftWord q
def clipped (n : List Bool→ℕ) (outer right : Bool) (q : List Bool) :=
  min (Nat.fromBitsLE (endpoint right q)) (birth n outer false q)
include hn in
theorem clipped_unary (right : Bool) : UnaryFn (clipped n outer right) := by
  have HE : endpoint right∈FP :=by cases right <;> polytime [endpoint,rightWord,leftWord,IntegralMixedPhysicalCriticalQuery.root]
  exact UnaryFn.fromBitsLE_min HE (IntegralMixedPhysicalCriticalPrefixes.birth_unary hn outer false)

def term (n : List Bool→ℕ) (outer upper : Bool) (original : List Bool) : Term :=
  if upper then .add (.var (clipped n outer true (pair original [])))
    (.mul (.const (-1)) (.var (birth n outer false (pair original []))))
  else .add (.var (birth n outer false (pair original [])))
    (.mul (.const (-1)) (.var (clipped n outer false (pair original []))))
def word (n : List Bool→ℕ) (outer upper : Bool) (saved : List Bool) :=(term n outer upper saved).toData.toBits

include hn in
theorem word_FP (upper : Bool) : word n outer upper∈FP := by
  have HT : (fun q : List Bool=>pair q [])∈FP :=mem_FP_pair id_mem_FP (constFn_mem_FP [])
  have HN:=Term.variableBits_mem_FP ((IntegralMixedPhysicalCriticalPrefixes.birth_unary hn outer false).comp HT)
  have HE (r : Bool):=Term.variableBits_mem_FP ((clipped_unary hn outer r).comp HT)
  have HK:=(constFn_mem_FP (Term.const (-1)).toData.toBits)
  cases upper
  · exact mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 HN (Codec.taggedTwo_mem_FP 3 HK (HE false)))
      (fun _=>by simp only [word,term,Term.variableBits_eq,Term.toData,Codec.taggedTwo_toBits];rfl)
  · exact mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 (HE true) (Codec.taggedTwo_mem_FP 3 HK HN))
      (fun _=>by simp only [word,term,Term.variableBits_eq,Term.toData,Codec.taggedTwo_toBits];rfl)

def probe (z : List Bool) :=pair z []
theorem probe_FP : probe∈FP :=mem_FP_pair id_mem_FP (constFn_mem_FP [])
noncomputable def value (upper : Bool) :=IntegralFramedPhysicalBankTerm.value (childBank hn ht ha hR outer)
  (tables hn ht ha hR outer) (represents hn ht ha hR outer) (word n outer upper)∘probe

attribute [local irreducible] bank native childAccess value

theorem evaluator (upper : Bool) : SpaceFunction (value hn ht ha hR outer upper) :=by
  unfold value
  exact (IntegralFramedPhysicalBankTerm.evaluator (childBank hn ht ha hR outer)
    (tables hn ht ha hR outer) (represents hn ht ha hR outer) (childAccess hn ht ha hR outer)
    (tables_native hn ht ha hR outer) (word n outer upper) (word_FP hn outer upper)
    (IntegralMixedPhysicalCriticalPrefixes.row_evaluator hn ht ha hR outer true)).precompose probe probe_FP

theorem guard_count (q d : List Bool) :
    IntegralMixedFramedCriticalGuardBits.count (bank hn ht ha hR outer).parameters
      (tables hn ht ha hR outer) (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true)) (pair q d)=
        (input hn ht ha hR outer true).count q :=by
  change _=IntegralMixedFramedPhysicalIndex.arity (IntegralMixedFramedHistoryFamilyBits.commands
    (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (key n outer true q))
  have E:=IntegralMixedFramedCriticalGuardBits.count_actual
    (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
    (tables hn ht ha hR outer) (represents hn ht ha hR outer)
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true)) (pair q d)
  have HK : IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true) (pair q d)=key n outer true q :=
    congrArg (key n outer true) (pairFst_pair q d)
  exact E.trans (congrArg (fun k=>IntegralMixedFramedPhysicalIndex.arity
    (IntegralMixedFramedHistoryFamilyBits.commands (bank hn ht ha hR outer).parameters
      (bank hn ht ha hR outer).plan k)) HK)

def stage (n : List Bool→ℕ) (outer : Bool) (z : List Bool) :=birth n outer false (pairFst z)
noncomputable def correlation :=IntegralFramedPhysicalCriticalGuardTest.value (input hn ht ha hR outer true)
  (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
  (tables hn ht ha hR outer) (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor
  (bank hn ht ha hR outer).seed (bank hn ht ha hR outer).bounds (key n outer true) (stage n outer)
  (guard_count hn ht ha hR outer)∘probe

theorem correlation_evaluator : SpaceFunction (correlation hn ht ha hR outer) :=by
  let B:=bank hn ht ha hR outer
  let A:=native hn ht ha hR outer
  exact (IntegralFramedPhysicalCriticalGuardTest.evaluator (input hn ht ha hR outer true)
    B.parameters B.plan B.data (tables hn ht ha hR outer) B.nodes B.factor B.seed B.bounds
    (key n outer true) (stage n outer) (guard_count hn ht ha hR outer)
    (IntegralMixedPhysicalCriticalPrefixes.access hn ht ha hR outer true)
    A.parameters (tables_native hn ht ha hR outer) A.liftedData A.controls A.bounds A.nodes A.factor A.seed
    (IntegralMixedPhysicalCriticalPrefixes.key_FP hn outer true)
    ((IntegralMixedPhysicalCriticalPrefixes.birth_unary hn outer false).comp pairFst_mem_FP)).precompose probe probe_FP

def Guard (n : List Bool→ℕ) (outer : Bool) (q : List Bool) : Prop :=
  IntegralMixedPhysicalCriticalQuery.critical q ∧
    Nat.fromBitsLE (leftWord q)<birth n outer false q ∧ Nat.fromBitsLE (rightWord q)<birth n outer false q
include hn in
theorem guard_FP : FPPred (Guard n outer) :=
  IntegralMixedPhysicalCriticalQuery.critical_FP.and
    (((BinaryFn.fromBits (by polytime [leftWord,IntegralMixedPhysicalCriticalQuery.root])).lt
      (BinaryFn.ofUnary (IntegralMixedPhysicalCriticalPrefixes.birth_unary hn outer false))).and
    ((BinaryFn.fromBits (by polytime [rightWord,IntegralMixedPhysicalCriticalQuery.root])).lt
      (BinaryFn.ofUnary (IntegralMixedPhysicalCriticalPrefixes.birth_unary hn outer false))))

noncomputable def witnessLanguage : Language := {z |
  Guard n outer (pairFst z) ∧
  SquareSampleCompleteVertices.Valid (input hn ht ha hR outer false) (pairFst z) (parentWord (pairFst z)) ∧
  SquareSampleCompleteVertices.Valid (input hn ht ha hR outer true) (pairFst z) (pairSnd z) ∧
  IntegralMixedPhysicalCriticalBankEquality.agrees hn ht ha hR outer z ∧
  correlation hn ht ha hR outer z=InfinitesimalSign.encode 0 ∧
  value hn ht ha hR outer false z=InfinitesimalSign.encode 1 ∧
  value hn ht ha hR outer true z=InfinitesimalSign.encode 1}

theorem witness_decider : SpaceDecider (witnessLanguage hn ht ha hR outer) :=by
  have GP:=SpaceFunction.ofFP _ (((guard_FP hn outer).comp pairFst_mem_FP).flag_mem_FP)
  have P:=((SquareSampleCompleteVertices.decider (IntegralMixedPhysicalCriticalPrefixes.access hn ht ha hR outer false)).precompose
    (fun z=>pair (pairFst z) (parentWord (pairFst z))) (by polytime [parentWord])).flagEvaluator
  have C:=(SquareSampleCompleteVertices.decider (IntegralMixedPhysicalCriticalPrefixes.access hn ht ha hR outer true)).flagEvaluator
  have A:=IntegralMixedPhysicalCriticalBankEquality.scanEvaluator hn ht ha hR outer
  have G:=(correlation_evaluator hn ht ha hR outer).postcompose (fun z=>[decide (z=InfinitesimalSign.encode 0)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  have L:=(evaluator hn ht ha hR outer false).postcompose (fun z=>[decide (z=InfinitesimalSign.encode 1)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  have U:=(evaluator hn ht ha hR outer true).postcompose (fun z=>[decide (z=InfinitesimalSign.encode 1)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  apply (GP.andFlags (P.andFlags (C.andFlags (A.andFlags (G.andFlags (L.andFlags U)))))).decider
    (fun z=>decide (z=[true])) (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [witnessLanguage,Set.mem_ofPred_eq,Set.mem_preimage,SquareSampleCompleteVertices.language,
    pairFst_pair,pairSnd_pair,Function.comp_apply,List.cons.injEq,and_true,decide_eq_true_eq]

noncomputable def width (q : List Bool) :=SquareSampleCompleteVertices.width (input hn ht ha hR outer true) q
theorem width_unary : UnaryFn (width hn ht ha hR outer) :=
  SquareSampleCompleteVertices.width_unary (IntegralMixedPhysicalCriticalPrefixes.access hn ht ha hR outer true)
noncomputable def language : Language := {q |∃w : List Bool,
  w.length=width hn ht ha hR outer q ∧ pair q w∈witnessLanguage hn ht ha hR outer}

theorem decider : SpaceDecider (language hn ht ha hR outer) :=by
  have E:=(witness_decider hn ht ha hR outer).flagEvaluator.exists_words (width_unary hn ht ha hR outer)
  apply E.decider (fun z=>decide (z=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

theorem mem_PSPACE : language hn ht ha hR outer∈PSPACE :=(decider hn ht ha hR outer).mem_PSPACE

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval
