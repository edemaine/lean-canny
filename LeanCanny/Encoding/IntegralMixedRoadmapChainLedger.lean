/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapChainChecked
public import LeanCanny.Encoding.IntegralMixedRoadmapPaddedWord
/-! # A native checked whole table is exactly a bounded typed record chain -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapChain
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedRoadmapRecordChain
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem count_nil :WordListRecords.count ([] : List Bool)=0:=WordListRecords.count_encode []

theorem seed_point_good (n current j : ℕ) (hj : j<n+1) :
    IntegralMixedChronologicalFrameCode.PointGood n current [] 0 j :=by
  refine ⟨⟨by rw [count_nil];omega,?_⟩,by rw [count_nil],by omega,by rw [count_nil];omega,hj⟩
  intro i hi
  rw [count_nil] at hi
  omega

noncomputable def seed (n initial C : ℕ) (i : Fin (n+2)) : Word (codeBound n initial C) :=
  if hi : i.val=0 then ⟨seedCode n,raw_point_code_length (Nat.le_add_right initial _) [] 0 0
    (seed_point_good n initial 0 (by omega))⟩
  else ⟨IntegralMixedChronologicalFrameCode.code n [] 0 (n-(i.val-1)),
    raw_point_code_length (Nat.le_add_right initial _) [] 0 _ (seed_point_good n initial _ (by omega))⟩

theorem seed_values (n initial C : ℕ) : (List.ofFn (seed n initial C)).map Subtype.val=seedCodes n :=by
  rw [List.map_ofFn]
  apply List.ext_getElem
  · simp only [List.length_ofFn,seedCodes,List.length_append,List.length_singleton,
      IntegralMixedChronologicalCompanionCode.codes,List.length_map,List.length_range,count_nil,Nat.sub_zero]
    omega
  · intro i hi hj
    simp only [List.getElem_ofFn,seedCodes,List.singleton_append,
      IntegralMixedChronologicalCompanionCode.codes,count_nil,Nat.sub_zero]
    cases i with
    | zero=>simp only [Function.comp_apply,seed,dite_true,List.getElem_cons_zero]
    | succ i=>simp only [Function.comp_apply,seed,show i+1≠0 by omega,dite_false,List.getElem_cons_succ,
        List.getElem_map,List.getElem_range,Nat.add_sub_cancel]

theorem level_codes (n : ℕ) (q : List Bool) (i : ℕ) :
    IntegralMixedRoadmapLevel.codes n (levelPacket n q i)=IntegralMixedRoadmapLevel.codes n (template q i) :=by
  have H:=congrArg WordListRecords.decode (level_compiled n q i)
  simpa only [IntegralMixedRoadmapLevel.compiled,WordListRecords.decode_encode] using H

def relevel {n k l T cap : ℕ} (h : k=l) (L : Level n k T cap) :Level n l T cap:=h▸L
theorem relevel_codes {n k l T cap : ℕ} (h : k=l) (L : Level n k T cap) :
    (relevel h L).codes=L.codes :=by cases h;rfl

noncomputable def typedLevel {n B sourceCap initial C : ℕ} {q : List Bool}
    (h : Checked n B sourceCap initial C q) (i : ℕ) (hi : i<depth q) :
    Level n i (codeBound n initial C) (maxBirth n initial) :=
  relevel (withSlice_k q i _) (originalLevel (level_checked h i hi) (level_end_bound h i hi) h.2.1)

theorem typedLevel_codes {n B sourceCap initial C : ℕ} {q : List Bool}
    (h : Checked n B sourceCap initial C q) (i : ℕ) (hi : i<depth q) :
    (typedLevel h i hi).codes.map Subtype.val=IntegralMixedRoadmapLevel.codes n (template q i) :=by
  rw [typedLevel,relevel_codes,originalLevel_codes]
  exact level_codes n q i

noncomputable def chainFrom {n B sourceCap initial C : ℕ} {q : List Bool}
    (h : Checked n B sourceCap initial C q) (k : ℕ) : (len : ℕ)→k+len≤depth q→Chain n (codeBound n initial C) (maxBirth n initial) k
  | 0,_=>.stop k
  | len+1,hk=>.descend k (by have HD:=h.1;omega) (typedLevel h k (by omega))
      (chainFrom h (k+1) len (by omega))

theorem chainFrom_codes {n B sourceCap initial C : ℕ} {q : List Bool}
    (h : Checked n B sourceCap initial C q) (k len : ℕ) (hk : k+len≤depth q) :
    (chainFrom h k len hk).codes.map Subtype.val=
      (List.range len).flatMap (fun j=>IntegralMixedRoadmapLevel.codes n (template q (k+j))) :=by
  induction len generalizing k with
  | zero=>rfl
  | succ len ih=>
    simp only [chainFrom,Chain.codes,List.map_append,typedLevel_codes,ih,List.range_succ_eq_map,
      List.flatMap_cons,List.flatMap_map,Nat.add_zero]
    simp only [Nat.add_comm,Nat.add_left_comm]

theorem chainFrom_depth {n B sourceCap initial C : ℕ} {q : List Bool}
    (h : Checked n B sourceCap initial C q) (k len : ℕ) (hk : k+len≤depth q) :
    (chainFrom h k len hk).depth=len :=by
  induction len generalizing k with
  | zero=>rfl
  | succ len ih=>simp only [chainFrom,Chain.depth,ih]

noncomputable def records {n B sourceCap initial C : ℕ} {q : List Bool}
    (h : Checked n B sourceCap initial C q) :Records n (codeBound n initial C) (maxBirth n initial) where
  seed:=seed n initial C
  chain:=chainFrom h 0 (depth q) (by omega)

theorem records_codes {n B sourceCap initial C : ℕ} {q : List Bool} (h : Checked n B sourceCap initial C q) :
    (records h).codes.map Subtype.val=meaningfulCodes n q :=by
  simp only [Records.codes,records,List.map_append,seed_values,chainFrom_codes,Nat.zero_add,meaningfulCodes]

theorem seedCodes_length (n : ℕ) :(seedCodes n).length=n+2 :=by
  simp only [seedCodes,List.length_append,List.length_singleton,IntegralMixedChronologicalCompanionCode.codes,
    List.length_map,List.length_range,count_nil,Nat.sub_zero]
  omega

private theorem flatMap_length (d : ℕ) (f : ℕ→List (List Bool)) :
    ((List.range d).flatMap f).length=∑i∈Finset.range d,(f i).length :=by
  induction d with
  | zero=>rfl
  | succ d ih=>simp only [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.length_append,ih,Finset.sum_range_succ]

theorem template_codes_length (n : ℕ) (q : List Bool) (i : ℕ) :
    (IntegralMixedRoadmapLevel.codes n (template q i)).length=blockCount n q i :=by
  rw [←level_codes,IntegralMixedRoadmapLevel.codes_length]
  exact level_count n q i

theorem meaningfulCodes_length (n : ℕ) (q : List Bool) :
    (meaningfulCodes n q).length=rawStart n q (depth q) :=by
  simp only [meaningfulCodes,List.length_append,seedCodes_length,flatMap_length,template_codes_length,rawStart,prefixCount]

theorem compiledCodes_length (n : ℕ) (q : List Bool) (hd : depth q≤n) :
    (compiledCodes n q).length=probedRecordBound n :=by
  have H:=rawStart_bound n q (depth q) (by omega)
  simp only [compiledCodes,List.length_append,meaningfulCodes_length,List.length_replicate,List.length_singleton]
  unfold paddingCount probedRecordBound
  omega

theorem records_length {n B sourceCap initial C : ℕ} {q : List Bool} (h : Checked n B sourceCap initial C q) :
    (records h).codes.length=rawStart n q (depth q) :=by
  have H:=congrArg List.length (records_codes h)
  simpa only [List.length_map,meaningfulCodes,List.length_append,seedCodes_length,flatMap_length,
    template_codes_length,rawStart,prefixCount] using H

noncomputable def reservedProbe {n B sourceCap initial C : ℕ} {q : List Bool}
    (h : Checked n B sourceCap initial C q) :Word (codeBound n initial C):=⟨probe q,h.2.2.2.2.2.2.2.1⟩

theorem raw_paddedWord {n B sourceCap initial C : ℕ} {q : List Bool} (h : Checked n B sourceCap initial C q) :
    raw q=(records h).paddedWord (seed n initial C ⟨0,by omega⟩) (reservedProbe h) :=by
  rw [h.2.2.2.2.2.1]
  simp only [compiled,compiledCodes,Records.paddedWord,Records.paddedCodes,List.map_append,List.map_replicate,
    List.map_cons,List.map_nil,records_codes,records_length,reservedProbe,seed,dite_true,paddingCount]

theorem records_depth {n B sourceCap initial C : ℕ} {q : List Bool} (h : Checked n B sourceCap initial C q) :
    (records h).chain.depth=depth q :=chainFrom_depth _ _ _ _

theorem raw_length_le {n B sourceCap initial C : ℕ} {q : List Bool} (h : Checked n B sourceCap initial C q) :
    (raw q).length≤(2*codeBound n initial C+2)*probedRecordBound n :=by
  rw [raw_paddedWord h]
  exact (records h).paddedWord_length _ _

end LeanCanny.Encoding.IntegralMixedRoadmapChain
