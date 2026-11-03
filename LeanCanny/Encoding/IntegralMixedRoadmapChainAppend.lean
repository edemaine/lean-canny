/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapChainConstruction
/-! # A newly appended level preserves the literal earlier chain

Metadata is chronological. Earlier frozen labels, programs and record offsets
therefore do not depend on the new entry or the final reserved probe.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapChain
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def levelEntry (l r : List Bool) (side : Bool) :=WordList.encode [l,r,if side then [true] else []]
def appendPayload (n : ℕ) (q l r : List Bool) (side : Bool) (p : List Bool) :=
  completePayload n (WordList.encode (WordListRecords.decode (metadata q)++[levelEntry l r side])) p

theorem append_depth (n : ℕ) (q l r : List Bool) (side : Bool) (p : List Bool) :
    depth (appendPayload n q l r side p)=depth q+1 :=by
  simp only [depth,appendPayload,completePayload_metadata,WordListRecords.count_encode,
    List.length_append,WordListRecords.length_decode,List.length_singleton]

theorem append_entry_before (n : ℕ) (q l r : List Bool) (side : Bool) (p : List Bool)
    (i : ℕ) (hi : i<depth q) : entry (appendPayload n q l r side p) i=entry q i :=by
  have HL : i<(WordListRecords.decode (metadata q)).length:=by
    rw [WordListRecords.length_decode]
    exact hi
  simp only [entry,appendPayload,completePayload_metadata,WordList.get_encode]
  rw [List.getElem?_append_left HL]
  simp only [depth] at hi
  simp only [WordListRecords.decode,List.getElem?_map,List.getElem?_range hi,Option.map_some,Option.getD_some]

theorem append_entry_last (n : ℕ) (q l r : List Bool) (side : Bool) (p : List Bool) :
    entry (appendPayload n q l r side p) (depth q)=levelEntry l r side :=by
  have HL : depth q=(WordListRecords.decode (metadata q)).length:=
    (WordListRecords.length_decode _).symm
  simp only [entry,appendPayload,completePayload_metadata,WordList.get_encode]
  rw [HL]
  simp

theorem chosen_eq_of_entry {q r : List Bool} {i : ℕ} (he : entry q i=entry r i) :chosen q i=chosen r i :=by
  unfold chosen sideWord left right
  rw [he]

theorem frozen_eq_of_entries {q r : List Bool} (k : ℕ)
    (he : ∀j<k,entry q j=entry r j) : frozen q k=frozen r k :=by
  unfold frozen
  apply congrArg WordList.encode
  apply List.map_congr_left
  intro j hj
  exact congrArg BinaryNatCode.encode (chosen_eq_of_entry (he j (List.mem_range.mp hj)))

theorem blockCount_eq_of_entry (n : ℕ) {q r : List Bool} {i : ℕ} (he : entry q i=entry r i) :
    blockCount n q i=blockCount n r i :=by
  unfold blockCount freshCount left right
  rw [he]

theorem rawStart_eq_of_entries (n : ℕ) {q r : List Bool} (k : ℕ)
    (he : ∀j<k,entry q j=entry r j) : rawStart n q k=rawStart n r k :=by
  unfold rawStart prefixCount
  apply congrArg (n+2+·)
  apply Finset.sum_congr rfl
  intro j hj
  exact blockCount_eq_of_entry n (he j (Finset.mem_range.mp hj))

theorem template_eq_of_entries {q r : List Bool} (i : ℕ)
    (he : ∀j≤ i,entry q j=entry r j) :template q i=template r i :=by
  have HF:=frozen_eq_of_entries i (fun j hj=>he j hj.le)
  unfold template withSlice
  rw [HF]
  simp only [left,right,side,sideWord,he i (Nat.le_refl i)]

theorem append_frozen_before (n : ℕ) (q l r : List Bool) (side : Bool) (p : List Bool)
    (i : ℕ) (hi : i≤depth q) : frozen (appendPayload n q l r side p) i=frozen q i :=
  frozen_eq_of_entries i (fun j hj=>append_entry_before n q l r side p j (hj.trans_le hi))

theorem append_rawStart_before (n : ℕ) (q l r : List Bool) (side : Bool) (p : List Bool)
    (i : ℕ) (hi : i≤depth q) : rawStart n (appendPayload n q l r side p) i=rawStart n q i :=
  rawStart_eq_of_entries n i (fun j hj=>append_entry_before n q l r side p j (hj.trans_le hi))

theorem append_template_before (n : ℕ) (q l r : List Bool) (side : Bool) (p : List Bool)
    (i : ℕ) (hi : i<depth q) :template (appendPayload n q l r side p) i=template q i :=
  template_eq_of_entries i (fun j hj=>append_entry_before n q l r side p j (hj.trans_lt hi))

theorem canonicalEntry_eq_of_entry {q r : List Bool} {i : ℕ} (he : entry q i=entry r i) :
    canonicalEntry q i=canonicalEntry r i :=by
  unfold canonicalEntry left right side sideWord
  rw [he]

theorem append_template_last (n : ℕ) (q l r : List Bool) (s : Bool) (p : List Bool) :
    template (appendPayload n q l r s p) (depth q)=
      IntegralMixedRoadmapLevel.packet (frozen q (depth q)) l r s [] :=by
  have HF:=append_frozen_before n q l r s p (depth q) (Nat.le_refl _)
  have HE:=append_entry_last n q l r s p
  unfold template withSlice
  rw [HF]
  cases s <;> simp [left,right,side,sideWord,HE,levelEntry,WordList.get_encode]

theorem append_last_canonical (n : ℕ) (q l r : List Bool) (s : Bool) (p : List Bool) :
    entry (appendPayload n q l r s p) (depth q)=canonicalEntry (appendPayload n q l r s p) (depth q) :=by
  have HE:=append_entry_last n q l r s p
  rw [HE]
  unfold canonicalEntry
  cases s <;> simp [left,right,side,sideWord,HE,levelEntry,WordList.get_encode]

private theorem good_payload_iff (n B sourceCap birth : ℕ) (w l r : List Bool) (s : Bool) (x y : List Bool) :
    IntegralMixedRoadmapLevel.Good n B sourceCap birth (IntegralMixedRoadmapLevel.packet w l r s x) ↔
      IntegralMixedRoadmapLevel.Good n B sourceCap birth (IntegralMixedRoadmapLevel.packet w l r s y) :=by
  cases s <;> simp [IntegralMixedRoadmapLevel.Good,IntegralMixedRoadmapLevel.labels,
    IntegralMixedRoadmapLevel.g,IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapLevel.left,
    IntegralMixedRoadmapLevel.right,IntegralMixedRoadmapLevel.freshLeft,IntegralMixedRoadmapLevel.sideWord,
    IntegralMixedRoadmapLevel.side,IntegralMixedRoadmapLevel.slice,IntegralMixedRoadmapLevel.packet]

theorem append_checked {n B sourceCap initial C : ℕ} {q : List Bool}
    (hq : Checked n B sourceCap initial C q) (l r : List Bool) (s : Bool) (p : List Bool)
    (hd : depth q<n)
    (hnew : IntegralMixedRoadmapLevel.Good n B sourceCap (birth n initial q (depth q))
      (IntegralMixedRoadmapLevel.packet (frozen q (depth q)) l r s []))
    (hp : p.length≤IntegralMixedRoadmapRecordChain.codeBound n initial C) :
    Checked n B sourceCap initial C (appendPayload n q l r s p) :=by
  apply completePayload_checked n B sourceCap initial C
    (WordListRecords.decode (metadata q)++[levelEntry l r s]) p ?_ hq.2.1 hq.2.2.1 ?_ ?_ hp
  · simp only [List.length_append,WordListRecords.length_decode,List.length_singleton]
    change depth q+1≤n
    omega
  · intro i hi
    change i<depth (appendPayload n q l r s p) at hi
    change entry (appendPayload n q l r s p) i=canonicalEntry (appendPayload n q l r s p) i
    rw [append_depth] at hi
    by_cases HI : i<depth q
    · have HE:=append_entry_before n q l r s p i HI
      exact HE.trans (((hq.2.2.2.2.1 i HI).1).trans (canonicalEntry_eq_of_entry HE).symm)
    · have HE : i=depth q:=by omega
      subst i
      exact append_last_canonical n q l r s p
  · intro i hi
    change i<depth (appendPayload n q l r s p) at hi
    change IntegralMixedRoadmapLevel.Good n B sourceCap (birth n initial (appendPayload n q l r s p) i)
      (template (appendPayload n q l r s p) i)
    rw [append_depth] at hi
    by_cases HI : i<depth q
    · have HB : birth n initial (appendPayload n q l r s p) i=birth n initial q i:=
        congrArg (initial+·) (append_rawStart_before n q l r s p i HI.le)
      rw [HB,append_template_before n q l r s p i HI]
      exact (good_payload_iff n B sourceCap (birth n initial q i) (frozen q i) (left q i) (right q i)
        (side q i) _ []).mp (level_checked hq i HI).1
    · have HE : i=depth q:=by omega
      subst i
      have HB : birth n initial (appendPayload n q l r s p) (depth q)=birth n initial q (depth q):=
        congrArg (initial+·) (append_rawStart_before n q l r s p (depth q) (Nat.le_refl _))
      rw [HB,append_template_last]
      exact hnew

def chainPrefixCodes (n : ℕ) (q : List Bool) (k : ℕ) :=seedCodes n++
  (List.range k).flatMap (fun j=>IntegralMixedRoadmapLevel.codes n (template q j))

theorem chainPrefixCodes_length (n : ℕ) (q : List Bool) (k : ℕ) :
    (chainPrefixCodes n q k).length=rawStart n q k :=by
  induction k with
  | zero=>simp only [chainPrefixCodes,List.range_zero,List.flatMap_nil,List.append_nil,seedCodes_length,
      rawStart,prefixCount,Finset.sum_range_zero,Nat.add_zero]
  | succ k ih=>
    simp only [chainPrefixCodes,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.length_append,template_codes_length,rawStart_succ] at *
    omega

theorem chainPrefixCodes_eq_of_entries (n : ℕ) {q r : List Bool} (k : ℕ)
    (he : ∀j<k,entry q j=entry r j) :chainPrefixCodes n q k=chainPrefixCodes n r k :=by
  unfold chainPrefixCodes
  apply congrArg (seedCodes n++·)
  apply List.flatMap_congr
  intro j hj
  apply congrArg (IntegralMixedRoadmapLevel.codes n)
  exact template_eq_of_entries j (fun i hi=>he i (hi.trans_lt (List.mem_range.mp hj)))

theorem compiled_prefix (n : ℕ) (q : List Bool) (k : ℕ) (hk : k≤depth q) :
    ∃rest,compiledCodes n q=chainPrefixCodes n q k++rest :=by
  have HR : List.range (depth q)=List.range k++(List.range (depth q-k)).map (fun j=>k+j):=by
    conv_lhs => rw [show depth q=k+(depth q-k) by omega]
    rw [List.range_add]
  refine ⟨((List.range (depth q-k)).map (fun j=>k+j)).flatMap
    (fun j=>IntegralMixedRoadmapLevel.codes n (template q j))++
      List.replicate (paddingCount n q) (seedCode n)++[probe q],?_⟩
  unfold compiledCodes meaningfulCodes chainPrefixCodes
  rw [HR]
  simp only [List.flatMap_append,List.append_assoc]

theorem compiled_prefix_lookup (n : ℕ) (q : List Bool) (k : ℕ) (hk : k≤depth q)
    (i : ℕ) (hi : i<rawStart n q k) :
    WordList.get (compiled n q) i=WordList.get (WordList.encode (chainPrefixCodes n q k)) i :=by
  obtain ⟨rest,HE⟩:=compiled_prefix n q k hk
  have HL : i<(chainPrefixCodes n q k).length:=by rw [chainPrefixCodes_length];exact hi
  rw [compiled,HE,WordList.get_encode,List.getElem?_append_left HL,WordList.get_encode]

theorem append_raw_before {n B sourceCap initial C : ℕ} {q : List Bool}
    (hq : Checked n B sourceCap initial C q) (l r : List Bool) (s : Bool) (p : List Bool)
    (i : ℕ) (hi : i<rawStart n q (depth q)) :
    WordList.get (raw (appendPayload n q l r s p)) i=WordList.get (raw q) i :=by
  have HR : raw (appendPayload n q l r s p)=compiled n (appendPayload n q l r s p):=
    completePayload_raw n _ p
  have HK : depth q≤depth (appendPayload n q l r s p):=by rw [append_depth];omega
  have HI : i<rawStart n (appendPayload n q l r s p) (depth q):=by
    rw [append_rawStart_before n q l r s p (depth q) (Nat.le_refl _)]
    exact hi
  rw [HR,hq.2.2.2.2.2.1,compiled_prefix_lookup n _ (depth q) HK i HI,
    compiled_prefix_lookup n q (depth q) (Nat.le_refl _) i hi]
  rw [chainPrefixCodes_eq_of_entries n (depth q)
    (fun j hj=>append_entry_before n q l r s p j hj)]

end LeanCanny.Encoding.IntegralMixedRoadmapChain
