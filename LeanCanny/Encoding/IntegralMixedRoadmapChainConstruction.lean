/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapChainLedger
/-! # Literal compiled chains contain every local level at its declared offset

This direction supports completeness: constructing valid local programs must
produce a checked whole table, as well as interpreting already checked input.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapChain
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedRoadmapRecordChain
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem range_split (d i : ℕ) (hi : i<d) :
    List.range d=List.range i++[i]++(List.range (d-(i+1))).map (fun j=>i+1+j) :=by
  conv_lhs => rw [show d=(i+1)+(d-(i+1)) by omega]
  rw [List.range_add,List.range_succ]

private theorem prefix_length (n : ℕ) (q : List Bool) (i : ℕ) :
    (seedCodes n++(List.range i).flatMap (fun j=>IntegralMixedRoadmapLevel.codes n (template q j))).length=
      rawStart n q i :=by
  induction i with
  | zero=>simp only [List.range_zero,List.flatMap_nil,List.append_nil,seedCodes_length,rawStart,prefixCount,Finset.sum_range_zero,Nat.add_zero]
  | succ i ih=>
    simp only [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.length_append,template_codes_length,rawStart_succ] at *
    omega

theorem compiledCodes_split (n : ℕ) (q : List Bool) (i : ℕ) (hi : i<depth q) :
    ∃before after,compiledCodes n q=before++IntegralMixedRoadmapLevel.codes n (template q i)++after ∧
      before.length=rawStart n q i :=by
  refine ⟨seedCodes n++(List.range i).flatMap (fun j=>IntegralMixedRoadmapLevel.codes n (template q j)),
    ((List.range (depth q-(i+1))).map (fun j=>i+1+j)).flatMap
      (fun j=>IntegralMixedRoadmapLevel.codes n (template q j))++
        List.replicate (paddingCount n q) (seedCode n)++[probe q],?_,prefix_length n q i⟩
  unfold compiledCodes meaningfulCodes
  rw [range_split (depth q) i hi]
  simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

private theorem rawSlice_middle (before middle after : List (List Bool)) :
    IntegralMixedRoadmapLevel.rawSlice (WordList.encode (before++middle++after)) before.length middle.length=
      WordList.encode middle :=by
  simp only [List.append_assoc]
  unfold IntegralMixedRoadmapLevel.rawSlice
  apply congrArg WordList.encode
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,WordList.get_encode]
    rw [List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem?_append_left hj]
    simp only [List.getElem?_eq_getElem hj,Option.getD_some]

theorem compiled_level_slice (n : ℕ) (q : List Bool) (i : ℕ) (hi : i<depth q) :
    IntegralMixedRoadmapLevel.rawSlice (compiled n q) (rawStart n q i) (blockCount n q i)=
      IntegralMixedRoadmapLevel.compiled n (template q i) :=by
  obtain ⟨before,after,HE,HL⟩:=compiledCodes_split n q i hi
  rw [←HL,←template_codes_length n q i]
  unfold compiled IntegralMixedRoadmapLevel.compiled
  rw [HE,rawSlice_middle]

theorem compiled_level_fits (n : ℕ) (q : List Bool) (i : ℕ) (hi : i<depth q) :
    rawStart n q i+blockCount n q i≤WordListRecords.count (compiled n q) :=by
  obtain ⟨before,after,HE,HL⟩:=compiledCodes_split n q i hi
  rw [compiled,WordListRecords.count_encode,HE,List.length_append,List.length_append,
    template_codes_length,HL]
  omega

theorem checked_of_compiled (n B sourceCap initial C : ℕ) (q : List Bool)
    (hd : depth q≤n) (hBC : B≤C) (hcap : sourceCap≤2^B)
    (hmeta : metadata q=IntegralMixedRoadmapLevel.rawSlice (metadata q) 0 (depth q))
    (hentry : ∀i<depth q,entry q i=canonicalEntry q i)
    (hgood : ∀i<depth q,IntegralMixedRoadmapLevel.Good n B sourceCap (birth n initial q i) (template q i))
    (hraw : raw q=compiled n q) (hprobe : (probe q).length≤codeBound n initial C)
    (hpacket : q=packet (metadata q) (raw q) (probe q)) : Checked n B sourceCap initial C q :=by
  refine ⟨hd,hBC,hcap,hmeta,?_,hraw,?_,hprobe,hpacket⟩
  · intro i hi
    have HS : levelPacket n q i=withSlice q i (IntegralMixedRoadmapLevel.compiled n (template q i)):=by
      unfold levelPacket
      rw [hraw,compiled_level_slice n q i hi]
    refine ⟨hentry i hi,?_,?_⟩
    · rw [HS]
      exact IntegralMixedRoadmapLevel.checked_packet n B sourceCap (birth n initial q i)
        (frozen q i) (left q i) (right q i) (side q i) (hgood i hi)
    · apply (level_inRaw_iff n q i).mpr
      rw [hraw]
      exact compiled_level_fits n q i hi
  · rw [hraw,compiled,WordListRecords.count_encode,compiledCodes_length n q hd]

/-- Canonical raw-table completion changes no metadata or probe bytes. -/
def completePayload (n : ℕ) (m p : List Bool) :=packet m (compiled n (packet m [] p)) p

theorem completePayload_metadata (n : ℕ) (m p : List Bool) : metadata (completePayload n m p)=m :=by
  simp only [completePayload,metadata,packet,pairFst_pair]
theorem completePayload_probe (n : ℕ) (m p : List Bool) : probe (completePayload n m p)=p :=by
  simp only [completePayload,probe,packet,pairSnd_pair]
theorem completePayload_raw (n : ℕ) (m p : List Bool) :
    raw (completePayload n m p)=compiled n (completePayload n m p) :=by
  simp only [completePayload,raw,packet,pairFst_pair,pairSnd_pair]
  exact (compiled_packet n m p _ []).symm

theorem completePayload_checked (n B sourceCap initial C : ℕ) (entries : List (List Bool)) (p : List Bool)
    (hd : entries.length≤n) (hBC : B≤C) (hcap : sourceCap≤2^B)
    (hentry : ∀i<depth (completePayload n (WordList.encode entries) p),
      entry (completePayload n (WordList.encode entries) p) i=
        canonicalEntry (completePayload n (WordList.encode entries) p) i)
    (hgood : ∀i<depth (completePayload n (WordList.encode entries) p),
      IntegralMixedRoadmapLevel.Good n B sourceCap (birth n initial (completePayload n (WordList.encode entries) p) i)
        (template (completePayload n (WordList.encode entries) p) i))
    (hp : p.length≤codeBound n initial C) :
    Checked n B sourceCap initial C (completePayload n (WordList.encode entries) p) :=by
  apply checked_of_compiled n B sourceCap initial C _ ?_ hBC hcap ?_ hentry hgood
    (completePayload_raw n _ p) ?_ ?_
  · simpa only [depth,completePayload_metadata,WordListRecords.count_encode] using hd
  · simp only [completePayload_metadata,depth,WordListRecords.count_encode]
    exact (rawSlice_all entries).symm
  · simpa only [completePayload_probe] using hp
  · simp only [completePayload,metadata,raw,probe,packet,pairFst_pair,pairSnd_pair]

theorem complete_seed_checked (n B sourceCap initial C : ℕ) (hBC : B≤C) (hcap : sourceCap≤2^B) :
    Checked n B sourceCap initial C (completePayload n [] (seedCode n)) :=by
  apply completePayload_checked n B sourceCap initial C [] (seedCode n) (by simp) hBC hcap
  · intro i hi
    simp only [depth,completePayload_metadata,WordListRecords.count_encode,List.length_nil] at hi
    omega
  · intro i hi
    simp only [depth,completePayload_metadata,WordListRecords.count_encode,List.length_nil] at hi
    omega
  · have H:=(seed n initial C ⟨0,by omega⟩).property
    simpa only [seed,dite_true] using H

end LeanCanny.Encoding.IntegralMixedRoadmapChain
