/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapChainAppend
/-! # An ancestor's literal chain keeps the original fixed record horizon

Only metadata after the selected depth is discarded. The compiled earlier
program and its producer labels are preserved; unused births are seed padding.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapChain
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def prefixPayload (n : ℕ) (q : List Bool) (k : ℕ) (p : List Bool):=
  completePayload n (WordList.encode ((WordListRecords.decode (metadata q)).take k)) p

theorem prefix_depth (n : ℕ) (q : List Bool) (k : ℕ) (p : List Bool) (hk : k≤depth q) :
    depth (prefixPayload n q k p)=k :=by
  simp only [depth,prefixPayload,completePayload_metadata,WordListRecords.count_encode,
    List.length_take,WordListRecords.length_decode]
  exact min_eq_left hk

theorem prefix_entry (n : ℕ) (q : List Bool) (k : ℕ) (p : List Bool) (i : ℕ) (hi : i<k) (hk : k≤depth q) :
    entry (prefixPayload n q k p) i=entry q i :=by
  have HI : i<WordListRecords.count (metadata q):=hi.trans_le hk
  simp only [entry,prefixPayload,completePayload_metadata,WordList.get_encode]
  rw [List.getElem?_take]
  simp only [hi,ite_true]
  simp only [WordListRecords.decode,List.getElem?_map,List.getElem?_range HI,Option.map_some,Option.getD_some]

theorem prefix_frozen (n : ℕ) (q : List Bool) (k : ℕ) (p : List Bool) (hk : k≤depth q) :
    frozen (prefixPayload n q k p) k=frozen q k :=
  frozen_eq_of_entries k (fun i hi=>prefix_entry n q k p i hi hk)

theorem prefix_rawStart (n : ℕ) (q : List Bool) (k : ℕ) (p : List Bool) (hk : k≤depth q) :
    rawStart n (prefixPayload n q k p) k=rawStart n q k :=
  rawStart_eq_of_entries n k (fun i hi=>prefix_entry n q k p i hi hk)

private theorem template_good {n B sourceCap initial C : ℕ} {q : List Bool}
    (hq : Checked n B sourceCap initial C q) (i : ℕ) (hi : i<depth q) :
    IntegralMixedRoadmapLevel.Good n B sourceCap (birth n initial q i) (template q i) :=by
  have H:=(level_checked hq i hi).1
  cases HS :side q i <;> simpa [IntegralMixedRoadmapLevel.Good,IntegralMixedRoadmapLevel.labels,
    IntegralMixedRoadmapLevel.g,IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapLevel.left,
    IntegralMixedRoadmapLevel.right,IntegralMixedRoadmapLevel.freshLeft,IntegralMixedRoadmapLevel.sideWord,
    IntegralMixedRoadmapLevel.side,IntegralMixedRoadmapLevel.slice,IntegralMixedRoadmapLevel.packet,
    levelPacket,template,withSlice,HS] using H

theorem prefix_checked {n B sourceCap initial C : ℕ} {q : List Bool}
    (hq : Checked n B sourceCap initial C q) (k : ℕ) (hk : k≤depth q) (p : List Bool)
    (hp : p.length≤IntegralMixedRoadmapRecordChain.codeBound n initial C) :
    Checked n B sourceCap initial C (prefixPayload n q k p) :=by
  apply completePayload_checked n B sourceCap initial C ((WordListRecords.decode (metadata q)).take k) p
    ?_ hq.2.1 hq.2.2.1 ?_ ?_ hp
  · rw [List.length_take,WordListRecords.length_decode]
    change min k (depth q)≤n
    rw [min_eq_left hk]
    exact hk.trans hq.1
  · intro i hi
    change i<depth (prefixPayload n q k p) at hi
    rw [prefix_depth n q k p hk] at hi
    have HE:=prefix_entry n q k p i hi hk
    exact HE.trans (((hq.2.2.2.2.1 i (hi.trans_le hk)).1).trans (canonicalEntry_eq_of_entry HE).symm)
  · intro i hi
    change i<depth (prefixPayload n q k p) at hi
    rw [prefix_depth n q k p hk] at hi
    change IntegralMixedRoadmapLevel.Good n B sourceCap (birth n initial (prefixPayload n q k p) i)
      (template (prefixPayload n q k p) i)
    have HT:=template_eq_of_entries i (fun j hj=>prefix_entry n q k p j (hj.trans_lt hi) hk)
    have HB :birth n initial (prefixPayload n q k p) i=birth n initial q i:=
      congrArg (initial+·) (rawStart_eq_of_entries n i (fun j hj=>prefix_entry n q k p j (hj.trans hi) hk))
    rw [HB,HT]
    exact template_good hq i (hi.trans_le hk)

theorem prefix_raw_before {n B sourceCap initial C : ℕ} {q : List Bool}
    (hq : Checked n B sourceCap initial C q) (k : ℕ) (hk : k≤depth q) (p : List Bool)
    (i : ℕ) (hi : i<rawStart n q k) :
    WordList.get (raw (prefixPayload n q k p)) i=WordList.get (raw q) i :=by
  have HR :raw (prefixPayload n q k p)=compiled n (prefixPayload n q k p):=completePayload_raw n _ p
  have HK :k≤depth (prefixPayload n q k p):=by rw [prefix_depth n q k p hk]
  have HI :i<rawStart n (prefixPayload n q k p) k:=by rw [prefix_rawStart n q k p hk];exact hi
  rw [HR,hq.2.2.2.2.2.1,compiled_prefix_lookup n _ k HK i HI,compiled_prefix_lookup n q k hk i hi]
  rw [chainPrefixCodes_eq_of_entries n k (fun j hj=>prefix_entry n q k p j hj hk)]

end LeanCanny.Encoding.IntegralMixedRoadmapChain
