/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalPlanMetadata
public import LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitHeaderGeneric
/-! # Original causal header tables represent the actual interpreted plan

The command writer encodes only original record headers. Total fallback
headers are literal zero/unit selections at every prefix/context address.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCausalPlanBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedCausalRecordBits
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def headerWords (P : Parameters) (R : ∀ root,List (Record (P.ambient root) (P.width root))) (root : List Bool) :=
  WordList.encode ((R root).reverse.map fun r => IntegralMixedCommandHeaderBits.encode r.template.header)

def fallbackHeader : IntegralMixedCommandHeaderBits.Header := ⟨2,0,1,0,0,0,2⟩
def fallbackWords (P : Parameters) (root : List Bool) := WordList.encode
  ((List.range (5*(P.cap root+2))).map fun _ => IntegralMixedCommandHeaderBits.encode fallbackHeader)

theorem fallbackWords_FP (P : Parameters) (a : Access P) : fallbackWords P∈FP := by
  have HE : (fun _ : List Bool => pair (IntegralMixedCommandHeaderBits.encode fallbackHeader) [])∈FP := constFn_mem_FP _
  have HN := ((UnaryFn.const 5).mul (a.cap.add (UnaryFn.const 2))).replicate_mem_FP true
  apply mem_FP_of_eq (flatMap_range_mem_FP HE HN)
  intro root
  simp only [fallbackWords,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,List.length_replicate]

theorem fallbackWords_get (P : Parameters) (key : List Bool) :
    WordList.get (fallbackWords P (pairFst key)) (IntegralMixedHeaderTablesBits.fallbackIndex P key)=
      IntegralMixedCommandHeaderBits.encode fallbackHeader := by
  rw [fallbackWords,WordList.get_encode]
  simp only [List.getElem?_map,List.getElem?_range (IntegralMixedHeaderTablesBits.fallbackIndex_lt P key),Option.map_some,Option.getD_some]

noncomputable def tables (P : Parameters) (R : ∀ root,List (Record (P.ambient root) (P.width root))) : IntegralMixedHeaderTablesBits.Tables where
  commands := headerWords P R
  fallback := fallbackWords P

theorem tables_native (P : Parameters) (a : Access P)
    (R : ∀ root,List (Record (P.ambient root) (P.width root))) (h : headerWords P R∈FP) :
    IntegralMixedHeaderTablesBits.Access (tables P R) := ⟨h,fallbackWords_FP P a⟩

theorem tables_represent (P : Parameters) (base : Plan P)
    (R : ∀ root,List (Record (P.ambient root) (P.width root)))
    (hroom : ∀ root,(R root).length+2≤P.cap root+1) (hn : ∀ root,0<P.ambient root)
    (hd : ∀ root,∀ r∈R root,r.source.degree=P.degree root) (hW : ∀ root,(P.degree root).size≤P.sourceWidth root) :
    IntegralMixedFramedHeaderBits.Represents P (plan P base R hroom) (data P base R hroom hn hd hW) (tables P R) where
  commands root := (plan_words P base R hroom root).symm
  fallback key := fallbackWords_get P key
end LeanCanny.Algebra.IntegralMixedCausalPlanBits
