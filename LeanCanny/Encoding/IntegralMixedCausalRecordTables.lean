/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCausalRecordPlan
/-! # Original-only native mode, header and affine-body tables -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCausalRecordPlanBits
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralCriticalHistoryTask IntegralMixedFramedHistoryFamilyBits
open IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def mode (n : ℕ) (code : List Bool) :=
  pair [if IntegralMixedUnitRecordCode.critical code then false else IntegralMixedCausalUnitRecordBits.current code]
    (BinaryNatCode.encode (if IntegralMixedUnitRecordCode.critical code then 0 else IntegralMixedUnitRecordCode.height n code))

theorem mode_FP {n : List Bool→ℕ} (hn : UnaryFn n) {code : List Bool→List Bool} (hc : code∈FP) :
    (fun q => mode (n q) (code q))∈FP := by
  have HF (i : ℕ) := mem_FP_comp (f:=code) (g:=fun w => WordList.get w i) hc (IntegralMixedCommandHeaderBits.get_FP i)
  have HB := FPPred.getBit (HF 0) (UnaryFn.const 0)
  have HM := (FPPred.getBit (HF 10) (UnaryFn.const 0)).flag_mem_FP
  have HH := (BinaryFn.fromBits (HF 5)).mod
    (((BinaryFn.fromBits (HF 2)).mod (BinaryFn.ofUnary hn)).add (BinaryFn.const 1))
  apply mem_FP_of_eq (HB.ite_mem_FP (constFn_mem_FP (pair [false] (BinaryNatCode.encode 0)))
    (mem_FP_pair HM HH.bits_mem_FP))
  intro q
  simp only [mode,IntegralMixedCausalUnitRecordBits.current,Function.comp_apply,Bool.decide_eq_true,IntegralMixedUnitRecordCode.critical,IntegralMixedUnitRecordCode.field]
  split_ifs <;> rfl

noncomputable def headerEntry (P : Parameters) (z : List Bool) :=
  pair (IntegralMixedCommandHeaderBits.encode (IntegralMixedCausalUnitHeaderBits.header
    (P.ambient (pairFst z)) (P.degree (pairFst z)) (reader z))) []
noncomputable def modeEntry (P : Parameters) (z : List Bool) :=
  pair (mode (P.ambient (pairFst z)) (reader z)) []
noncomputable def bodyEntry (P : Parameters) (z : List Bool) :=
  pair (IntegralMixedCausalUnitBodyBits.body (P.ambient (pairFst z)) (pairSnd z).length (reader z)) []

noncomputable def headerTable (P : Parameters) (root : List Bool) := WordList.encode
  ((List.range (count root)).map fun b => IntegralMixedCommandHeaderBits.encode
    (IntegralMixedCausalUnitHeaderBits.header (P.ambient root) (P.degree root) (code root b)))
noncomputable def modeTable (P : Parameters) (root : List Bool) := WordList.encode
  ((List.range (count root)).map fun b => mode (P.ambient root) (code root b))
noncomputable def bodyTable (P : Parameters) (root : List Bool) := WordList.encode
  ((List.range (count root)).map fun b => IntegralMixedCausalUnitBodyBits.body (P.ambient root) b (code root b))

attribute [local irreducible] IntegralMixedCausalUnitHeaderBits.header IntegralMixedCausalUnitBodyBits.body mode reader

theorem headerTable_FP (P : Parameters) (a : Access P) : headerTable P∈FP := by
  have HE : headerEntry P∈FP := mem_FP_pair
    (IntegralMixedCausalUnitHeaderBits.header_FP (a.ambient.comp pairFst_mem_FP) (a.degree.comp pairFst_mem_FP) reader_FP) (constFn_mem_FP [])
  apply mem_FP_of_eq (flatMap_range_mem_FP HE (count_unary.replicate_mem_FP true))
  intro root
  simp only [headerTable,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,headerEntry,reader,
    pairFst_pair,pairSnd_pair,List.length_replicate]

theorem modeTable_FP (P : Parameters) (a : Access P) : modeTable P∈FP := by
  have HE : modeEntry P∈FP := mem_FP_pair (mode_FP (a.ambient.comp pairFst_mem_FP) reader_FP) (constFn_mem_FP [])
  apply mem_FP_of_eq (flatMap_range_mem_FP HE (count_unary.replicate_mem_FP true))
  intro root
  simp only [modeTable,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,modeEntry,reader,
    pairFst_pair,pairSnd_pair,List.length_replicate]

theorem bodyTable_FP (P : Parameters) (a : Access P) : bodyTable P∈FP := by
  have HP := mem_FP_pair reader_FP (mem_FP_pair pairSnd_mem_FP ((a.ambient.comp pairFst_mem_FP).replicate_mem_FP true))
  have HB : (fun z => IntegralMixedCausalUnitBodyBits.body (P.ambient (pairFst z)) (pairSnd z).length (reader z))∈FP :=
    mem_FP_of_eq (mem_FP_comp HP IntegralMixedCausalUnitBodyBits.writer_FP) (fun z => by
      simp only [Function.comp_apply,IntegralMixedCausalUnitBodyBits.writer,pairFst_pair,pairSnd_pair,List.length_replicate])
  have HE : bodyEntry P∈FP := mem_FP_pair HB (constFn_mem_FP [])
  apply mem_FP_of_eq (flatMap_range_mem_FP HE (count_unary.replicate_mem_FP true))
  intro root
  simp only [bodyTable,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,bodyEntry,reader,
    pairFst_pair,pairSnd_pair,List.length_replicate]

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀ root,0<P.ambient root) (hd : ∀ root b,(S root b).degree=P.degree root)
  (hcap : ∀ root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)

theorem headerWords_eq (root : List Bool) :
    IntegralMixedCausalPlanBits.headerWords P (originalRecords P S hn hd hcap) root=headerTable P root := by
  unfold IntegralMixedCausalPlanBits.headerWords originalRecords
  rw [List.reverse_reverse,List.map_map]
  congr 1
  apply List.map_congr_left
  intro b _
  simp only [Function.comp_apply]
  unfold step
  rw [IntegralMixedCausalUnitHeaderBits.record_header,hd]

theorem modeWords_eq (root : List Bool) :
    IntegralMixedCausalPlanBits.modeWords P (originalRecords P S hn hd hcap) root=modeTable P root := by
  unfold IntegralMixedCausalPlanBits.modeWords originalRecords
  rw [List.reverse_reverse,List.map_map]
  congr 1
  apply List.map_congr_left
  intro b _
  simp only [Function.comp_apply]
  unfold step IntegralMixedCausalUnitRecordBits.record
  cases hh : IntegralMixedUnitRecordCode.critical (code root b) <;>
    simp only [hh,Bool.false_eq_true,ite_false,ite_true,IntegralMixedCausalPlanBits.templateCurrent,
      IntegralMixedCausalPlanBits.templateHeight,mode,IntegralMixedCausalUnitRecordBits.cut]
  rfl

theorem metadata (a : Access P) : IntegralMixedCausalPlanBits.Metadata P (originalRecords P S hn hd hcap) :=
  IntegralMixedCausalPlanBits.metadata P a _ (mem_FP_of_eq (modeTable_FP P a) (fun root => (modeWords_eq P S hn hd hcap root).symm))

theorem tables_native (a : Access P) : IntegralMixedHeaderTablesBits.Access
    (IntegralMixedCausalPlanBits.tables P (originalRecords P S hn hd hcap)) :=
  IntegralMixedCausalPlanBits.tables_native P a _ (mem_FP_of_eq (headerTable_FP P a) (fun root => (headerWords_eq P S hn hd hcap root).symm))

end LeanCanny.Encoding.IntegralMixedCausalRecordPlanBits
