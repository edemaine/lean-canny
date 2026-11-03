/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSourceIntegerSnapshot
public import LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitHeaderGeneric
/-! # Native literal headers for charged-source integer preludes -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def commandHeaders (count : List Bool → ℕ) (root : List Bool) :=
  WordList.encode ((List.range (count root)).map fun _=>IntegralMixedCommandHeaderBits.encode IntegralMixedCommandHeaderBits.zero)

theorem commandHeaders_FP {count : List Bool → ℕ} (hc : UnaryFn count) : commandHeaders count∈FP := by
  have H:=flatMap_range_mem_FP
    (constFn_mem_FP (pair (IntegralMixedCommandHeaderBits.encode IntegralMixedCommandHeaderBits.zero) []))
    (hc.replicate_mem_FP true)
  apply mem_FP_of_eq H
  intro root
  simp only [commandHeaders,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    List.length_replicate]

noncomputable def tables (P : Parameters) (count : List Bool → ℕ) : IntegralMixedHeaderTablesBits.Tables :=
  ⟨commandHeaders count,FlatAffineExceptionalCanonicalUnitHeaders.fallbackOfWords P (fun _=>[])⟩

theorem tables_native (P : Parameters) (a : Access P) {count : List Bool → ℕ} (hc : UnaryFn count) :
    IntegralMixedHeaderTablesBits.Access (tables P count) := by
  constructor
  · exact commandHeaders_FP hc
  · exact FlatAffineExceptionalCanonicalUnitHeaders.fallbackOfWords_FP P a (fun _ : List Bool=>[]) (constFn_mem_FP ([] : List Bool))

variable (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
  (hdegree : ∀root,(Q root).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
  (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,count root+2≤P.cap root+1)
  (hn : ∀root,0<P.ambient root) (hSW : ∀root,(P.degree root).size≤P.sourceWidth root)

theorem tables_represents : IntegralMixedFramedHeaderBits.Represents P
    (plan P Q hdegree hcap S count hz hd hroom) (data P Q hdegree hcap S count hz hd hroom hn hSW) (tables P count) where
  commands root := by
    unfold IntegralMixedFramedHeaderBits.words
    have HM : ((plan P Q hdegree hcap S count hz hd hroom).rules root).reverse.map
        (fun c=>IntegralMixedCommandHeaderBits.encode (IntegralMixedCommandHeaderBits.command c.command))=
      ((plan P Q hdegree hcap S count hz hd hroom).rules root).reverse.map
        (fun _=>IntegralMixedCommandHeaderBits.encode IntegralMixedCommandHeaderBits.zero) := by
      apply List.map_congr_left
      intro c hc
      have HC := List.mem_reverse.mp hc
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp HC
      rfl
    rw [HM]
    simp only [tables,commandHeaders,List.map_const',List.length_reverse,plan,commands_length,List.length_range]
  fallback key := by
    change WordList.get (FlatAffineExceptionalCanonicalUnitHeaders.fallbackOfWords P (fun _=>[]) (pairFst key))
      (IntegralMixedHeaderTablesBits.fallbackIndex P key)=_
    rw [FlatAffineExceptionalCanonicalUnitHeaders.fallbackOfWords_get P (fun _=>[]) _ _ (IntegralMixedHeaderTablesBits.fallbackIndex_lt P key)]
    change IntegralMixedCommandHeaderBits.encode (IntegralMixedCanonicalUnitHeaderBits.selection (P.ambient (pairFst key)) (P.degree (pairFst key)) [])=
      IntegralMixedCommandHeaderBits.encode (IntegralMixedCommandHeaderBits.selection
        (IntegralMixedCanonicalUnitRuleBits.selection
          (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P Q hdegree hcap S count hz hd hroom) key).source
          (hn (pairFst key)) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) []))
    rw [IntegralMixedCanonicalUnitHeaderBits.selection_eq,instruction_source,hdegree]

end LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
