/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedEmptyUnitData
public import LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitHeaderGeneric
/-! # Native exact header tables with no initial integer bank -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedEmptyUnitPlan
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (keyAt prefixLength)
open IntegralMixedCanonicalUnitSourceBits (Originals source)
open scoped Classical

noncomputable def tables (P : Parameters) : IntegralMixedHeaderTablesBits.Tables :=
  ⟨FlatAffineExceptionalCanonicalUnitHeaders.laterTable P,
    FlatAffineExceptionalCanonicalUnitHeaders.fallbackOfWords P (selectedCode P)⟩

theorem native (P : Parameters) (a : Access P) : IntegralMixedHeaderTablesBits.Access (tables P) :=
  ⟨FlatAffineExceptionalCanonicalUnitHeaders.laterTable_FP P a,
    FlatAffineExceptionalCanonicalUnitHeaders.fallbackOfWords_FP P a (selectedCode P) (selectedCode_FP P a)⟩

variable (P : Parameters) (O : Originals P)
  (hn : ∀ root, 0<P.ambient root)
  (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (hroom : ∀ root, count root+2≤P.cap root+1)
  (hSW : ∀ root, (P.degree root).size≤P.sourceWidth root)

theorem commands_represents (root : List Bool) :
    (tables P).commands root=IntegralMixedFramedHeaderBits.words ((plan P O hn hcap hroom).rules root) := by
  change WordList.encode ((List.range (count root)).map fun i => IntegralMixedCommandHeaderBits.encode
    (IntegralMixedCanonicalUnitHeaderBits.command (P.ambient root) (P.degree root) (code root i)))=_
  have HS (i : ℕ) : IntegralMixedCommandHeaderBits.command (step P O hn hcap root i).command=
      IntegralMixedCanonicalUnitHeaderBits.command (P.ambient root) (P.degree root) (code root i) := by
    simpa only [step,IntegralMixedCanonicalUnitSourceBits.source_degree] using
      IntegralMixedCanonicalUnitHeaderBits.command_eq (source P O root i) (hn root) i (code root i) (hcap root)
  change _=IntegralMixedFramedHeaderBits.words (rules P O hn hcap root)
  simp only [IntegralMixedFramedHeaderBits.words,rules,List.reverse_reverse,List.map_map,Function.comp_def,HS]

private theorem selectedCode_congr (P : Parameters) (x y : List Bool)
    (hr : pairFst x=pairFst y) (hb : prefixLength P x=prefixLength P y) : selectedCode P x=selectedCode P y := by
  unfold selectedCode inRecords
  rw [hr,hb]

theorem fallback_readback (key : List Bool) :
    WordList.get ((tables P).fallback (pairFst key)) (IntegralMixedHeaderTablesBits.fallbackIndex P key)=
      IntegralMixedCommandHeaderBits.encode (IntegralMixedCommandHeaderBits.selection
        ((data P O hn hcap hroom hSW).fallback key)) := by
  let i := IntegralMixedHeaderTablesBits.fallbackIndex P key
  have HI : i<5*(P.cap (pairFst key)+2) := IntegralMixedHeaderTablesBits.fallbackIndex_lt P key
  have HD : i/5=prefixLength P key := by
    have HC : min (Nat.fromBitsLE (pairSnd (pairSnd key))) 4≤4 := min_le_right _ _
    change (5*IntegralMixedFullHistoryFamilyBits.prefixLength P key+min (Nat.fromBitsLE (pairSnd (pairSnd key))) 4)/5=
      IntegralMixedFullHistoryFamilyBits.prefixLength P key
    omega
  have HR : pairFst (FlatAffineExceptionalCanonicalUnitHeaders.fallbackKey (pairFst key) i)=pairFst key :=
    IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _
  have HB : prefixLength P (FlatAffineExceptionalCanonicalUnitHeaders.fallbackKey (pairFst key) i)=prefixLength P key := by
    unfold FlatAffineExceptionalCanonicalUnitHeaders.fallbackKey
    rw [HD]
    exact IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P _ _ _ (min_le_right _ _)
  have HE := selectedCode_congr P _ _ HR HB
  change WordList.get (FlatAffineExceptionalCanonicalUnitHeaders.fallbackOfWords P (selectedCode P) (pairFst key)) i=_
  rw [FlatAffineExceptionalCanonicalUnitHeaders.fallbackOfWords_get P (selectedCode P) _ i HI,HE]
  change _=IntegralMixedCommandHeaderBits.encode (IntegralMixedCommandHeaderBits.selection
    (IntegralMixedCanonicalUnitRuleBits.selection
      (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O hn hcap hroom) key).source
      (hn (pairFst key)) (prefixLength P key) (selectedCode P key)))
  rw [IntegralMixedCanonicalUnitHeaderBits.selection_eq,(data P O hn hcap hroom hSW).degree_eq key]

theorem represents : IntegralMixedFramedHeaderBits.Represents P (plan P O hn hcap hroom)
    (data P O hn hcap hroom hSW) (tables P) :=
  ⟨commands_represents P O hn hcap hroom,fallback_readback P O hn hcap hroom hSW⟩

end LeanCanny.Encoding.IntegralMixedEmptyUnitPlan
