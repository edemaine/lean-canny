/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitHeaders
/-! # Exact provenance of the derived total canonical header tables -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitHeaders
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (keyAt prefixLength)
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open IntegralMixedCanonicalUnitSourceBits (Originals)
open FlatAffineExceptionalCanonicalUnitPlan
open scoped Classical

variable (P : Parameters) (O : Originals P) (F : Inputs)
  (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
  (hn : ∀ root, 0<P.ambient root)
  (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root) ≤ 2^P.width root)
  (hW : ∀ root, FlatAffineExceptionalBankSource.width F (input root) ≤ P.width root)
  (hroom : ∀ root, count root+seedCount F root+2 ≤ P.cap root+1)
  (hSW : ∀ root, (P.degree root).size ≤ P.sourceWidth root)

private theorem prelude_headers (root : List Bool) :
    ((prelude P O F C h hcap hW root).reverse.map fun c => IntegralMixedCommandHeaderBits.encode
      (IntegralMixedCommandHeaderBits.command c.command)) =
        List.replicate (seedCount F root) (IntegralMixedCommandHeaderBits.encode IntegralMixedCommandHeaderBits.zero) := by
  simp only [prelude,seedCount,FlatAffineExceptionalFramedIntegerPrelude.commands,List.map_reverse,List.map_ofFn,
    Function.comp_def,FlatAffineExceptionalFramedIntegerPrelude.command,FlatAffineExceptionalIntegerCommands.command,
    IntegralMixedCommandHeaderBits.command,List.ofFn_const,List.reverse_replicate]

theorem commands_represents (root : List Bool) :
    commands P F root = IntegralMixedFramedHeaderBits.words ((plan P O F C h hn hcap hW hroom).rules root) := by
  unfold commands laterTable
  rw [FlatAffineExceptionalIntegerHeaders.prepend_encode]
  unfold IntegralMixedFramedHeaderBits.words
  rw [rules_eq,List.reverse_append,List.map_append,prelude_headers P O F C h hcap hW]
  have HS (i : ℕ) : IntegralMixedCommandHeaderBits.command
      (FlatAffineExceptionalCanonicalUnitPlan.step P O F hn hcap root i).command =
        IntegralMixedCanonicalUnitHeaderBits.command (P.ambient root) (P.degree root) (code root i) := by
    simpa only [FlatAffineExceptionalCanonicalUnitPlan.step,IntegralMixedCanonicalUnitSourceBits.source_degree] using
      IntegralMixedCanonicalUnitHeaderBits.command_eq
        (IntegralMixedCanonicalUnitSourceBits.source P O root (seedCount F root+i))
        (hn root) (seedCount F root+i) (code root i) (hcap root)
  simp only [later,List.reverse_reverse,List.map_map,Function.comp_def,HS]

private theorem selectedCode_congr (a b : List Bool) (hr : pairFst a=pairFst b)
    (hb : prefixLength P a=prefixLength P b) : selectedCode P F a=selectedCode P F b := by
  unfold selectedCode inLater
  rw [hr,hb]

theorem fallback_readback (key : List Bool) :
    WordList.get (fallback P F (pairFst key)) (IntegralMixedHeaderTablesBits.fallbackIndex P key) =
      IntegralMixedCommandHeaderBits.encode (IntegralMixedCommandHeaderBits.selection
        ((data P O F C h hn hcap hW hroom hSW).fallback key)) := by
  let i := IntegralMixedHeaderTablesBits.fallbackIndex P key
  have HI : i<5*(P.cap (pairFst key)+2) := IntegralMixedHeaderTablesBits.fallbackIndex_lt P key
  have HD : i/5=prefixLength P key := by
    have HC : min (Nat.fromBitsLE (pairSnd (pairSnd key))) 4≤4 := min_le_right _ _
    change (5*IntegralMixedFullHistoryFamilyBits.prefixLength P key+min (Nat.fromBitsLE (pairSnd (pairSnd key))) 4)/5=
      IntegralMixedFullHistoryFamilyBits.prefixLength P key
    omega
  have HR : pairFst (fallbackKey (pairFst key) i)=pairFst key := IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _
  have HB : prefixLength P (fallbackKey (pairFst key) i)=prefixLength P key := by
    unfold fallbackKey
    rw [HD]
    exact IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P _ _ _ (min_le_right _ _)
  have HE := selectedCode_congr P F _ _ HR HB
  change WordList.get (fallback P F (pairFst key)) i = _
  rw [fallback,WordList.get_encode]
  simp only [List.getElem?_map,List.getElem?_range HI,Option.map_some,Option.getD_some]
  rw [HE]
  change _ = IntegralMixedCommandHeaderBits.encode (IntegralMixedCommandHeaderBits.selection
    (IntegralMixedCanonicalUnitRuleBits.selection
      (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P O F C h hn hcap hW hroom) key).source
      (hn (pairFst key)) (prefixLength P key) (selectedCode P F key)))
  rw [IntegralMixedCanonicalUnitHeaderBits.selection_eq,(data P O F C h hn hcap hW hroom hSW).degree_eq key]

theorem represents : IntegralMixedFramedHeaderBits.Represents P (plan P O F C h hn hcap hW hroom)
    (data P O F C h hn hcap hW hroom hSW) (tables P F) :=
  ⟨commands_represents P O F C h hn hcap hW hroom,
    fallback_readback P O F C h hn hcap hW hroom hSW⟩

end LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitHeaders
