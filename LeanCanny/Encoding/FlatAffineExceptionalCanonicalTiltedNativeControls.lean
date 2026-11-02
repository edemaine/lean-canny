/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalCanonicalTiltedNativeBody
/-! # All native controls for the actual canonical tilted plan

Later records are literal critical or limit-cut commands. Thus the actual
initial-bank polynomial source supplies all original integer leaves directly.
There is no integer word, natDegree FP hypothesis, coefficient cost oracle,
interpreted bank cost, or supplied body/snapshot agreement.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalCanonicalTiltedNative
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalCanonicalUnitPlan (count seedCount input)
open scoped Classical

theorem later_noninteger (P : Parameters) (s : Description P) (F : Inputs)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (root : List Bool) (c : Instruction (P.ambient root) (P.width root))
    (hc : c∈FlatAffineExceptionalCanonicalUnitPlan.later P (originals P s) F hn hcap root) :
    c.command.context≠0 := by
  change c∈(((List.range (count root)).map
    (FlatAffineExceptionalCanonicalUnitPlan.step P (originals P s) F hn hcap root)).reverse) at hc
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
  change (IntegralMixedCanonicalUnitRuleBits.command
    (IntegralMixedCanonicalUnitSourceBits.source P (originals P s) root (seedCount F root+i))
    (hn root) (seedCount F root+i) (FlatAffineExceptionalCanonicalUnitPlan.code root i) (hcap root)).context≠0
  unfold IntegralMixedCanonicalUnitRuleBits.command
  split_ifs
  · exact Nat.one_ne_zero
  · exact (by decide : (2:ℕ)≠0)

theorem integerOriginal (P : Parameters) (a : Access P) (s : Description P) {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (q : List Bool) → Fin (arity F q))
    (hh : UnaryFn (fun q => (h q).val)) (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (hW : ∀ root, FlatAffineExceptionalBankSource.width F (input root)≤P.width root)
    (hroom : ∀ root, count root+seedCount F root+2≤P.cap root+1) :
    IntegralMixedIntegerFamilyBits.Original P
      (IntegralMixedFramedIntegerBits.polynomial P (plan P s F C h hn hcap hW hroom)) :=
  FlatAffineExceptionalFramedIntegerOriginal.original P a
    (IntegralMixedCanonicalUnitSourceBits.seed P (originals P s) hcap (fun root => by have H:=hroom root; omega))
    hF C h hh input FlatAffineExceptionalCanonicalUnitPlan.input_FP
    (FlatAffineExceptionalCanonicalUnitPlan.later P (originals P s) F hn hcap) hW
    (fun root => by rw [FlatAffineExceptionalCanonicalUnitPlan.later_length]; exact hroom root)
    (later_noninteger P s F hn hcap)

noncomputable def controls (P : Parameters) (a : Access P) (s : Description P) {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (q : List Bool) → Fin (arity F q))
    (hh : UnaryFn (fun q => (h q).val)) (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (hW : ∀ root, FlatAffineExceptionalBankSource.width F (input root)≤P.width root)
    (hroom : ∀ root, count root+seedCount F root+2≤P.cap root+1)
    (hSW : ∀ root, (P.degree root).size≤P.sourceWidth root)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P (plan P s F C h hn hcap hW hroom)
      (data P s F C h hn hcap hW hroom hSW) T) :
    IntegralMixedFramedNativeBits.Controls P (plan P s F C h hn hcap hW hroom)
      (data P s F C h hn hcap hW hroom hSW) :=
  FlatAffineExceptionalFramedNative.bodyControls P a _ _
    (body P a s hF C h hn hcap hW hroom hSW T ht hr)
    (integerOriginal P a s hF C h hh hn hcap hW hroom)

end LeanCanny.Encoding.FlatAffineExceptionalCanonicalTiltedNative
