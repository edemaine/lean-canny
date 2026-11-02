/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitLookup
public import LeanCanny.Algebra.IntegralMixedCanonicalTiltedSource
/-! # Saved-source tilted bodies follow the actual canonical instruction

Initial integer instructions and all out-of-range defaults read source zero.
A later record reads its actual absolute birth source. The original selector
packet carries that birth in unary, supporting native causal powers without
treating an unbounded binary exponent as a unary loop count.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalCanonicalTiltedBody
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalCanonicalUnitPlan (inLater sourceIndex seedCount count)
open scoped Classical

theorem sourceIndex_unary (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access) :
    UnaryFn (sourceIndex P F) := by
  have HB : UnaryFn (fun key => seedCount F (pairFst key)) :=
    (FlatAffineExceptionalCanonicalUnitPlan.seedCount_unary hF).comp pairFst_mem_FP
  have HP : UnaryFn (IntegralMixedFramedHistoryFamilyBits.prefixLength P) :=
    IntegralMixedFullHistoryFamilyBits.prefix_unary P a
  have HN : UnaryFn (fun key => count (pairFst key)) :=
    FlatAffineExceptionalCanonicalUnitPlan.count_unary.comp pairFst_mem_FP
  have HI : BinaryFn (fun key => IntegralMixedFramedHistoryFamilyBits.prefixLength P key-seedCount F (pairFst key)) :=
    (BinaryFn.ofUnary HP).sub (BinaryFn.ofUnary HB)
  have HS : FPPred (inLater P F) := (FPPred.le HB HP).and (HI.lt (BinaryFn.ofUnary HN))
  exact UnaryFn.ite HS HP (UnaryFn.const 0)

noncomputable def packet (P : Parameters) (F : Inputs) (key : List Bool) : List Bool :=
  pair (pairFst key) (List.replicate (sourceIndex P F key) true)

theorem packet_FP (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access) : packet P F∈FP :=
  mem_FP_pair pairFst_mem_FP ((sourceIndex_unary P a hF).replicate_mem_FP true)

noncomputable def selected (P : Parameters) (F : Inputs) (v : List Bool → ℕ → ℕ) (key : List Bool) : ℕ :=
  v (pairFst key) (sourceIndex P F key)

theorem selected_unary (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access)
    (v : List Bool → ℕ → ℕ) (hv : UnaryFn (fun q => v (pairFst q) (pairSnd q).length)) :
    UnaryFn (selected P F v) := by
  apply (hv.comp (packet_FP P a hF)).of_eq
  intro key
  simp only [packet,pairFst_pair,pairSnd_pair,List.length_replicate,selected]

theorem selected_binary (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access)
    (v : List Bool → ℕ → ℕ) (hv : BinaryFn (fun q => v (pairFst q) (pairSnd q).length)) :
    BinaryFn (selected P F v) := by
  have HB : BinaryFn (fun key => v (pairFst (packet P F key)) (pairSnd (packet P F key)).length) :=
    hv.comp (packet_FP P a hF)
  apply BinaryFn.of_bits
  apply mem_FP_of_eq HB.bits_mem_FP
  intro key
  simp only [packet,pairFst_pair,pairSnd_pair,List.length_replicate,selected]

theorem term_FP (t : List Bool → ETR.Term) (ht : (fun root => (t root).toData.toBits)∈FP) :
    (fun key => (t (pairFst key)).toData.toBits)∈FP := mem_FP_comp pairFst_mem_FP ht

theorem low_identity (P : Parameters) (t : List Bool → ETR.Term) (k u E : List Bool → ℕ → ℕ)
    (hd : ∀ root, FixedLeadingTiltedSource.degree (t root).toData.size=P.degree root)
    (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (q : List Bool) → Fin (arity F q)) (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (hW : ∀ root, FlatAffineExceptionalBankSource.width F (FlatAffineExceptionalCanonicalUnitPlan.input root)≤P.width root)
    (hroom : ∀ root, count root+seedCount F root+2≤P.cap root+1) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.instruction P
      (FlatAffineExceptionalCanonicalUnitPlan.plan P (IntegralMixedCanonicalTiltedSourceBits.originals P t k u E hd)
        F C h hn hcap hW hroom) key).source.low=
      FermatLevelFramedTiltedSyntax.low P (fun z => t (pairFst z))
        (selected P F k) (selected P F u) (selected P F E) key := by
  rw [FlatAffineExceptionalCanonicalUnitPlan.instruction_source P _ F C h hn hcap hW hroom key]
  exact IntegralMixedCanonicalTiltedSourceBits.low_saved P t k u E hd (sourceIndex P F) key

end LeanCanny.Encoding.FlatAffineExceptionalCanonicalTiltedBody
