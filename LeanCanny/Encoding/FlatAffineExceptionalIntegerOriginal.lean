/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalIntegerProducer
/-! # Charged original integer access for the actual exceptional-bank history

The polynomial transport is proved by chronological lookup in the constructed
history. Only native original-input projection, initial width/room planning,
and integer-free later syntax remain parameters. No coefficient agreement or
whole mixed-history evaluator is assumed.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalIntegerProducer
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births width)
open scoped Classical

theorem original (P : Parameters) (a : Access P) (base : IntegralMixedFullHistoryFamilyBits.Data P)
    {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val))
    (input : List Bool → List Bool) (hi : input ∈ FP)
    (later : (root : List Bool) → List (Command (base.spatial root) (P.width root)))
    (hW : ∀ root, width F (input root) ≤ P.width root)
    (hroom : ∀ root, (later root).length + births F (input root) + 2 ≤ P.cap root + 1)
    (hno : ∀ root c, c ∈ later root → c.context ≠ 0) :
    IntegralMixedIntegerProducerSpaceBits.Original P (data P base F C h input later hW hroom) :=
  IntegralMixedIntegerProducerSpaceBits.original_of_source P (data P base F C h input later hW hroom)
    (FlatAffineExceptionalIntegerSource.source F C h) (FlatAffineExceptionalIntegerSource.access hF C h hh)
    (sourceQuery P F input ∘ IntegralMixedVirtualTaskBits.saved P)
    (mem_FP_comp (IntegralMixedVirtualTaskBits.saved_FP P a) (sourceQuery_FP P a hF input hi))
    (fun q => polynomial_source P base F C h input later hW hroom hno (IntegralMixedVirtualTaskBits.saved P q))

end LeanCanny.Encoding.FlatAffineExceptionalIntegerProducer
