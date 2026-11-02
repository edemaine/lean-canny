/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalCanonicalTiltedBody
public import LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitSnapshot
public import LeanCanny.Encoding.FlatAffineExceptionalFramedNativeControls
/-! # Canonical original records construct their complete native body

Original terms and unary-birth selector readers construct the spatial sources
and saved-source LOW words. Canonical records construct the unit-rule body
and snapshot. No interpreted coefficient, matrix, denominator, source LOW
agreement or unit snapshot is a supplied control. Header provenance and
original source scopes remain explicit frontend obligations.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalCanonicalTiltedNative
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalCanonicalUnitPlan (count seedCount input)
open scoped Classical

structure Description (P : Parameters) where
  term : List Bool → ETR.Term
  frozen : List Bool → ℕ → ℕ
  tilt : List Bool → ℕ → ℕ
  exponent : List Bool → ℕ → ℕ
  degree : ∀ root, FixedLeadingTiltedSource.degree (term root).toData.size=P.degree root
  term_FP : (fun root => (term root).toData.toBits)∈FP
  frozen_native : UnaryFn (fun q => frozen (pairFst q) (pairSnd q).length)
  tilt_native : UnaryFn (fun q => tilt (pairFst q) (pairSnd q).length)
  exponent_native : BinaryFn (fun q => exponent (pairFst q) (pairSnd q).length)
  term_scope : ∀ root, (term root).arity+1≤P.ambient root
  tilt_scope : ∀ root b, tilt root b+2≤P.ambient root
  factor : List Bool → ℕ
  seed : List Bool → ℕ
  factor_native : BinaryFn factor
  seed_native : BinaryFn seed
  factor_positive : ∀ root, 1≤factor root

noncomputable abbrev originals (P : Parameters) (s : Description P) :=
  IntegralMixedCanonicalTiltedSourceBits.originals P s.term s.frozen s.tilt s.exponent s.degree

noncomputable abbrev plan (P : Parameters) (s : Description P) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (q : List Bool) → Fin (arity F q))
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (hW : ∀ root, FlatAffineExceptionalBankSource.width F (input root)≤P.width root)
    (hroom : ∀ root, count root+seedCount F root+2≤P.cap root+1) :=
  FlatAffineExceptionalCanonicalUnitPlan.plan P (originals P s) F C h hn hcap hW hroom

noncomputable abbrev data (P : Parameters) (s : Description P) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (q : List Bool) → Fin (arity F q))
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (hW : ∀ root, FlatAffineExceptionalBankSource.width F (input root)≤P.width root)
    (hroom : ∀ root, count root+seedCount F root+2≤P.cap root+1)
    (hSW : ∀ root, (P.degree root).size≤P.sourceWidth root) :=
  FlatAffineExceptionalCanonicalUnitPlan.data P (originals P s) F C h hn hcap hW hroom hSW

noncomputable def body (P : Parameters) (a : Access P) (s : Description P) {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (q : List Bool) → Fin (arity F q))
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (hW : ∀ root, FlatAffineExceptionalBankSource.width F (input root)≤P.width root)
    (hroom : ∀ root, count root+seedCount F root+2≤P.cap root+1)
    (hSW : ∀ root, (P.degree root).size≤P.sourceWidth root)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P (plan P s F C h hn hcap hW hroom)
      (data P s F C h hn hcap hW hroom hSW) T) :
    FlatAffineExceptionalFramedNative.Body P (plan P s F C h hn hcap hW hroom)
      (data P s F C h hn hcap hW hroom hSW) where
  unit := FlatAffineExceptionalCanonicalUnitPlan.unitControls P (originals P s) F C h hn hcap hW hroom hSW a hF T ht hr
  term key := s.term (pairFst key)
  frozen := FlatAffineExceptionalCanonicalTiltedBody.selected P F s.frozen
  tilt := FlatAffineExceptionalCanonicalTiltedBody.selected P F s.tilt
  exponent := FlatAffineExceptionalCanonicalTiltedBody.selected P F s.exponent
  term_FP := FlatAffineExceptionalCanonicalTiltedBody.term_FP s.term s.term_FP
  frozen_native := FlatAffineExceptionalCanonicalTiltedBody.selected_unary P a hF s.frozen s.frozen_native
  tilt_native := FlatAffineExceptionalCanonicalTiltedBody.selected_unary P a hF s.tilt s.tilt_native
  exponent_native := FlatAffineExceptionalCanonicalTiltedBody.selected_binary P a hF s.exponent s.exponent_native
  term_scope key := s.term_scope (pairFst key)
  tilt_scope key := s.tilt_scope (pairFst key) _
  low := FlatAffineExceptionalCanonicalTiltedBody.low_identity P s.term s.frozen s.tilt s.exponent s.degree
    F C h hn hcap hW hroom
  nodes _ := 1
  factor := s.factor
  seed := s.seed
  nodes_native := BinaryFn.const 1
  factor_native := s.factor_native
  seed_native := s.seed_native

end LeanCanny.Encoding.FlatAffineExceptionalCanonicalTiltedNative
