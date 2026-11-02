/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedEmptyUnitSnapshot
public import LeanCanny.Encoding.IntegralMixedEmptyUnitHeaders
public import LeanCanny.Encoding.IntegralMixedEmptyIntegerOriginal
public import LeanCanny.Encoding.FlatAffineExceptionalCanonicalTiltedNativeBody
public import LeanCanny.Algebra.IntegralMixedFramedNativePlanned
public import LeanCanny.Algebra.IntegralMixedFramedUnitSourceBounds
/-! # Original-only native arithmetic for an empty-prelude tilted plan

The canonical records construct their sources, bodies, snapshots and headers.
Integer padding is the constant original word X. Every selector reads the
actual source index (zero outside the record range) through a unary-birth
packet. No exceptional-bank input, interpreted evaluator, coefficient cost,
or caller-supplied syntax agreement is an argument.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedEmptyTiltedNative
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical

abbrev Description (P : Parameters) := FlatAffineExceptionalCanonicalTiltedNative.Description P
noncomputable abbrev originals (P : Parameters) (s : Description P) :=
  FlatAffineExceptionalCanonicalTiltedNative.originals P s

noncomputable abbrev plan (P : Parameters) (s : Description P)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (hroom : ∀ root, IntegralMixedEmptyUnitPlan.count root+2≤P.cap root+1) :=
  IntegralMixedEmptyUnitPlan.plan P (originals P s) hn hcap hroom

noncomputable abbrev data (P : Parameters) (s : Description P)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (hroom : ∀ root, IntegralMixedEmptyUnitPlan.count root+2≤P.cap root+1)
    (hSW : ∀ root, (P.degree root).size≤P.sourceWidth root) :=
  IntegralMixedEmptyUnitPlan.data P (originals P s) hn hcap hroom hSW

noncomputable def packet (P : Parameters) (key : List Bool) :=
  pair (pairFst key) (List.replicate (IntegralMixedEmptyUnitPlan.sourceIndex P key) true)

theorem packet_FP (P : Parameters) (a : Access P) : packet P∈FP :=
  mem_FP_pair pairFst_mem_FP ((IntegralMixedEmptyUnitPlan.sourceIndex_unary P a).replicate_mem_FP true)

noncomputable def selected (P : Parameters) (v : List Bool → ℕ → ℕ) (key : List Bool) :=
  v (pairFst key) (IntegralMixedEmptyUnitPlan.sourceIndex P key)

theorem selected_unary (P : Parameters) (a : Access P) (v : List Bool → ℕ → ℕ)
    (hv : UnaryFn (fun q => v (pairFst q) (pairSnd q).length)) : UnaryFn (selected P v) := by
  apply (hv.comp (packet_FP P a)).of_eq
  intro key
  simp only [packet,pairFst_pair,pairSnd_pair,List.length_replicate,selected]

theorem selected_binary (P : Parameters) (a : Access P) (v : List Bool → ℕ → ℕ)
    (hv : BinaryFn (fun q => v (pairFst q) (pairSnd q).length)) : BinaryFn (selected P v) := by
  have HB : BinaryFn (fun key => v (pairFst (packet P key)) (pairSnd (packet P key)).length) := hv.comp (packet_FP P a)
  apply BinaryFn.of_eq HB
  intro key
  simp only [packet,pairFst_pair,pairSnd_pair,List.length_replicate,selected]

noncomputable def inputSyntax (P : Parameters) (a : Access P) (s : Description P)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (hroom : ∀ root, IntegralMixedEmptyUnitPlan.count root+2≤P.cap root+1)
    (hSW : ∀ root, (P.degree root).size≤P.sourceWidth root) :
    IntegralMixedFramedNativeBits.Syntax P (plan P s hn hcap hroom) (data P s hn hcap hroom hSW) where
  unit := IntegralMixedEmptyUnitPlan.unitControls P (originals P s) hn hcap hroom hSW a
    (IntegralMixedEmptyUnitPlan.tables P) (IntegralMixedEmptyUnitPlan.native P a)
    (IntegralMixedEmptyUnitPlan.represents P (originals P s) hn hcap hroom hSW)
  term key := s.term (pairFst key)
  frozen := selected P s.frozen
  tilt := selected P s.tilt
  exponent := selected P s.exponent
  term_FP := mem_FP_comp pairFst_mem_FP s.term_FP
  frozen_native := selected_unary P a s.frozen s.frozen_native
  tilt_native := selected_unary P a s.tilt s.tilt_native
  exponent_native := selected_binary P a s.exponent s.exponent_native
  term_scope key := s.term_scope (pairFst key)
  tilt_scope key := s.tilt_scope (pairFst key) _
  low key := by
    rw [IntegralMixedEmptyUnitPlan.instruction_source P (originals P s) hn hcap hroom key]
    exact IntegralMixedCanonicalTiltedSourceBits.low_saved P s.term s.frozen s.tilt s.exponent s.degree
      (IntegralMixedEmptyUnitPlan.sourceIndex P) key
  integerWord := IntegralMixedEmptyUnitPlan.integerWord
  integer_FP := IntegralMixedEmptyUnitPlan.integerWord_FP
  integer := IntegralMixedEmptyUnitPlan.integerWord_polynomial P (originals P s) hn hcap hroom
  nodes _ := 1
  factor := s.factor
  seed := s.seed
  nodes_native := BinaryFn.const 1
  factor_native := s.factor_native
  seed_native := s.seed_native

noncomputable def controls (P : Parameters) (a : Access P) (s : Description P)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (hroom : ∀ root, IntegralMixedEmptyUnitPlan.count root+2≤P.cap root+1)
    (hSW : ∀ root, (P.degree root).size≤P.sourceWidth root) :=
  IntegralMixedFramedNativeBits.Controls.ofSyntax P a _ _ (inputSyntax P a s hn hcap hroom hSW)

noncomputable def plannedMachine (P : Parameters) (a : Access P) (s : Description P)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (hroom : ∀ root, IntegralMixedEmptyUnitPlan.count root+2≤P.cap root+1)
    (hSW : ∀ root, (P.degree root).size≤P.sourceWidth root) :=
  IntegralMixedFramedNativeBits.plannedMachine P a _ _ (inputSyntax P a s hn hcap hroom hSW)

theorem planned_model_space (P : Parameters) (a : Access P) (s : Description P)
    (hn : ∀ root, 0<P.ambient root)
    (hcap : ∀ root, IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (hroom : ∀ root, IntegralMixedEmptyUnitPlan.count root+2≤P.cap root+1)
    (hSW : ∀ root, (P.degree root).size≤P.sourceWidth root)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P (plan P s hn hcap hroom) (fun _ => 1) s.factor s.seed) :
    SpaceFunction (plannedMachine P a s hn hcap hroom hSW).model :=
  IntegralMixedFramedNativeBits.planned_model_space P a _ _ (inputSyntax P a s hn hcap hroom hSW) hs s.factor_positive
    (IntegralMixedFramedUnitSourceBounds.fallback_bounds P _ _
      (inputSyntax P a s hn hcap hroom hSW).unit.writer (inputSyntax P a s hn hcap hroom hSW).unit.snapshot
      (fun _ => 1) s.seed (fun _ => Nat.le_refl _))

end LeanCanny.Encoding.IntegralMixedEmptyTiltedNative
