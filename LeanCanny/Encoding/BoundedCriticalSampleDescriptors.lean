/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleHashEnumeration

/-! # Native validity and enumeration of short actual-sample descriptors

Canonical signed integer words name the selected injective hash values.
Validity charges parameter selection and the determinant cut reader. Each
valid descriptor names one actual full critical sample, and every ordinal
below the native sample count produces such a word. Individual polynomial
sign queries at these labels remain required.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleDescriptors
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open Brackets
open scoped Classical

def integer (w : List Bool) : ℤ := (Nat.fromBitsLE (pairFst w) : ℤ) - Nat.fromBitsLE (pairSnd w)
def Canonical (w : List Bool) : Prop := IntegerSumBits.difference w = w

theorem difference_integer (w : List Bool) :
    IntegerSumBits.difference w = SignStatisticBits.integerCode (integer w) := by
  simp only [IntegerSumBits.difference, BinaryNat.sub_pair, SignStatisticBits.integerCode, integer]
  congr 2 <;> omega

theorem integer_code (z : ℤ) : integer (SignStatisticBits.integerCode z) = z := by
  simp only [integer, SignStatisticBits.integerCode, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  omega

theorem canonical_code (z : ℤ) : Canonical (SignStatisticBits.integerCode z) := by
  rw [Canonical, difference_integer, integer_code]

theorem canonical_FP : FPPred Canonical := stringEq_fppred IntegerSumBits.difference_mem_FP id_mem_FP

theorem realized_iff (P : Readers) (c w : List Bool) :
    (∃ x : BoundedFullCriticalSamples.Samples P c, BoundedCriticalSampleHashChoice.descriptor P c x = w) ↔
      Canonical w ∧ integer w ∈ BoundedCriticalSampleHashRoots.values P c := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨canonical_code _, ?_⟩
    rw [BoundedCriticalSampleHashChoice.descriptor, integer_code]
    exact (BoundedCriticalSampleHashRoots.mem_values P c _).mpr
      ⟨BoundedCriticalSampleLabels.parameter P c x, rfl⟩
  · rintro ⟨hc, hv⟩
    obtain ⟨theta, he⟩ := (BoundedCriticalSampleHashRoots.mem_values P c _).mp hv
    refine ⟨BoundedCriticalSampleLabels.rootEquiv P c theta, ?_⟩
    simp only [BoundedCriticalSampleHashChoice.descriptor, BoundedCriticalSampleHashChoice.sampleHash,
      BoundedCriticalSampleLabels.parameter, Equiv.symm_apply_apply, he]
    exact (difference_integer w).symm.trans hc

def language (P : Readers) : Language := {q | ∃ x : BoundedFullCriticalSamples.Samples P (pairFst q),
  BoundedCriticalSampleHashChoice.descriptor P (pairFst q) x = pairSnd q}

theorem language_iff (P : Readers) (q : List Bool) : q ∈ language P ↔
    Canonical (pairSnd q) ∧ integer (pairSnd q) ∈ BoundedCriticalSampleHashRoots.values P (pairFst q) :=
  realized_iff P (pairFst q) (pairSnd q)

def cutQuery (q : List Bool) : List Bool := pair (pairFst q)
  (pair (pairFst (pairSnd q)) (pair (pairSnd (pairSnd q)) []))
theorem cutQuery_FP : cutQuery ∈ FP := mem_FP_pair pairFst_mem_FP
  (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) (constFn_mem_FP [])))

theorem cut_threshold (q : List Bool) : RationalCutBits.threshold (cutQuery q) = (integer (pairSnd q) : ℝ) := by
  simp only [cutQuery, RationalCutBits.threshold, RationalCutBits.numerator, RationalCutBits.positive,
    RationalCutBits.negative, RationalCutBits.divisor, RationalCutBits.denominatorMinusOne,
    pairFst_pair, pairSnd_pair, show Nat.fromBitsLE ([] : List Bool) = 0 from rfl,
    Nat.zero_add, Nat.cast_one, div_one, integer, Int.cast_sub, Int.cast_natCast]

theorem cut_mem_iff (P : Readers) (q : List Bool) :
    cutQuery q ∈ BoundedCriticalSampleHashCuts.language P ↔
      integer (pairSnd q) ∈ BoundedCriticalSampleHashRoots.values P (pairFst q) :=
  BoundedCriticalSampleHashCuts.language_at_integer P (cutQuery q) (pairFst q) (integer (pairSnd q))
    (pairFst_pair _ _) (cut_threshold q)

noncomputable def accept (z : List Bool) : Bool := decide
  (Canonical (pairSnd (pairFst z)) ∧ 0 < Nat.fromBitsLE (pairSnd z))

theorem accept_FP : (fun z => [accept z]) ∈ FP :=
  ((canonical_FP.comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)).and
    ((BinaryFn.const 0).lt (BinaryFn.fromBits pairSnd_mem_FP))).flag_mem_FP

theorem decider {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (language P) := by
  have E := ((BoundedCriticalSampleHashCuts.evaluator h ha 0).precompose cutQuery cutQuery_FP).withInput
  apply E.decider accept accept_FP
  intro q
  simp only [accept, Function.comp_apply, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, decide_eq_true_eq]
  rw [BoundedCriticalSampleHashCuts.count_zero_pos_iff, cut_mem_iff]
  exact realized_iff P (pairFst q) (pairSnd q)

theorem mem_PSPACE {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : language P ∈ PSPACE :=
  (decider h ha).mem_PSPACE

theorem unique_sample (P : Readers) (q : List Bool) (hq : q ∈ language P) :
    ∃! x : BoundedFullCriticalSamples.Samples P (pairFst q),
      BoundedCriticalSampleHashChoice.descriptor P (pairFst q) x = pairSnd q := by
  obtain ⟨x, hx⟩ := hq
  exact ⟨x, hx, fun y hy => BoundedCriticalSampleHashChoice.descriptor_injective P (pairFst q) (hy.trans hx.symm)⟩

theorem length_bound (P : Readers) (q : List Bool) (hq : q ∈ language P) :
    (pairSnd q).length ≤ BoundedCriticalSampleHashChoice.descriptorWidth P (pairFst q) := by
  obtain ⟨x, hx⟩ := hq
  rw [← hx]
  exact BoundedCriticalSampleHashChoice.descriptor_length_le P (pairFst q) x

theorem enumerated_mem (P : Readers) (c : List Bool) (r : ℕ) (hr : r < BoundedCriticalSampleCount.count P c) :
    pair c (SignStatisticBits.integerCode (BoundedCriticalSampleHashEnumeration.value P (pair c (BinaryNatCode.encode r)))) ∈
      language P := by
  change ∃ x : BoundedFullCriticalSamples.Samples P (pairFst (pair c
      (SignStatisticBits.integerCode (BoundedCriticalSampleHashEnumeration.value P (pair c (BinaryNatCode.encode r)))))),
    BoundedCriticalSampleHashChoice.descriptor P _ x = pairSnd (pair c
      (SignStatisticBits.integerCode (BoundedCriticalSampleHashEnumeration.value P (pair c (BinaryNatCode.encode r)))))
  rw [pairFst_pair, pairSnd_pair]
  obtain ⟨x, hx, _⟩ := BoundedCriticalSampleHashEnumeration.unique_sample_descriptor P c r hr
  exact ⟨x, hx⟩

end LeanCanny.Encoding.BoundedCriticalSampleDescriptors
