/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceSampleHashEnumeration

/-! # Native validity and enumeration of short regular flat descriptors

Canonical signed integer words name the selected injective hash values.
Validity charges parameter selection and the determinant cut reader. Each
valid descriptor names one regular flat root, and every ordinal
below the native regular flat count produces such a word. Downstream
`FlatFullSourceSampleTestSign` reads polynomial signs at these labels;
all ancestral constraints are already enforced by the complete flat equations.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceSampleDescriptors
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open Brackets
open FlatFullSourceTower (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourceSampleRecords.length FlatFullSourceSampleThom.labelWidth
  FlatFullSourceSampleCoordinates.parameterDegree FlatFullSourceSampleCoordinates.baseHeight
  FlatFullSourceSampleQueries.roots FlatFullSourceSampleRegularCount.count

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

theorem realized_iff (P : Inputs) (c w : List Bool) :
    (∃ x : FlatFullSourceSampleRecordSpan.Root P c, FlatFullSourceSampleHashChoice.descriptor P c x = w) ↔
      Canonical w ∧ integer w ∈ FlatFullSourceSampleHashRoots.values P c := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨canonical_code _, ?_⟩
    rw [FlatFullSourceSampleHashChoice.descriptor, integer_code]
    exact (FlatFullSourceSampleHashRoots.mem_values P c _).mpr
      ⟨x, rfl⟩
  · rintro ⟨hc, hv⟩
    obtain ⟨theta, he⟩ := (FlatFullSourceSampleHashRoots.mem_values P c _).mp hv
    refine ⟨theta, ?_⟩
    simp only [FlatFullSourceSampleHashChoice.descriptor, he]
    exact (difference_integer w).symm.trans hc

def language (P : Inputs) : Language := {q | ∃ x : FlatFullSourceSampleRecordSpan.Root P (pairFst q),
  FlatFullSourceSampleHashChoice.descriptor P (pairFst q) x = pairSnd q}

noncomputable def candidateWord (P : Inputs) (c : List Bool) (z : FlatFullSourceSampleParameters.Candidates P c) : List Bool :=
  FlatFullSourceSampleHashChoice.descriptor P c
    ((FlatFullSourceSampleHashEnumeration.rootCandidateEquiv P c).symm z)

theorem language_iff_candidate (P : Inputs) (q : List Bool) : q ∈ language P ↔
    ∃ z : FlatFullSourceSampleParameters.Candidates P (pairFst q), candidateWord P (pairFst q) z = pairSnd q := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨FlatFullSourceSampleHashEnumeration.rootCandidateEquiv P (pairFst q) x, ?_⟩
    simpa only [candidateWord, Equiv.symm_apply_apply] using hx
  · rintro ⟨z, hz⟩
    exact ⟨(FlatFullSourceSampleHashEnumeration.rootCandidateEquiv P (pairFst q)).symm z, hz⟩

theorem unique_candidate (P : Inputs) (q : List Bool) (hq : q ∈ language P) :
    ∃! z : FlatFullSourceSampleParameters.Candidates P (pairFst q), candidateWord P (pairFst q) z = pairSnd q := by
  obtain ⟨z, hz⟩ := (language_iff_candidate P q).mp hq
  refine ⟨z, hz, ?_⟩
  intro y hy
  apply (FlatFullSourceSampleHashEnumeration.rootCandidateEquiv P (pairFst q)).symm.injective
  exact FlatFullSourceSampleHashChoice.descriptor_injective P (pairFst q) (hy.trans hz.symm)

theorem candidateWord_enumerated (P : Inputs) (c : List Bool) (r : Fin (FlatFullSourceSampleRegularCount.count P c)) :
    candidateWord P c (FlatFullSourceSampleHashEnumeration.candidateEquiv P c r) =
      SignStatisticBits.integerCode (FlatFullSourceSampleHashEnumeration.value P (pair c (BinaryNatCode.encode r.val))) := by
  change FlatFullSourceSampleHashChoice.descriptor P c
    ((FlatFullSourceSampleHashEnumeration.rootCandidateEquiv P c).symm
      (FlatFullSourceSampleHashEnumeration.rootCandidateEquiv P c (FlatFullSourceSampleHashEnumeration.root P c r))) = _
  rw [Equiv.symm_apply_apply]
  exact FlatFullSourceSampleHashEnumeration.descriptor_root P c r

theorem language_iff (P : Inputs) (q : List Bool) : q ∈ language P ↔
    Canonical (pairSnd q) ∧ integer (pairSnd q) ∈ FlatFullSourceSampleHashRoots.values P (pairFst q) :=
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

theorem cut_mem_iff (P : Inputs) (q : List Bool) :
    cutQuery q ∈ FlatFullSourceSampleHashCuts.language P ↔
      integer (pairSnd q) ∈ FlatFullSourceSampleHashRoots.values P (pairFst q) :=
  FlatFullSourceSampleHashCuts.language_at_integer P (cutQuery q) (pairFst q) (integer (pairSnd q))
    (pairFst_pair _ _) (cut_threshold q)

noncomputable def accept (z : List Bool) : Bool := decide
  (Canonical (pairSnd (pairFst z)) ∧ 0 < Nat.fromBitsLE (pairSnd z))

theorem accept_FP : (fun z => [accept z]) ∈ FP :=
  ((canonical_FP.comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)).and
    ((BinaryFn.const 0).lt (BinaryFn.fromBits pairSnd_mem_FP))).flag_mem_FP

theorem decider {P : Inputs} (h : P.Access) : SpaceDecider (language P) := by
  have E := ((FlatFullSourceSampleHashCuts.evaluator h 0).precompose cutQuery cutQuery_FP).withInput
  apply E.decider accept accept_FP
  intro q
  simp only [accept, Function.comp_apply, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, decide_eq_true_eq]
  rw [FlatFullSourceSampleHashCuts.count_zero_pos_iff, cut_mem_iff]
  exact realized_iff P (pairFst q) (pairSnd q)

theorem mem_PSPACE {P : Inputs} (h : P.Access) : language P ∈ PSPACE :=
  (decider h).mem_PSPACE

theorem unique_root (P : Inputs) (q : List Bool) (hq : q ∈ language P) :
    ∃! x : FlatFullSourceSampleRecordSpan.Root P (pairFst q),
      FlatFullSourceSampleHashChoice.descriptor P (pairFst q) x = pairSnd q := by
  obtain ⟨x, hx⟩ := hq
  exact ⟨x, hx, fun y hy => FlatFullSourceSampleHashChoice.descriptor_injective P (pairFst q) (hy.trans hx.symm)⟩

theorem length_bound (P : Inputs) (q : List Bool) (hq : q ∈ language P) :
    (pairSnd q).length ≤ FlatFullSourceSampleHashChoice.descriptorWidth P (pairFst q) := by
  obtain ⟨x, hx⟩ := hq
  rw [← hx]
  exact FlatFullSourceSampleHashChoice.descriptor_length_le P (pairFst q) x

theorem enumerated_mem (P : Inputs) (c : List Bool) (r : ℕ) (hr : r < FlatFullSourceSampleRegularCount.count P c) :
    pair c (SignStatisticBits.integerCode (FlatFullSourceSampleHashEnumeration.value P (pair c (BinaryNatCode.encode r)))) ∈
      language P := by
  change ∃ x : FlatFullSourceSampleRecordSpan.Root P (pairFst (pair c
      (SignStatisticBits.integerCode (FlatFullSourceSampleHashEnumeration.value P (pair c (BinaryNatCode.encode r)))))),
    FlatFullSourceSampleHashChoice.descriptor P _ x = pairSnd (pair c
      (SignStatisticBits.integerCode (FlatFullSourceSampleHashEnumeration.value P (pair c (BinaryNatCode.encode r)))))
  rw [pairFst_pair, pairSnd_pair]
  obtain ⟨x, hx, _⟩ := FlatFullSourceSampleHashEnumeration.unique_root_descriptor P c r hr
  exact ⟨x, hx⟩

end LeanCanny.Encoding.FlatFullSourceSampleDescriptors
