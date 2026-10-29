/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleHashEnumeration

/-! # Native validity and enumeration of short regular square-system descriptors

Canonical signed integer words name the selected injective hash values.
Validity charges parameter selection and the determinant cut reader. Each
valid descriptor names one regular square-system root, and every ordinal
below the native regular square-system count produces such a word. Downstream
`SquareSampleTestSign` reads polynomial signs at these labels;
all system equations are enforced before labeling.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleDescriptors
open LeanCanny.Algebra LeanCanny.Computation
open Brackets
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SquareSampleRecords.length SquareSampleThom.labelWidth
  SquareSampleCoordinates.parameterDegree SquareSampleCoordinates.baseHeight
  SquareSampleQueries.roots SquareSampleRegularCount.count

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
    (∃ x : SquareSampleRecordSpan.Root P c, SquareSampleHashChoice.descriptor P c x = w) ↔
      Canonical w ∧ integer w ∈ SquareSampleHashRoots.values P c := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨canonical_code _, ?_⟩
    rw [SquareSampleHashChoice.descriptor, integer_code]
    exact (SquareSampleHashRoots.mem_values P c _).mpr
      ⟨x, rfl⟩
  · rintro ⟨hc, hv⟩
    obtain ⟨theta, he⟩ := (SquareSampleHashRoots.mem_values P c _).mp hv
    refine ⟨theta, ?_⟩
    simp only [SquareSampleHashChoice.descriptor, he]
    exact (difference_integer w).symm.trans hc

def language (P : Inputs) : Language := {q | ∃ x : SquareSampleRecordSpan.Root P (pairFst q),
  SquareSampleHashChoice.descriptor P (pairFst q) x = pairSnd q}

noncomputable def candidateWord (P : Inputs) (c : List Bool) (z : SquareSampleParameters.Candidates P c) : List Bool :=
  SquareSampleHashChoice.descriptor P c
    ((SquareSampleHashEnumeration.rootCandidateEquiv P c).symm z)

theorem language_iff_candidate (P : Inputs) (q : List Bool) : q ∈ language P ↔
    ∃ z : SquareSampleParameters.Candidates P (pairFst q), candidateWord P (pairFst q) z = pairSnd q := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨SquareSampleHashEnumeration.rootCandidateEquiv P (pairFst q) x, ?_⟩
    simpa only [candidateWord, Equiv.symm_apply_apply] using hx
  · rintro ⟨z, hz⟩
    exact ⟨(SquareSampleHashEnumeration.rootCandidateEquiv P (pairFst q)).symm z, hz⟩

theorem unique_candidate (P : Inputs) (q : List Bool) (hq : q ∈ language P) :
    ∃! z : SquareSampleParameters.Candidates P (pairFst q), candidateWord P (pairFst q) z = pairSnd q := by
  obtain ⟨z, hz⟩ := (language_iff_candidate P q).mp hq
  refine ⟨z, hz, ?_⟩
  intro y hy
  apply (SquareSampleHashEnumeration.rootCandidateEquiv P (pairFst q)).symm.injective
  exact SquareSampleHashChoice.descriptor_injective P (pairFst q) (hy.trans hz.symm)

theorem candidateWord_enumerated (P : Inputs) (c : List Bool) (r : Fin (SquareSampleRegularCount.count P c)) :
    candidateWord P c (SquareSampleHashEnumeration.candidateEquiv P c r) =
      SignStatisticBits.integerCode (SquareSampleHashEnumeration.value P (pair c (BinaryNatCode.encode r.val))) := by
  change SquareSampleHashChoice.descriptor P c
    ((SquareSampleHashEnumeration.rootCandidateEquiv P c).symm
      (SquareSampleHashEnumeration.rootCandidateEquiv P c (SquareSampleHashEnumeration.root P c r))) = _
  rw [Equiv.symm_apply_apply]
  exact SquareSampleHashEnumeration.descriptor_root P c r

theorem language_iff (P : Inputs) (q : List Bool) : q ∈ language P ↔
    Canonical (pairSnd q) ∧ integer (pairSnd q) ∈ SquareSampleHashRoots.values P (pairFst q) :=
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
    cutQuery q ∈ SquareSampleHashCuts.language P ↔
      integer (pairSnd q) ∈ SquareSampleHashRoots.values P (pairFst q) :=
  SquareSampleHashCuts.language_at_integer P (cutQuery q) (pairFst q) (integer (pairSnd q))
    (pairFst_pair _ _) (cut_threshold q)

noncomputable def accept (z : List Bool) : Bool := decide
  (Canonical (pairSnd (pairFst z)) ∧ 0 < Nat.fromBitsLE (pairSnd z))

theorem accept_FP : (fun z => [accept z]) ∈ FP :=
  ((canonical_FP.comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)).and
    ((BinaryFn.const 0).lt (BinaryFn.fromBits pairSnd_mem_FP))).flag_mem_FP

theorem decider {P : Inputs} (h : P.Access) : SpaceDecider (language P) := by
  have E := ((SquareSampleHashCuts.evaluator h 0).precompose cutQuery cutQuery_FP).withInput
  apply E.decider accept accept_FP
  intro q
  simp only [accept, Function.comp_apply, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, decide_eq_true_eq]
  rw [SquareSampleHashCuts.count_zero_pos_iff, cut_mem_iff]
  exact realized_iff P (pairFst q) (pairSnd q)

theorem mem_PSPACE {P : Inputs} (h : P.Access) : language P ∈ PSPACE :=
  (decider h).mem_PSPACE

theorem unique_root (P : Inputs) (q : List Bool) (hq : q ∈ language P) :
    ∃! x : SquareSampleRecordSpan.Root P (pairFst q),
      SquareSampleHashChoice.descriptor P (pairFst q) x = pairSnd q := by
  obtain ⟨x, hx⟩ := hq
  exact ⟨x, hx, fun y hy => SquareSampleHashChoice.descriptor_injective P (pairFst q) (hy.trans hx.symm)⟩

theorem length_bound (P : Inputs) (q : List Bool) (hq : q ∈ language P) :
    (pairSnd q).length ≤ SquareSampleHashChoice.descriptorWidth P (pairFst q) := by
  obtain ⟨x, hx⟩ := hq
  rw [← hx]
  exact SquareSampleHashChoice.descriptor_length_le P (pairFst q) x

theorem enumerated_mem (P : Inputs) (c : List Bool) (r : ℕ) (hr : r < SquareSampleRegularCount.count P c) :
    pair c (SignStatisticBits.integerCode (SquareSampleHashEnumeration.value P (pair c (BinaryNatCode.encode r)))) ∈
      language P := by
  change ∃ x : SquareSampleRecordSpan.Root P (pairFst (pair c
      (SignStatisticBits.integerCode (SquareSampleHashEnumeration.value P (pair c (BinaryNatCode.encode r)))))),
    SquareSampleHashChoice.descriptor P _ x = pairSnd (pair c
      (SignStatisticBits.integerCode (SquareSampleHashEnumeration.value P (pair c (BinaryNatCode.encode r)))))
  rw [pairFst_pair, pairSnd_pair]
  obtain ⟨x, hx, _⟩ := SquareSampleHashEnumeration.unique_root_descriptor P c r hr
  exact ⟨x, hx⟩

end LeanCanny.Encoding.SquareSampleDescriptors
