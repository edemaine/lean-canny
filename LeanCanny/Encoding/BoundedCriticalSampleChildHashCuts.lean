/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleChildHashRoots

/-! # Native cut queries with hash parameters computed internally

Inputs retain the original source and a signed rational threshold. The
selected hash context is computed before calling the pencil cut reader.
Membership therefore certifies one specific regular child root, without
requiring a supplied hash context or a full derivative-sign record.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleChildHashCuts
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedCriticalSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleChildRecords.length BoundedCriticalSampleChildThom.labelWidth
  BoundedCriticalSampleChildCoordinates.parameterDegree BoundedCriticalSampleChildCoordinates.baseHeight
  BoundedCriticalSampleChildQueries.roots BoundedCriticalSampleChildRegularCount.count

def finish (z : List Bool) : List Bool := pair (pairSnd z) (pairSnd (pairFst z))
theorem finish_FP : finish ∈ FP := mem_FP_pair pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

noncomputable def query (P : Inputs) (q : List Bool) : List Bool :=
  pair (BoundedCriticalSampleChildHashChoice.value P (pairFst q)) (pairSnd q)
theorem query_evaluator {P : Inputs} (h : P.PolyTime) : SpaceFunction (query P) := by
  have E := (BoundedCriticalSampleChildHashChoice.evaluator h).precompose pairFst pairFst_mem_FP
  have H := E.withInput.postcompose finish finish_FP
  exact H.congr (funext fun q => by simp only [query, finish, Function.comp_apply, pairFst_pair, pairSnd_pair])

theorem query_source (P : Inputs) (q : List Bool) :
    pairFst (query P q) = BoundedCriticalSampleChildHashChoice.value P (pairFst q) := pairFst_pair _ _
theorem query_threshold (P : Inputs) (q : List Bool) :
    RationalCutBits.threshold (query P q) = RationalCutBits.threshold q := by
  simp only [query, RationalCutBits.threshold, RationalCutBits.numerator, RationalCutBits.positive,
    RationalCutBits.negative, RationalCutBits.divisor, RationalCutBits.denominatorMinusOne, pairSnd_pair]

noncomputable def count (P : Inputs) (σ : SignType) (q : List Bool) : ℕ :=
  BoundedCriticalSampleChildPencilCuts.count P σ (query P q)
theorem evaluator {P : Inputs} (h : P.PolyTime) (σ : SignType) :
    SpaceFunction (fun q => BinaryNatCode.encode (count P σ q)) :=
  (query_evaluator h).chain (BoundedCriticalSampleChildPencilCuts.evaluator h σ)

theorem count_below (P : Inputs) (q : List Bool) : count P .neg q =
    (((BoundedCriticalSampleChildHashRoots.values P (pairFst q)).image (Int.castRingHom ℝ)).filter
      (fun x => x < RationalCutBits.threshold q)).card := by
  rw [count, BoundedCriticalSampleChildPencilCuts.count_below, query_source, query_threshold, BoundedCriticalSampleChildHashRoots.rootSet_eq]

noncomputable def language (P : Inputs) : Language := {q |
  RationalCutBits.threshold q ∈ (BoundedCriticalSampleChildHashRoots.values P (pairFst q)).image (Int.castRingHom ℝ)}

theorem count_zero_pos_iff (P : Inputs) (q : List Bool) : 0 < count P 0 q ↔ q ∈ language P := by
  rw [count, BoundedCriticalSampleChildPencilCuts.count_zero_pos_iff, query_source, query_threshold,
    BoundedCriticalSampleChildHashRoots.rootSet_eq]
  rfl

theorem count_below_at_integer (P : Inputs) (q c : List Bool) (z : ℤ)
    (hc : pairFst q = c) (hz : RationalCutBits.threshold q = (z : ℝ)) :
    count P .neg q = BoundedCriticalSampleChildHashRoots.rank P c z := by
  rw [count_below, hc, hz, Finset.filter_image,
    Finset.card_image_of_injective _ (show Function.Injective (Int.castRingHom ℝ) from Int.cast_injective)]
  simp only [Int.coe_castRingHom, Int.cast_lt]
  rfl

theorem language_at_integer (P : Inputs) (q c : List Bool) (z : ℤ)
    (hc : pairFst q = c) (hz : RationalCutBits.threshold q = (z : ℝ)) :
    q ∈ language P ↔ z ∈ BoundedCriticalSampleChildHashRoots.values P c := by
  change RationalCutBits.threshold q ∈ (BoundedCriticalSampleChildHashRoots.values P (pairFst q)).image (Int.castRingHom ℝ) ↔ _
  rw [hc, hz]
  simp only [Finset.mem_image, Int.coe_castRingHom, Int.cast_inj, exists_eq_right]

theorem decider {P : Inputs} (h : P.PolyTime) : SpaceDecider (language P) := by
  have E := evaluator h 0
  have hc := ((BinaryFn.const 0).lt (BinaryFn.fromBits id_mem_FP)).flag_mem_FP
  apply E.decider (fun z => decide (0 < Nat.fromBitsLE z)) hc
  intro q
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq, language, Set.mem_ofPred_eq]
  rw [count, BoundedCriticalSampleChildPencilCuts.count_zero_pos_iff, query_source, query_threshold,
    BoundedCriticalSampleChildHashRoots.rootSet_eq]

theorem unique_root (P : Inputs) (q : List Bool) (hq : q ∈ language P) :
    ∃! x : BoundedCriticalSampleChildRecordSpan.Root P (pairFst q),
      (BoundedCriticalSampleChildHashChoice.hash P (pairFst q) x : ℝ) = RationalCutBits.threshold q := by
  obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hq
  obtain ⟨x, hx⟩ := (BoundedCriticalSampleChildHashRoots.mem_values P (pairFst q) z).mp hz
  refine ⟨x, ?_, ?_⟩
  · simpa only [hx, Int.coe_castRingHom] using he
  · intro y hy
    apply BoundedCriticalSampleChildHashChoice.hash_injective P (pairFst q)
    apply (Int.cast_injective (α := ℝ))
    exact hy.trans (by simpa only [hx, Int.coe_castRingHom] using he.symm)

def integerQuery (c : List Bool) (z : ℤ) : List Bool :=
  pair c (pair (BinaryNatCode.encode z.toNat) (pair (BinaryNatCode.encode (-z).toNat) []))
theorem integer_threshold (c : List Bool) (z : ℤ) : RationalCutBits.threshold (integerQuery c z) = (z : ℝ) := by
  have he : (z.toNat : ℤ) - (-z).toNat = z := by omega
  simp only [integerQuery, RationalCutBits.threshold, RationalCutBits.numerator, RationalCutBits.positive,
    RationalCutBits.negative, RationalCutBits.divisor, RationalCutBits.denominatorMinusOne, pairFst_pair,
    pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, show Nat.fromBitsLE ([] : List Bool) = 0 from rfl,
    Nat.zero_add, Nat.cast_one, div_one, he]

theorem integer_mem_iff (P : Inputs) (c : List Bool) (z : ℤ) :
    integerQuery c z ∈ language P ↔ z ∈ BoundedCriticalSampleChildHashRoots.values P c := by
  change RationalCutBits.threshold (integerQuery c z) ∈
    (BoundedCriticalSampleChildHashRoots.values P (pairFst (integerQuery c z))).image (Int.castRingHom ℝ) ↔ _
  rw [integer_threshold]
  simp only [integerQuery, pairFst_pair, Finset.mem_image, Int.coe_castRingHom, Int.cast_inj, exists_eq_right]

end LeanCanny.Encoding.BoundedCriticalSampleChildHashCuts
