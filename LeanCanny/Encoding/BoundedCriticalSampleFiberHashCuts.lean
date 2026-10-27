/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberHashRoots

/-! # Native cut queries with hash parameters computed internally

Inputs retain the original source and a signed rational threshold. The
selected hash context is computed before calling the pencil cut reader.
Membership therefore certifies one specific fiber root, without
requiring a supplied hash context or a full derivative-sign record.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberHashCuts
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open scoped Classical

def finish (z : List Bool) : List Bool := pair (pairSnd z) (pairSnd (pairFst z))
theorem finish_FP : finish ∈ FP := mem_FP_pair pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

noncomputable def query (P : Readers) (F : BoundedAlgebraicSlice.Family) (q : List Bool) : List Bool :=
  pair (BoundedCriticalSampleFiberHashChoice.value P F (pairFst q)) (pairSnd q)
theorem query_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (query P F) := by
  have E := (BoundedCriticalSampleFiberHashChoice.evaluator h A ha).precompose pairFst pairFst_mem_FP
  have H := E.withInput.postcompose finish finish_FP
  exact H.congr (funext fun q => by simp only [query, finish, Function.comp_apply, pairFst_pair, pairSnd_pair])

theorem query_source (P : Readers) (F : BoundedAlgebraicSlice.Family) (q : List Bool) :
    pairFst (query P F q) = BoundedCriticalSampleFiberHashChoice.value P F (pairFst q) := pairFst_pair _ _
theorem query_threshold (P : Readers) (F : BoundedAlgebraicSlice.Family) (q : List Bool) :
    RationalCutBits.threshold (query P F q) = RationalCutBits.threshold q := by
  simp only [query, RationalCutBits.threshold, RationalCutBits.numerator, RationalCutBits.positive,
    RationalCutBits.negative, RationalCutBits.divisor, RationalCutBits.denominatorMinusOne, pairSnd_pair]

noncomputable def count (P : Readers) (F : BoundedAlgebraicSlice.Family) (σ : SignType) (q : List Bool) : ℕ :=
  BoundedCriticalSampleFiberPencilCuts.count P F σ (query P F q)
theorem evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (σ : SignType) :
    SpaceFunction (fun q => BinaryNatCode.encode (count P F σ q)) :=
  (query_evaluator h A ha).chain (BoundedCriticalSampleFiberPencilCuts.evaluator h A ha σ)

theorem count_below (P : Readers) (F : BoundedAlgebraicSlice.Family) (q : List Bool) : count P F .neg q =
    (((BoundedCriticalSampleFiberHashRoots.values P F (pairFst q)).image (Int.castRingHom ℝ)).filter
      (fun x => x < RationalCutBits.threshold q)).card := by
  rw [count, BoundedCriticalSampleFiberPencilCuts.count_below, query_source, query_threshold, BoundedCriticalSampleFiberHashRoots.rootSet_eq]

noncomputable def language (P : Readers) (F : BoundedAlgebraicSlice.Family) : Language := {q |
  RationalCutBits.threshold q ∈ (BoundedCriticalSampleFiberHashRoots.values P F (pairFst q)).image (Int.castRingHom ℝ)}

theorem count_zero_pos_iff (P : Readers) (F : BoundedAlgebraicSlice.Family) (q : List Bool) : 0 < count P F 0 q ↔ q ∈ language P F := by
  rw [count, BoundedCriticalSampleFiberPencilCuts.count_zero_pos_iff, query_source, query_threshold,
    BoundedCriticalSampleFiberHashRoots.rootSet_eq]
  rfl

theorem count_below_at_integer (P : Readers) (F : BoundedAlgebraicSlice.Family) (q c : List Bool) (z : ℤ)
    (hc : pairFst q = c) (hz : RationalCutBits.threshold q = (z : ℝ)) :
    count P F .neg q = BoundedCriticalSampleFiberHashRoots.rank P F c z := by
  rw [count_below, hc, hz, Finset.filter_image,
    Finset.card_image_of_injective _ (show Function.Injective (Int.castRingHom ℝ) from Int.cast_injective)]
  simp only [Int.coe_castRingHom, Int.cast_lt]
  rfl

theorem language_at_integer (P : Readers) (F : BoundedAlgebraicSlice.Family) (q c : List Bool) (z : ℤ)
    (hc : pairFst q = c) (hz : RationalCutBits.threshold q = (z : ℝ)) :
    q ∈ language P F ↔ z ∈ BoundedCriticalSampleFiberHashRoots.values P F c := by
  change RationalCutBits.threshold q ∈ (BoundedCriticalSampleFiberHashRoots.values P F (pairFst q)).image (Int.castRingHom ℝ) ↔ _
  rw [hc, hz]
  simp only [Finset.mem_image, Int.coe_castRingHom, Int.cast_inj, exists_eq_right]

theorem decider {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (language P F) := by
  have E := evaluator h A ha 0
  have hc := ((BinaryFn.const 0).lt (BinaryFn.fromBits id_mem_FP)).flag_mem_FP
  apply E.decider (fun z => decide (0 < Nat.fromBitsLE z)) hc
  intro q
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq, language, Set.mem_ofPred_eq]
  rw [count, BoundedCriticalSampleFiberPencilCuts.count_zero_pos_iff, query_source, query_threshold,
    BoundedCriticalSampleFiberHashRoots.rootSet_eq]

theorem unique_root (P : Readers) (F : BoundedAlgebraicSlice.Family) (q : List Bool) (hq : q ∈ language P F) :
    ∃! x : BoundedCriticalSampleFiberRecordSpan.Root P F (pairFst q),
      (BoundedCriticalSampleFiberHashChoice.hash P F (pairFst q) x : ℝ) = RationalCutBits.threshold q := by
  obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hq
  obtain ⟨x, hx⟩ := (BoundedCriticalSampleFiberHashRoots.mem_values P F (pairFst q) z).mp hz
  refine ⟨x, ?_, ?_⟩
  · simpa only [hx, Int.coe_castRingHom] using he
  · intro y hy
    apply BoundedCriticalSampleFiberHashChoice.hash_injective P F (pairFst q)
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

theorem integer_mem_iff (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (z : ℤ) :
    integerQuery c z ∈ language P F ↔ z ∈ BoundedCriticalSampleFiberHashRoots.values P F c := by
  change RationalCutBits.threshold (integerQuery c z) ∈
    (BoundedCriticalSampleFiberHashRoots.values P F (pairFst (integerQuery c z))).image (Int.castRingHom ℝ) ↔ _
  rw [integer_threshold]
  simp only [integerQuery, pairFst_pair, Finset.mem_image, Int.coe_castRingHom, Int.cast_inj, exists_eq_right]

end LeanCanny.Encoding.BoundedCriticalSampleFiberHashCuts
