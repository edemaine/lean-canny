/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleChildPencilRootCount
public import LeanCanny.Computation.BoundedChoice
public import LeanCanny.Computation.PSPACEClosure

/-! # Native selection of separating regular-child hash parameters

One fixed-width block holds a modulus predecessor and another a parameter.
The native Gram-pencil root counter tests each candidate. Existence of a
bounded prime witness guarantees a successful search, but the test accepts
any modulus producing an injective integer weighted sum. The actual root
count is computed internally before the search; it is not a supplied oracle.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleChildHashChoice
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedCriticalSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleChildRecords.length BoundedCriticalSampleChildThom.labelWidth
  BoundedCriticalSampleChildCoordinates.parameterDegree BoundedCriticalSampleChildCoordinates.baseHeight
  BoundedCriticalSampleChildQueries.roots BoundedCriticalSampleChildRegularCount.count

noncomputable def width (P : Inputs) (u : List Bool) : ℕ := BoundedCriticalSampleChildRootHash.bitWidth P (pairFst u)
theorem width_unary {P : Inputs} (h : P.PolyTime) : UnaryFn (width P) :=
  (BoundedCriticalSampleChildRootHash.bitWidth_unary h).comp pairFst_mem_FP

noncomputable def word (P : Inputs) (q : List Bool) : List Bool :=
  ImplicitGraph.word (2 * width P (pairFst q)) (Nat.fromBitsLE (pairSnd q))
theorem word_FP {P : Inputs} (h : P.PolyTime) : word P ∈ FP :=
  ImplicitGraph.word_computable (((UnaryFn.const 2).mul (width_unary h)).comp pairFst_mem_FP)
    (BinaryFn.fromBits pairSnd_mem_FP)

noncomputable def modulusWord (P : Inputs) (q : List Bool) : List Bool :=
  (word P q).take (width P (pairFst q))
noncomputable def parameterWord (P : Inputs) (q : List Bool) : List Bool :=
  ((word P q).drop (width P (pairFst q))).take (width P (pairFst q))
theorem modulusWord_FP {P : Inputs} (h : P.PolyTime) : modulusWord P ∈ FP :=
  take_mem_FP (word_FP h) ((width_unary h).comp pairFst_mem_FP)
theorem parameterWord_FP {P : Inputs} (h : P.PolyTime) : parameterWord P ∈ FP :=
  take_mem_FP (drop_mem_FP (word_FP h) ((width_unary h).comp pairFst_mem_FP)) ((width_unary h).comp pairFst_mem_FP)

theorem modulusWord_length (P : Inputs) (q : List Bool) : (modulusWord P q).length = width P (pairFst q) := by
  simp only [modulusWord, List.length_take, word, ImplicitGraph.length_word]
  omega
theorem parameterWord_length (P : Inputs) (q : List Bool) : (parameterWord P q).length = width P (pairFst q) := by
  simp only [parameterWord, List.length_take, List.length_drop, word, ImplicitGraph.length_word]
  omega

noncomputable def candidate (P : Inputs) (q : List Bool) : List Bool :=
  pair (pairFst (pairFst q)) (pair (BinaryNat.normalize (pairSnd (pairFst q)))
    (pair (modulusWord P q) (BinaryNat.normalize (parameterWord P q))))
theorem candidate_FP {P : Inputs} (h : P.PolyTime) : candidate P ∈ FP := by
  have ho := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hn := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  have ht := mem_FP_comp (parameterWord_FP h) BinaryNat.normalize_mem_FP
  exact mem_FP_pair ho (mem_FP_pair hn (mem_FP_pair (modulusWord_FP h) ht))

theorem candidate_context (P : Inputs) (u v : List Bool) : candidate P (pair u v) =
    BoundedCriticalSampleChildWeightedMoments.context (pairFst u) (Nat.fromBitsLE (pairSnd u))
      (modulusWord P (pair u v)) (Nat.fromBitsLE (parameterWord P (pair u v))) := by
  simp only [candidate, BoundedCriticalSampleChildWeightedMoments.context, pairFst_pair,
    BinaryNat.normalize_eq_bits, BinaryNatCode.encode]

noncomputable def language (P : Inputs) : Language := candidate P ⁻¹' BoundedCriticalSampleChildPencilRootCount.language P
theorem decider {P : Inputs} (h : P.PolyTime) : SpaceDecider (language P) :=
  (BoundedCriticalSampleChildPencilRootCount.decider h).precompose (candidate P) (candidate_FP h)

private theorem word_value (w k : ℕ) (hk : k < 2 ^ w) : Nat.fromBitsLE (ImplicitGraph.word w k) = k := by
  have he := FixedWidthNatVector.decode_block 1 w (fun _ => k) 0 (by decide) hk
  simp only [Nat.zero_mul, List.drop_zero] at he
  change Nat.fromBitsLE ((ImplicitGraph.word w k).take w) = k at he
  simpa only [List.take_of_length_le (ImplicitGraph.length_word w k).le] using he

theorem exists_candidate (P : Inputs) (c : List Bool) :
    ∃ k < 2 ^ (2 * BoundedCriticalSampleChildRootHash.bitWidth P c),
      pair (pair c (BinaryNatCode.encode (BoundedCriticalSampleChildRegularCount.count P c))) (BinaryNatCode.encode k) ∈ language P := by
  obtain ⟨p, t, hp, hs, ht, hi⟩ := BoundedCriticalSampleChildRootHash.exists_short_labels P c
  let w := BoundedCriticalSampleChildRootHash.bitWidth P c
  let a := ImplicitGraph.word w (p - 1)
  let b := ImplicitGraph.word w t
  let r := a ++ b
  have ha : a.length = w := ImplicitGraph.length_word _ _
  have hb : b.length = w := ImplicitGraph.length_word _ _
  have hr : r.length = 2 * w := by rw [List.length_append, ha, hb]; omega
  have ham : Nat.fromBitsLE a + 1 = p := by
    have hv := word_value w (p - 1) (by dsimp [w]; omega)
    change Nat.fromBitsLE a = p - 1 at hv
    have hp0 := hp.pos
    omega
  have hbt : Nat.fromBitsLE b = t := word_value w t (ht.trans hs)
  let u := pair c (BinaryNatCode.encode (BoundedCriticalSampleChildRegularCount.count P c))
  let q := pair u (BinaryNatCode.encode (Nat.fromBitsLE r))
  have hw : width P (pairFst q) = w := by simp only [width, q, u, pairFst_pair]; rfl
  have hword : word P q = r := by
    simp only [word, width, q, u, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rw [← hr, ImplicitGraph.word_fromBitsLE]
  have hm : modulusWord P q = a := by
    rw [modulusWord, hword, hw]
    change (a ++ b).take w = a
    rw [← ha, List.take_left]
  have hparam : parameterWord P q = b := by
    rw [parameterWord, hword, hw]
    change ((a ++ b).drop w).take w = b
    rw [← ha, List.drop_left, ha, ← hb, List.take_length]
  refine ⟨Nat.fromBitsLE r, ?_, ?_⟩
  · simpa only [hr] using Nat.fromBitsLE_lt_pow_length r
  · change candidate P q ∈ BoundedCriticalSampleChildPencilRootCount.language P
    rw [show q = pair u (BinaryNatCode.encode (Nat.fromBitsLE r)) from rfl, candidate_context]
    simp only [u, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    change BoundedCriticalSampleChildWeightedMoments.context c (BoundedCriticalSampleChildRegularCount.count P c)
      (modulusWord P q) (Nat.fromBitsLE (parameterWord P q)) ∈ _
    rw [hm, hparam, hbt, BoundedCriticalSampleChildPencilRootCount.language_packet]
    rw [ham]
    exact BoundedCriticalSampleChildRootHash.integerValue_injective P c p t hi

noncomputable def bound (P : Inputs) (u : List Bool) : ℕ := 2 ^ (2 * width P u)
theorem bound_binary {P : Inputs} (h : P.PolyTime) : BinaryFn (bound P) :=
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow.comp ((UnaryFn.const 2).mul (width_unary h))

noncomputable def index (P : Inputs) (u : List Bool) : ℕ := BoundedChoice.search (language P) u (bound P u) - 1
noncomputable def selected (P : Inputs) (u : List Bool) : List Bool := candidate P (pair u (BinaryNatCode.encode (index P u)))

theorem selected_evaluator {P : Inputs} (h : P.PolyTime) : SpaceFunction (selected P) := by
  have E := BoundedChoice.evaluator (decider h) (fun u => BinaryNatCode.encode (bound P u))
    (bound_binary h).bits_mem_FP
  have H := E.withInput.postcompose (candidate P) (candidate_FP h)
  apply H.congr
  funext u
  simp only [selected, index, Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem selected_valid (P : Inputs) (c : List Bool) :
    selected P (pair c (BinaryNatCode.encode (BoundedCriticalSampleChildRegularCount.count P c))) ∈
      BoundedCriticalSampleChildPencilRootCount.language P := by
  have hex := exists_candidate P c
  have hb : bound P (pair c (BinaryNatCode.encode (BoundedCriticalSampleChildRegularCount.count P c))) =
      2 ^ (2 * BoundedCriticalSampleChildRootHash.bitWidth P c) := by simp only [bound, width, pairFst_pair]
  have hex' : ∃ k < bound P (pair c (BinaryNatCode.encode (BoundedCriticalSampleChildRegularCount.count P c))),
      pair (pair c (BinaryNatCode.encode (BoundedCriticalSampleChildRegularCount.count P c))) (BinaryNatCode.encode k) ∈ language P := by
    rw [hb]
    exact hex
  have h := BoundedChoice.witness (language P)
    (pair c (BinaryNatCode.encode (BoundedCriticalSampleChildRegularCount.count P c)))
    (bound P (pair c (BinaryNatCode.encode (BoundedCriticalSampleChildRegularCount.count P c)))) hex'
  exact h.2

noncomputable def prepare (P : Inputs) (c : List Bool) : List Bool :=
  pair c (BinaryNatCode.encode (BoundedCriticalSampleChildRegularCount.count P c))
noncomputable def value (P : Inputs) (c : List Bool) : List Bool := selected P (prepare P c)

theorem evaluator {P : Inputs} (h : P.PolyTime) : SpaceFunction (value P) :=
  ((BoundedCriticalSampleChildRegularCount.evaluator h).withInput).chain (selected_evaluator h)

theorem value_valid (P : Inputs) (c : List Bool) : value P c ∈ BoundedCriticalSampleChildPencilRootCount.language P :=
  selected_valid P c

theorem value_spec (P : Inputs) (c : List Bool) :
    ∃ m : List Bool, ∃ t : ℕ,
      value P c = BoundedCriticalSampleChildWeightedMoments.context c (BoundedCriticalSampleChildRegularCount.count P c) m t ∧
        m.length = BoundedCriticalSampleChildRootHash.bitWidth P c ∧ t < 2 ^ BoundedCriticalSampleChildRootHash.bitWidth P c ∧
        Function.Injective (BoundedCriticalSampleChildRootHash.integerValue P c (Nat.fromBitsLE m + 1) t) := by
  let u := prepare P c
  let q := pair u (BinaryNatCode.encode (index P u))
  let m := modulusWord P q
  let t := Nat.fromBitsLE (parameterWord P q)
  have hc : value P c = BoundedCriticalSampleChildWeightedMoments.context c (BoundedCriticalSampleChildRegularCount.count P c) m t := by
    change candidate P q = _
    have H := candidate_context P u (BinaryNatCode.encode (index P u))
    change candidate P q = BoundedCriticalSampleChildWeightedMoments.context (pairFst u) (Nat.fromBitsLE (pairSnd u)) m t at H
    have ho : pairFst u = c := by simp only [u, prepare, pairFst_pair]
    have hn : Nat.fromBitsLE (pairSnd u) = BoundedCriticalSampleChildRegularCount.count P c := by
      simp only [u, prepare, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rw [ho, hn] at H
    exact H
  have hw : width P (pairFst q) = BoundedCriticalSampleChildRootHash.bitWidth P c := by
    simp only [width, q, u, prepare, pairFst_pair]
  have hm : m.length = BoundedCriticalSampleChildRootHash.bitWidth P c := (modulusWord_length P q).trans hw
  have ht : t < 2 ^ BoundedCriticalSampleChildRootHash.bitWidth P c := by
    have H := Nat.fromBitsLE_lt_pow_length (parameterWord P q)
    rw [parameterWord_length, hw] at H
    exact H
  refine ⟨m, t, hc, hm, ht, ?_⟩
  have H := value_valid P c
  rw [hc, BoundedCriticalSampleChildPencilRootCount.language_packet] at H
  exact H

noncomputable def hash (P : Inputs) (c : List Bool) (x : BoundedCriticalSampleChildRecordSpan.Root P c) : ℤ :=
  BoundedCriticalSampleChildRootHash.integerValue P c
    (Nat.fromBitsLE (BoundedCriticalSampleChildWeightedMoments.modulus (value P c)) + 1)
    (Nat.fromBitsLE (BoundedCriticalSampleChildWeightedMoments.parameter (value P c))) x

theorem hash_injective (P : Inputs) (c : List Bool) : Function.Injective (hash P c) := by
  obtain ⟨m, t, hv, _, _, hi⟩ := value_spec P c
  unfold hash
  rw [hv]
  simpa only [BoundedCriticalSampleChildWeightedMoments.context, BoundedCriticalSampleChildWeightedMoments.modulus,
    BoundedCriticalSampleChildWeightedMoments.parameter, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi

noncomputable def hashBits (P : Inputs) (c : List Bool) : ℕ := BoundedCriticalSampleChildRootHash.valueBits P c + 1
theorem hashBits_unary {P : Inputs} (h : P.PolyTime) : UnaryFn (hashBits P) :=
  (BoundedCriticalSampleChildRootHash.valueBits_unary h).add (UnaryFn.const 1)

theorem hash_bits (P : Inputs) (c : List Bool) (x : BoundedCriticalSampleChildRecordSpan.Root P c) :
    (hash P c x).natAbs.size ≤ hashBits P c := by
  obtain ⟨m, t, hv, hm, _, _⟩ := value_spec P c
  unfold hash
  rw [hv]
  simp only [BoundedCriticalSampleChildWeightedMoments.context, BoundedCriticalSampleChildWeightedMoments.modulus,
    BoundedCriticalSampleChildWeightedMoments.parameter, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hp : Nat.fromBitsLE m + 1 ≤ 2 ^ BoundedCriticalSampleChildRootHash.bitWidth P c := by
    have H := Nat.fromBitsLE_lt_pow_length m
    rw [hm] at H
    omega
  have hn : BoundedCriticalSampleChildRegularCount.count P c ≤ 2 ^ BoundedCriticalSampleChildThom.labelWidth P c :=
    by simpa only [BoundedCriticalSampleChildThom.labelWidth] using BoundedCriticalSampleChildRegularCount.count_le P c
  have hb := (BoundedCriticalSampleChildRootHash.integerValue_bound P c (Nat.succ_pos _) t x).trans (Nat.mul_le_mul hn hp)
  rw [← pow_add] at hb
  have hs := Nat.size_le_size hb
  simpa only [Nat.size_pow, hashBits, BoundedCriticalSampleChildRootHash.valueBits] using hs

noncomputable def descriptor (P : Inputs) (c : List Bool) (x : BoundedCriticalSampleChildRecordSpan.Root P c) : List Bool :=
  SignStatisticBits.integerCode (hash P c x)

theorem descriptor_injective (P : Inputs) (c : List Bool) : Function.Injective (descriptor P c) := by
  intro x y h
  apply hash_injective P c
  have hp := congrArg (fun w => Nat.fromBitsLE (pairFst w)) h
  have hn := congrArg (fun w => Nat.fromBitsLE (pairSnd w)) h
  simp only [descriptor, SignStatisticBits.integerCode, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits] at hp hn
  omega

noncomputable def descriptorWidth (P : Inputs) (c : List Bool) : ℕ := 3 * hashBits P c + 5

theorem descriptorWidth_unary {P : Inputs} (h : P.PolyTime) : UnaryFn (descriptorWidth P) :=
  ((UnaryFn.const 3).mul (hashBits_unary h)).add (UnaryFn.const 5)

theorem descriptor_length_le (P : Inputs) (c : List Bool) (x : BoundedCriticalSampleChildRecordSpan.Root P c) :
    (descriptor P c x).length ≤ descriptorWidth P c :=
  IntegerSmallProductBits.code_length_le _ _ (Nat.size_le.mp (hash_bits P c x)).le

end LeanCanny.Encoding.BoundedCriticalSampleChildHashChoice
