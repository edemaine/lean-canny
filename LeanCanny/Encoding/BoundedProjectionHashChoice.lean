/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionPencilRootCount
public import LeanCanny.Computation.BoundedChoice
public import LeanCanny.Computation.PSPACEClosure

/-! # Native selection of separating projection-root hash parameters

One fixed-width block holds a modulus predecessor and another a parameter.
The native Gram-pencil root counter tests each candidate. Existence of a
bounded prime witness guarantees a successful search, but the test accepts
any modulus producing an injective integer weighted sum. The actual root
count is computed internally before the search; it is not a supplied oracle.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionHashChoice
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open scoped Classical

noncomputable def width (P : Readers) (u : List Bool) : ℕ := BoundedProjectionRootHash.bitWidth P (pairFst u)
theorem width_unary {P : Readers} (h : P.PolyTime) : UnaryFn (width P) :=
  (BoundedProjectionRootHash.bitWidth_unary h).comp pairFst_mem_FP

noncomputable def word (P : Readers) (q : List Bool) : List Bool :=
  ImplicitGraph.word (2 * width P (pairFst q)) (Nat.fromBitsLE (pairSnd q))
theorem word_FP {P : Readers} (h : P.PolyTime) : word P ∈ FP :=
  ImplicitGraph.word_computable (((UnaryFn.const 2).mul (width_unary h)).comp pairFst_mem_FP)
    (BinaryFn.fromBits pairSnd_mem_FP)

noncomputable def modulusWord (P : Readers) (q : List Bool) : List Bool :=
  (word P q).take (width P (pairFst q))
noncomputable def parameterWord (P : Readers) (q : List Bool) : List Bool :=
  ((word P q).drop (width P (pairFst q))).take (width P (pairFst q))
theorem modulusWord_FP {P : Readers} (h : P.PolyTime) : modulusWord P ∈ FP :=
  take_mem_FP (word_FP h) ((width_unary h).comp pairFst_mem_FP)
theorem parameterWord_FP {P : Readers} (h : P.PolyTime) : parameterWord P ∈ FP :=
  take_mem_FP (drop_mem_FP (word_FP h) ((width_unary h).comp pairFst_mem_FP)) ((width_unary h).comp pairFst_mem_FP)

theorem modulusWord_length (P : Readers) (q : List Bool) : (modulusWord P q).length = width P (pairFst q) := by
  simp only [modulusWord, List.length_take, word, ImplicitGraph.length_word]
  omega
theorem parameterWord_length (P : Readers) (q : List Bool) : (parameterWord P q).length = width P (pairFst q) := by
  simp only [parameterWord, List.length_take, List.length_drop, word, ImplicitGraph.length_word]
  omega

noncomputable def candidate (P : Readers) (q : List Bool) : List Bool :=
  pair (pairFst (pairFst q)) (pair (BinaryNat.normalize (pairSnd (pairFst q)))
    (pair (modulusWord P q) (BinaryNat.normalize (parameterWord P q))))
theorem candidate_FP {P : Readers} (h : P.PolyTime) : candidate P ∈ FP := by
  have ho := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hn := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  have ht := mem_FP_comp (parameterWord_FP h) BinaryNat.normalize_mem_FP
  exact mem_FP_pair ho (mem_FP_pair hn (mem_FP_pair (modulusWord_FP h) ht))

theorem candidate_context (P : Readers) (u v : List Bool) : candidate P (pair u v) =
    BoundedProjectionWeightedMoments.context (pairFst u) (Nat.fromBitsLE (pairSnd u))
      (modulusWord P (pair u v)) (Nat.fromBitsLE (parameterWord P (pair u v))) := by
  simp only [candidate, BoundedProjectionWeightedMoments.context, pairFst_pair,
    BinaryNat.normalize_eq_bits, BinaryNatCode.encode]

noncomputable def language (P : Readers) : Language := candidate P ⁻¹' BoundedProjectionPencilRootCount.language P
theorem decider {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (language P) :=
  (BoundedProjectionPencilRootCount.decider h ha).precompose (candidate P) (candidate_FP h)

private theorem word_value (w k : ℕ) (hk : k < 2 ^ w) : Nat.fromBitsLE (ImplicitGraph.word w k) = k := by
  have he := FixedWidthNatVector.decode_block 1 w (fun _ => k) 0 (by decide) hk
  simp only [Nat.zero_mul, List.drop_zero] at he
  change Nat.fromBitsLE ((ImplicitGraph.word w k).take w) = k at he
  simpa only [List.take_of_length_le (ImplicitGraph.length_word w k).le] using he

theorem exists_candidate (P : Readers) (c : List Bool) :
    ∃ k < 2 ^ (2 * BoundedProjectionRootHash.bitWidth P c),
      pair (pair c (BinaryNatCode.encode (BoundedProjectionRootCount.count P c))) (BinaryNatCode.encode k) ∈ language P := by
  obtain ⟨p, t, hp, hs, ht, hi⟩ := BoundedProjectionRootHash.exists_short_labels P c
  let w := BoundedProjectionRootHash.bitWidth P c
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
  let u := pair c (BinaryNatCode.encode (BoundedProjectionRootCount.count P c))
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
  · change candidate P q ∈ BoundedProjectionPencilRootCount.language P
    rw [show q = pair u (BinaryNatCode.encode (Nat.fromBitsLE r)) from rfl, candidate_context]
    simp only [u, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    change BoundedProjectionWeightedMoments.context c (BoundedProjectionRootCount.count P c)
      (modulusWord P q) (Nat.fromBitsLE (parameterWord P q)) ∈ _
    rw [hm, hparam, hbt, BoundedProjectionPencilRootCount.language_packet]
    rw [ham]
    exact BoundedProjectionRootHash.integerValue_injective P c p t hi

noncomputable def bound (P : Readers) (u : List Bool) : ℕ := 2 ^ (2 * width P u)
theorem bound_binary {P : Readers} (h : P.PolyTime) : BinaryFn (bound P) :=
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow.comp ((UnaryFn.const 2).mul (width_unary h))

noncomputable def index (P : Readers) (u : List Bool) : ℕ := BoundedChoice.search (language P) u (bound P u) - 1
noncomputable def selected (P : Readers) (u : List Bool) : List Bool := candidate P (pair u (BinaryNatCode.encode (index P u)))

theorem selected_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (selected P) := by
  have E := BoundedChoice.evaluator (decider h ha) (fun u => BinaryNatCode.encode (bound P u))
    (bound_binary h).bits_mem_FP
  have H := E.withInput.postcompose (candidate P) (candidate_FP h)
  apply H.congr
  funext u
  simp only [selected, index, Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem selected_valid (P : Readers) (c : List Bool) :
    selected P (pair c (BinaryNatCode.encode (BoundedProjectionRootCount.count P c))) ∈
      BoundedProjectionPencilRootCount.language P := by
  have hex := exists_candidate P c
  have hb : bound P (pair c (BinaryNatCode.encode (BoundedProjectionRootCount.count P c))) =
      2 ^ (2 * BoundedProjectionRootHash.bitWidth P c) := by simp only [bound, width, pairFst_pair]
  have hex' : ∃ k < bound P (pair c (BinaryNatCode.encode (BoundedProjectionRootCount.count P c))),
      pair (pair c (BinaryNatCode.encode (BoundedProjectionRootCount.count P c))) (BinaryNatCode.encode k) ∈ language P := by
    rw [hb]
    exact hex
  have h := BoundedChoice.witness (language P)
    (pair c (BinaryNatCode.encode (BoundedProjectionRootCount.count P c)))
    (bound P (pair c (BinaryNatCode.encode (BoundedProjectionRootCount.count P c)))) hex'
  exact h.2

noncomputable def prepare (P : Readers) (c : List Bool) : List Bool :=
  pair c (BinaryNatCode.encode (BoundedProjectionRootCount.count P c))
noncomputable def value (P : Readers) (c : List Bool) : List Bool := selected P (prepare P c)

theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P) :=
  ((BoundedProjectionRootCount.evaluator h ha).withInput).chain (selected_evaluator h ha)

theorem value_valid (P : Readers) (c : List Bool) : value P c ∈ BoundedProjectionPencilRootCount.language P :=
  selected_valid P c

theorem value_spec (P : Readers) (c : List Bool) :
    ∃ m : List Bool, ∃ t : ℕ,
      value P c = BoundedProjectionWeightedMoments.context c (BoundedProjectionRootCount.count P c) m t ∧
        m.length = BoundedProjectionRootHash.bitWidth P c ∧ t < 2 ^ BoundedProjectionRootHash.bitWidth P c ∧
        Function.Injective (BoundedProjectionRootHash.integerValue P c (Nat.fromBitsLE m + 1) t) := by
  let u := prepare P c
  let q := pair u (BinaryNatCode.encode (index P u))
  let m := modulusWord P q
  let t := Nat.fromBitsLE (parameterWord P q)
  have hc : value P c = BoundedProjectionWeightedMoments.context c (BoundedProjectionRootCount.count P c) m t := by
    change candidate P q = _
    have H := candidate_context P u (BinaryNatCode.encode (index P u))
    change candidate P q = BoundedProjectionWeightedMoments.context (pairFst u) (Nat.fromBitsLE (pairSnd u)) m t at H
    have ho : pairFst u = c := by simp only [u, prepare, pairFst_pair]
    have hn : Nat.fromBitsLE (pairSnd u) = BoundedProjectionRootCount.count P c := by
      simp only [u, prepare, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rw [ho, hn] at H
    exact H
  have hw : width P (pairFst q) = BoundedProjectionRootHash.bitWidth P c := by
    simp only [width, q, u, prepare, pairFst_pair]
  have hm : m.length = BoundedProjectionRootHash.bitWidth P c := (modulusWord_length P q).trans hw
  have ht : t < 2 ^ BoundedProjectionRootHash.bitWidth P c := by
    have H := Nat.fromBitsLE_lt_pow_length (parameterWord P q)
    rw [parameterWord_length, hw] at H
    exact H
  refine ⟨m, t, hc, hm, ht, ?_⟩
  have H := value_valid P c
  rw [hc, BoundedProjectionPencilRootCount.language_packet] at H
  exact H

noncomputable def hash (P : Readers) (c : List Bool) (x : BoundedProjectionRecordSpan.Root P c) : ℤ :=
  BoundedProjectionRootHash.integerValue P c
    (Nat.fromBitsLE (BoundedProjectionWeightedMoments.modulus (value P c)) + 1)
    (Nat.fromBitsLE (BoundedProjectionWeightedMoments.parameter (value P c))) x

theorem hash_injective (P : Readers) (c : List Bool) : Function.Injective (hash P c) := by
  obtain ⟨m, t, hv, _, _, hi⟩ := value_spec P c
  unfold hash
  rw [hv]
  simpa only [BoundedProjectionWeightedMoments.context, BoundedProjectionWeightedMoments.modulus,
    BoundedProjectionWeightedMoments.parameter, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi

noncomputable def hashBits (P : Readers) (c : List Bool) : ℕ := BoundedProjectionRootHash.valueBits P c + 1
theorem hashBits_unary {P : Readers} (h : P.PolyTime) : UnaryFn (hashBits P) :=
  (BoundedProjectionRootHash.valueBits_unary h).add (UnaryFn.const 1)

theorem hash_bits (P : Readers) (c : List Bool) (x : BoundedProjectionRecordSpan.Root P c) :
    (hash P c x).natAbs.size ≤ hashBits P c := by
  obtain ⟨m, t, hv, hm, _, _⟩ := value_spec P c
  unfold hash
  rw [hv]
  simp only [BoundedProjectionWeightedMoments.context, BoundedProjectionWeightedMoments.modulus,
    BoundedProjectionWeightedMoments.parameter, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hp : Nat.fromBitsLE m + 1 ≤ 2 ^ BoundedProjectionRootHash.bitWidth P c := by
    have H := Nat.fromBitsLE_lt_pow_length m
    rw [hm] at H
    omega
  have hn : BoundedProjectionRootCount.count P c ≤ 2 ^ BoundedCriticalProjection.labelWidth P c :=
    BoundedCriticalLabels.rootSet_card_le P c
  have hb := (BoundedProjectionRootHash.integerValue_bound P c (Nat.succ_pos _) t x).trans (Nat.mul_le_mul hn hp)
  rw [← pow_add] at hb
  have hs := Nat.size_le_size hb
  simpa only [Nat.size_pow, hashBits, BoundedProjectionRootHash.valueBits] using hs

end LeanCanny.Encoding.BoundedProjectionHashChoice
