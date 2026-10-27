/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberPencilRootCount
public import LeanCanny.Computation.BoundedChoice
public import LeanCanny.Computation.PSPACEClosure

/-! # Native selection of separating fiber-root hash parameters

One fixed-width block holds a modulus predecessor and another a parameter.
The native Gram-pencil root counter tests each candidate. Existence of a
bounded prime witness guarantees a successful search, but the test accepts
any modulus producing an injective integer weighted sum. The actual root
count is computed internally before the search; it is not a supplied oracle.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberHashChoice
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open scoped Classical

noncomputable def width (F : BoundedAlgebraicSlice.Family) (u : List Bool) : ℕ := BoundedCriticalSampleFiberRootHash.bitWidth F (pairFst u)
theorem width_unary {F : BoundedAlgebraicSlice.Family} (A : F.Access) : UnaryFn (width F) :=
  (BoundedCriticalSampleFiberRootHash.bitWidth_unary A).comp pairFst_mem_FP

noncomputable def word (F : BoundedAlgebraicSlice.Family) (q : List Bool) : List Bool :=
  ImplicitGraph.word (2 * width F (pairFst q)) (Nat.fromBitsLE (pairSnd q))
theorem word_FP {F : BoundedAlgebraicSlice.Family} (A : F.Access) : word F ∈ FP :=
  ImplicitGraph.word_computable (((UnaryFn.const 2).mul (width_unary A)).comp pairFst_mem_FP)
    (BinaryFn.fromBits pairSnd_mem_FP)

noncomputable def modulusWord (F : BoundedAlgebraicSlice.Family) (q : List Bool) : List Bool :=
  (word F q).take (width F (pairFst q))
noncomputable def parameterWord (F : BoundedAlgebraicSlice.Family) (q : List Bool) : List Bool :=
  ((word F q).drop (width F (pairFst q))).take (width F (pairFst q))
theorem modulusWord_FP {F : BoundedAlgebraicSlice.Family} (A : F.Access) : modulusWord F ∈ FP :=
  take_mem_FP (word_FP A) ((width_unary A).comp pairFst_mem_FP)
theorem parameterWord_FP {F : BoundedAlgebraicSlice.Family} (A : F.Access) : parameterWord F ∈ FP :=
  take_mem_FP (drop_mem_FP (word_FP A) ((width_unary A).comp pairFst_mem_FP)) ((width_unary A).comp pairFst_mem_FP)

theorem modulusWord_length (F : BoundedAlgebraicSlice.Family) (q : List Bool) : (modulusWord F q).length = width F (pairFst q) := by
  simp only [modulusWord, List.length_take, word, ImplicitGraph.length_word]
  omega
theorem parameterWord_length (F : BoundedAlgebraicSlice.Family) (q : List Bool) : (parameterWord F q).length = width F (pairFst q) := by
  simp only [parameterWord, List.length_take, List.length_drop, word, ImplicitGraph.length_word]
  omega

noncomputable def candidate (F : BoundedAlgebraicSlice.Family) (q : List Bool) : List Bool :=
  pair (pairFst (pairFst q)) (pair (BinaryNat.normalize (pairSnd (pairFst q)))
    (pair (modulusWord F q) (BinaryNat.normalize (parameterWord F q))))
theorem candidate_FP {F : BoundedAlgebraicSlice.Family} (A : F.Access) : candidate F ∈ FP := by
  have ho := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hn := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  have ht := mem_FP_comp (parameterWord_FP A) BinaryNat.normalize_mem_FP
  exact mem_FP_pair ho (mem_FP_pair hn (mem_FP_pair (modulusWord_FP A) ht))

theorem candidate_context (F : BoundedAlgebraicSlice.Family) (u v : List Bool) : candidate F (pair u v) =
    BoundedCriticalSampleFiberWeightedMoments.context (pairFst u) (Nat.fromBitsLE (pairSnd u))
      (modulusWord F (pair u v)) (Nat.fromBitsLE (parameterWord F (pair u v))) := by
  simp only [candidate, BoundedCriticalSampleFiberWeightedMoments.context, pairFst_pair,
    BinaryNat.normalize_eq_bits, BinaryNatCode.encode]

noncomputable def language (P : Readers) (F : BoundedAlgebraicSlice.Family) : Language := candidate F ⁻¹' BoundedCriticalSampleFiberPencilRootCount.language P F
theorem decider {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (language P F) :=
  (BoundedCriticalSampleFiberPencilRootCount.decider h A ha).precompose (candidate F) (candidate_FP A)

private theorem word_value (w k : ℕ) (hk : k < 2 ^ w) : Nat.fromBitsLE (ImplicitGraph.word w k) = k := by
  have he := FixedWidthNatVector.decode_block 1 w (fun _ => k) 0 (by decide) hk
  simp only [Nat.zero_mul, List.drop_zero] at he
  change Nat.fromBitsLE ((ImplicitGraph.word w k).take w) = k at he
  simpa only [List.take_of_length_le (ImplicitGraph.length_word w k).le] using he

theorem exists_candidate (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) :
    ∃ k < 2 ^ (2 * BoundedCriticalSampleFiberRootHash.bitWidth F c),
      pair (pair c (BinaryNatCode.encode (BoundedCriticalSampleSlice.RootCount.count P F c))) (BinaryNatCode.encode k) ∈ language P F := by
  obtain ⟨p, t, hp, hs, ht, hi⟩ := BoundedCriticalSampleFiberRootHash.exists_short_labels P F c
  let w := BoundedCriticalSampleFiberRootHash.bitWidth F c
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
  let u := pair c (BinaryNatCode.encode (BoundedCriticalSampleSlice.RootCount.count P F c))
  let q := pair u (BinaryNatCode.encode (Nat.fromBitsLE r))
  have hw : width F (pairFst q) = w := by simp only [width, q, u, pairFst_pair]; rfl
  have hword : word F q = r := by
    simp only [word, width, q, u, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rw [← hr, ImplicitGraph.word_fromBitsLE]
  have hm : modulusWord F q = a := by
    rw [modulusWord, hword, hw]
    change (a ++ b).take w = a
    rw [← ha, List.take_left]
  have hparam : parameterWord F q = b := by
    rw [parameterWord, hword, hw]
    change ((a ++ b).drop w).take w = b
    rw [← ha, List.drop_left, ha, ← hb, List.take_length]
  refine ⟨Nat.fromBitsLE r, ?_, ?_⟩
  · simpa only [hr] using Nat.fromBitsLE_lt_pow_length r
  · change candidate F q ∈ BoundedCriticalSampleFiberPencilRootCount.language P F
    rw [show q = pair u (BinaryNatCode.encode (Nat.fromBitsLE r)) from rfl, candidate_context]
    simp only [u, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    change BoundedCriticalSampleFiberWeightedMoments.context c (BoundedCriticalSampleSlice.RootCount.count P F c)
      (modulusWord F q) (Nat.fromBitsLE (parameterWord F q)) ∈ _
    rw [hm, hparam, hbt, BoundedCriticalSampleFiberPencilRootCount.language_packet]
    rw [ham]
    exact BoundedCriticalSampleFiberRootHash.integerValue_injective P F c p t hi

noncomputable def bound (F : BoundedAlgebraicSlice.Family) (u : List Bool) : ℕ := 2 ^ (2 * width F u)
theorem bound_binary {F : BoundedAlgebraicSlice.Family} (A : F.Access) : BinaryFn (bound F) :=
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow.comp ((UnaryFn.const 2).mul (width_unary A))

noncomputable def index (P : Readers) (F : BoundedAlgebraicSlice.Family) (u : List Bool) : ℕ := BoundedChoice.search (language P F) u (bound F u) - 1
noncomputable def selected (P : Readers) (F : BoundedAlgebraicSlice.Family) (u : List Bool) : List Bool := candidate F (pair u (BinaryNatCode.encode (index P F u)))

theorem selected_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (selected P F) := by
  have E := BoundedChoice.evaluator (decider h A ha) (fun u => BinaryNatCode.encode (bound F u))
    (bound_binary A).bits_mem_FP
  have H := E.withInput.postcompose (candidate F) (candidate_FP A)
  apply H.congr
  funext u
  simp only [selected, index, Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem selected_valid (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) :
    selected P F (pair c (BinaryNatCode.encode (BoundedCriticalSampleSlice.RootCount.count P F c))) ∈
      BoundedCriticalSampleFiberPencilRootCount.language P F := by
  have hex := exists_candidate P F c
  have hb : bound F (pair c (BinaryNatCode.encode (BoundedCriticalSampleSlice.RootCount.count P F c))) =
      2 ^ (2 * BoundedCriticalSampleFiberRootHash.bitWidth F c) := by simp only [bound, width, pairFst_pair]
  have hex' : ∃ k < bound F (pair c (BinaryNatCode.encode (BoundedCriticalSampleSlice.RootCount.count P F c))),
      pair (pair c (BinaryNatCode.encode (BoundedCriticalSampleSlice.RootCount.count P F c))) (BinaryNatCode.encode k) ∈ language P F := by
    rw [hb]
    exact hex
  have h := BoundedChoice.witness (language P F)
    (pair c (BinaryNatCode.encode (BoundedCriticalSampleSlice.RootCount.count P F c)))
    (bound F (pair c (BinaryNatCode.encode (BoundedCriticalSampleSlice.RootCount.count P F c)))) hex'
  exact h.2

noncomputable def prepare (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) : List Bool :=
  pair c (BinaryNatCode.encode (BoundedCriticalSampleSlice.RootCount.count P F c))
noncomputable def value (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) : List Bool := selected P F (prepare P F c)

theorem evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P F) :=
  ((BoundedCriticalSampleSlice.RootCount.count_evaluator h A ha).withInput).chain (selected_evaluator h A ha)

theorem value_valid (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) : value P F c ∈ BoundedCriticalSampleFiberPencilRootCount.language P F :=
  selected_valid P F c

theorem value_spec (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) :
    ∃ m : List Bool, ∃ t : ℕ,
      value P F c = BoundedCriticalSampleFiberWeightedMoments.context c (BoundedCriticalSampleSlice.RootCount.count P F c) m t ∧
        m.length = BoundedCriticalSampleFiberRootHash.bitWidth F c ∧ t < 2 ^ BoundedCriticalSampleFiberRootHash.bitWidth F c ∧
        Function.Injective (BoundedCriticalSampleFiberRootHash.integerValue P F c (Nat.fromBitsLE m + 1) t) := by
  let u := prepare P F c
  let q := pair u (BinaryNatCode.encode (index P F u))
  let m := modulusWord F q
  let t := Nat.fromBitsLE (parameterWord F q)
  have hc : value P F c = BoundedCriticalSampleFiberWeightedMoments.context c (BoundedCriticalSampleSlice.RootCount.count P F c) m t := by
    change candidate F q = _
    have H := candidate_context F u (BinaryNatCode.encode (index P F u))
    change candidate F q = BoundedCriticalSampleFiberWeightedMoments.context (pairFst u) (Nat.fromBitsLE (pairSnd u)) m t at H
    have ho : pairFst u = c := by simp only [u, prepare, pairFst_pair]
    have hn : Nat.fromBitsLE (pairSnd u) = BoundedCriticalSampleSlice.RootCount.count P F c := by
      simp only [u, prepare, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rw [ho, hn] at H
    exact H
  have hw : width F (pairFst q) = BoundedCriticalSampleFiberRootHash.bitWidth F c := by
    simp only [width, q, u, prepare, pairFst_pair]
  have hm : m.length = BoundedCriticalSampleFiberRootHash.bitWidth F c := (modulusWord_length F q).trans hw
  have ht : t < 2 ^ BoundedCriticalSampleFiberRootHash.bitWidth F c := by
    have H := Nat.fromBitsLE_lt_pow_length (parameterWord F q)
    rw [parameterWord_length, hw] at H
    exact H
  refine ⟨m, t, hc, hm, ht, ?_⟩
  have H := value_valid P F c
  rw [hc, BoundedCriticalSampleFiberPencilRootCount.language_packet] at H
  exact H

noncomputable def hash (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (x : BoundedCriticalSampleFiberRecordSpan.Root P F c) : ℤ :=
  BoundedCriticalSampleFiberRootHash.integerValue P F c
    (Nat.fromBitsLE (BoundedCriticalSampleFiberWeightedMoments.modulus (value P F c)) + 1)
    (Nat.fromBitsLE (BoundedCriticalSampleFiberWeightedMoments.parameter (value P F c))) x

theorem hash_injective (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) : Function.Injective (hash P F c) := by
  obtain ⟨m, t, hv, _, _, hi⟩ := value_spec P F c
  unfold hash
  rw [hv]
  simpa only [BoundedCriticalSampleFiberWeightedMoments.context, BoundedCriticalSampleFiberWeightedMoments.modulus,
    BoundedCriticalSampleFiberWeightedMoments.parameter, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi

noncomputable def hashBits (F : BoundedAlgebraicSlice.Family) (c : List Bool) : ℕ := BoundedCriticalSampleFiberRootHash.valueBits F c + 1
theorem hashBits_unary {F : BoundedAlgebraicSlice.Family} (A : F.Access) : UnaryFn (hashBits F) :=
  (BoundedCriticalSampleFiberRootHash.valueBits_unary A).add (UnaryFn.const 1)

theorem hash_bits (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (x : BoundedCriticalSampleFiberRecordSpan.Root P F c) :
    (hash P F c x).natAbs.size ≤ hashBits F c := by
  obtain ⟨m, t, hv, hm, _, _⟩ := value_spec P F c
  unfold hash
  rw [hv]
  simp only [BoundedCriticalSampleFiberWeightedMoments.context, BoundedCriticalSampleFiberWeightedMoments.modulus,
    BoundedCriticalSampleFiberWeightedMoments.parameter, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hp : Nat.fromBitsLE m + 1 ≤ 2 ^ BoundedCriticalSampleFiberRootHash.bitWidth F c := by
    have H := Nat.fromBitsLE_lt_pow_length m
    rw [hm] at H
    omega
  have hn : BoundedCriticalSampleSlice.RootCount.count P F c ≤ 2 ^ (F.degree (BoundedCriticalSampleSlice.context c)).size :=
    (BoundedCriticalSampleFiberRoot.count_le_degree P F c).trans (Nat.lt_size_self _).le
  have hb := (BoundedCriticalSampleFiberRootHash.integerValue_bound P F c (Nat.succ_pos _) t x).trans (Nat.mul_le_mul hn hp)
  rw [← pow_add] at hb
  have hs := Nat.size_le_size hb
  simpa only [Nat.size_pow, hashBits, BoundedCriticalSampleFiberRootHash.valueBits] using hs

end LeanCanny.Encoding.BoundedCriticalSampleFiberHashChoice
