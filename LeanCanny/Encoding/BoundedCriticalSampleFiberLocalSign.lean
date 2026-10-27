/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberTestDerivatives
public import LeanCanny.Algebra.PolynomialLocalSignSpace

/-! # Native one-sided signs at ordered algebraic-fiber roots

The scan retains only the first nonzero derivative sign. Odd orders reverse
their signs for the left side. The binary degree control permits exponentially
many derivatives; neither a signature nor a nearby rational point is stored.
The correctness theorems give actual one-sided neighborhoods at every valid
root, without requiring simplicity of either the root or the test polynomial.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberLocalSign
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice (Family)
open BoundedCriticalSampleSlice
open scoped Classical

def parityTag (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd q) % 2 = 0 then [false, true] else [true]
theorem parityTag_FP : parityTag ∈ FP :=
  (((BinaryFn.fromBits pairSnd_mem_FP).mod (BinaryFn.const 2)).eq (BinaryFn.const 0)).ite_mem_FP
    (constFn_mem_FP _) (constFn_mem_FP _)

theorem parityTag_packet (q : List Bool) (k : ℕ) :
    parityTag (pair q (BinaryNatCode.encode k)) = InfinitesimalSign.encode (SignType.sign ((-1 : ℝ) ^ k)) := by
  simp only [parityTag, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    neg_one_pow_eq_ite, Nat.even_iff]
  split_ifs <;> simp only [sign_one, Left.sign_neg, InfinitesimalSign.encode]

noncomputable def leftRead (P : Readers) (F G : Family) (q : List Bool) : List Bool :=
  BoundedCriticalSampleFiberSignatureRead.multiplyTags
    (pair (parityTag q) (BoundedCriticalSampleFiberTestDerivatives.value P F G q))

theorem leftRead_evaluator {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (leftRead P F G) :=
  ((SpaceFunction.ofFP parityTag parityTag_FP).pairOutputs (BoundedCriticalSampleFiberTestDerivatives.evaluator h A B ha)).postcompose
    BoundedCriticalSampleFiberSignatureRead.multiplyTags BoundedCriticalSampleFiberSignatureRead.multiplyTags_FP

theorem leftRead_length (P : Readers) (F G : Family) (q : List Bool) : (leftRead P F G q).length ≤ 2 := by
  unfold leftRead BoundedCriticalSampleFiberSignatureRead.multiplyTags
  split_ifs <;> decide

theorem leftRead_packet (P : Readers) (F G : Family) (u : List Bool) (r : Fin (RootCount.count P F u)) (k : ℕ) :
    leftRead P F G (pair (pair u (BinaryNatCode.encode r.val)) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign ((-1 : ℝ) ^ k *
        ((Polynomial.derivative^[k]) (specialized P G u)).eval (BoundedCriticalSampleFiberRoot.root P F u r).val)) := by
  rw [leftRead, parityTag_packet, BoundedCriticalSampleFiberTestDerivatives.packet,
    BoundedCriticalSampleFiberSignatureRead.multiplyTags_packet, sign_mul]

noncomputable def count (G : Family) (q : List Bool) : List Bool :=
  BinaryNatCode.encode (G.degree (BoundedCriticalSampleSlice.context (pairFst q)) + 1)
theorem count_FP {G : Family} (B : G.Access) : count G ∈ FP := by
  have hd : BinaryFn (fun q => G.degree (BoundedCriticalSampleSlice.context (pairFst q))) :=
    B.degree_binary.comp (mem_FP_comp pairFst_mem_FP BoundedCriticalSampleSlice.context_FP)
  exact (hd.add (BinaryFn.const 1)).bits_mem_FP

/-- `fromLeft = true` selects the left side; `false` selects the right side. -/
noncomputable def value (P : Readers) (F G : Family) (fromLeft : Bool) : List Bool → List Bool :=
  PolynomialLocalSignBits.value
    (if fromLeft then leftRead P F G else BoundedCriticalSampleFiberTestDerivatives.value P F G) (count G)

attribute [local irreducible] leftRead BoundedCriticalSampleFiberTestDerivatives.value

theorem evaluator {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (fromLeft : Bool) :
    SpaceFunction (value P F G fromLeft) := by
  cases fromLeft with
  | false =>
    have E := PolynomialLocalSignBits.evaluator (BoundedCriticalSampleFiberTestDerivatives.evaluator h A B ha)
      (count_FP B) (BoundedCriticalSampleFiberTestDerivatives.value_length P F G)
    exact E
  | true =>
    have E := PolynomialLocalSignBits.evaluator (leftRead_evaluator h A B ha) (count_FP B) (leftRead_length P F G)
    exact E

theorem right_packet (P : Readers) (F G : Family) (u : List Bool) (r : Fin (RootCount.count P F u)) :
    value P F G false (pair u (BinaryNatCode.encode r.val)) =
      InfinitesimalSign.encode (PolynomialLocalSign.right (specialized P G u) (BoundedCriticalSampleFiberRoot.root P F u r).val) := by
  change PolynomialLocalSignBits.value (BoundedCriticalSampleFiberTestDerivatives.value P F G) (count G)
    (pair u (BinaryNatCode.encode r.val)) = _
  rw [PolynomialLocalSignBits.packet _ _ _
    (fun k => (SignType.sign (((Polynomial.derivative^[k]) (specialized P G u)).eval
      (BoundedCriticalSampleFiberRoot.root P F u r).val) : ℤ))
    (fun k => by rw [BoundedCriticalSampleFiberTestDerivatives.packet, PolynomialLocalSign.tag_cast])]
  simp only [count, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact PolynomialLocalSign.scan_right _ _ _ ((specialized_degree P G u).trans_lt (Nat.lt_succ_self _))

theorem left_packet (P : Readers) (F G : Family) (u : List Bool) (r : Fin (RootCount.count P F u)) :
    value P F G true (pair u (BinaryNatCode.encode r.val)) =
      InfinitesimalSign.encode (PolynomialLocalSign.left (specialized P G u) (BoundedCriticalSampleFiberRoot.root P F u r).val) := by
  change PolynomialLocalSignBits.value (leftRead P F G) (count G) (pair u (BinaryNatCode.encode r.val)) = _
  rw [PolynomialLocalSignBits.packet _ _ _
    (fun k => (SignType.sign ((-1 : ℝ) ^ k * ((Polynomial.derivative^[k]) (specialized P G u)).eval
      (BoundedCriticalSampleFiberRoot.root P F u r).val) : ℤ))
    (fun k => by rw [leftRead_packet, PolynomialLocalSign.tag_cast])]
  simp only [count, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact PolynomialLocalSign.scan_left _ _ _ ((specialized_degree P G u).trans_lt (Nat.lt_succ_self _))

theorem right_eventually (P : Readers) (F G : Family) (u : List Bool) (r : Fin (RootCount.count P F u)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ →
      value P F G false (pair u (BinaryNatCode.encode r.val)) = InfinitesimalSign.encode
        (SignType.sign ((specialized P G u).eval ((BoundedCriticalSampleFiberRoot.root P F u r).val + t))) := by
  obtain ⟨δ, hδ, H⟩ := PolynomialLocalSign.right_eventually (specialized P G u) (BoundedCriticalSampleFiberRoot.root P F u r).val
  exact ⟨δ, hδ, fun t ht htd => by rw [right_packet, H t ht htd]⟩

theorem left_eventually (P : Readers) (F G : Family) (u : List Bool) (r : Fin (RootCount.count P F u)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ →
      value P F G true (pair u (BinaryNatCode.encode r.val)) = InfinitesimalSign.encode
        (SignType.sign ((specialized P G u).eval ((BoundedCriticalSampleFiberRoot.root P F u r).val - t))) := by
  obtain ⟨δ, hδ, H⟩ := PolynomialLocalSign.left_eventually (specialized P G u) (BoundedCriticalSampleFiberRoot.root P F u r).val
  exact ⟨δ, hδ, fun t ht htd => by rw [left_packet, H t ht htd]⟩

end LeanCanny.Encoding.BoundedCriticalSampleFiberLocalSign
