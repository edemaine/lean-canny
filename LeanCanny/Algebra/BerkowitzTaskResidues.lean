/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzTaskRouting

/-! # Reply lengths depend only on the original modulus

The factor's modular negation reduces arbitrary input words. Thus every
internal reply has the modulus bit bound, independently of source reply
canonicality. A source entry bound extends it to the whole task dispatcher.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
open LeanCanny.Encoding LeanCanny.Computation MatrixPower

private theorem negate_length_le (m : ℕ) (hm : m ≠ 0) (x : List Bool) :
    (ArithmeticBits.negate (pair (BinaryNatCode.encode m) x)).length ≤ m.size := by
  rw [ArithmeticBits.negate_pair]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.size_eq_bits_len]
  exact Nat.size_le_size (Nat.mod_lt _ (Nat.pos_of_ne_zero hm)).le

theorem determinant_value_length_le (F : ModularFamily) (c : List Bool) :
    (F.value c).length ≤ (F.modulus c).size := by
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  exact residueBits_length_le _ _

theorem moment_value_length_le (F : ModularFamily) (p : List Bool) :
    ((momentFamily F).value p).length ≤ (F.modulus (pairFst (pairFst p))).size := by
  let : NeZero ((momentFamily F).modulus p) := ⟨(momentFamily F).modulus_ne_zero p⟩
  exact residueBits_length_le _ _

theorem factor_value_length_le {F : ModularFamily} (a : ModularAccess F) (p : List Bool) :
    (ModularAccess.factorValue a p).length ≤ (F.modulus (pairFst (pairFst p))).size := by
  have hn (x : List Bool) : (ModularAccess.negative a (pair p x)).length ≤
      (F.modulus (pairFst (pairFst p))).size := by
    simp only [ModularAccess.negative, pairFst_pair, pairSnd_pair, a.modulus_eq]
    exact negate_length_le _ (F.modulus_ne_zero _) x
  unfold ModularAccess.factorValue
  split_ifs
  · rw [ModularAccess.oneCoefficient_correct]
    let : NeZero (F.modulus (pairFst (pairFst p))) := ⟨F.modulus_ne_zero _⟩
    exact residueBits_length_le _ _
  · exact hn _
  · exact hn _
  · exact Nat.zero_le _

theorem answer_length_le {F : ModularFamily} (a : ModularAccess F)
    (hentry : ∀ p, (a.entry p).length ≤ (F.modulus (pairFst p)).size) (q : List Bool) :
    (answer a q).length ≤ (F.modulus (origin q)).size := by
  simp only [answer, origin]
  split_ifs
  · exact Nat.zero_le _
  · exact determinant_value_length_le F _
  · exact factor_value_length_le a _
  · exact moment_value_length_le F _
  · exact hentry _

end LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
