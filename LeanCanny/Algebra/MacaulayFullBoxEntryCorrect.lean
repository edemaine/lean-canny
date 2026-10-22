/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayFullBoxEntrySpace

/-! # Correctness of the native full-box block entry reader -/

@[expose] public section
namespace LeanCanny.Algebra.MacaulayFullBoxBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

abbrev Coefficient := Polynomial (Polynomial ℤ)
noncomputable def scalar (modulus : List Bool → List Bool) (c : List Bool) (u v : ℕ)
    (p : Coefficient) : List Bool :=
  residueBits (((p.coeff v).coeff u : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))

lemma scalar_zero (modulus : List Bool → List Bool) (c : List Bool) (u v : ℕ) :
    scalar modulus c u v 0 = [] := by simp [scalar, residueBits, BinaryNatCode.encode]

def entryPacket (c : List Bool) (a b u v : ℕ) :=
  pair c (pair (BinaryNatCode.encode a) (pair (BinaryNatCode.encode b)
    (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))

@[simp] lemma ctx_entryPacket (c : List Bool) (a b u v : ℕ) : ctx (entryPacket c a b u v) = c := by
  simp only [ctx, entryPacket, pairFst_pair]
@[simp] lemma idx_entryPacket (c : List Bool) (a b u v : ℕ) : idx (entryPacket c a b u v) = BinaryNatCode.encode a := by
  simp only [idx, entryPacket, pairFst_pair, pairSnd_pair]
@[simp] lemma shift_entryPacket (c : List Bool) (a b u v : ℕ) : shift (entryPacket c a b u v) = BinaryNatCode.encode b := by
  simp only [shift, entryPacket, pairFst_pair, pairSnd_pair]
@[simp] lemma uv_entryPacket (c : List Bool) (a b u v : ℕ) :
    uv (entryPacket c a b u v) = pair (BinaryNatCode.encode u) (BinaryNatCode.encode v) := by
  simp only [uv, entryPacket, pairSnd_pair]

lemma top_packet (L : Layout) (c : List Bool) (a b u v : ℕ) :
    top L (entryPacket c a b u v) ↔ a < (L.arity c + 1) * FixedWidthPolynomial.count (L.arity c) (L.width c) := by
  simp only [top, ctx_entryPacket, idx_entryPacket, rowCut_eq, MacaulayBits.fromBits_encode]
lemma left_packet (L : Layout) (c : List Bool) (a b u v : ℕ) :
    left L (entryPacket c a b u v) ↔ b < (L.arity c + 1) * FixedWidthPolynomial.count (L.arity c) (L.width c) := by
  simp only [left, ctx_entryPacket, shift_entryPacket, rowCut_eq, MacaulayBits.fromBits_encode]
lemma diagonal_packet (c : List Bool) (a b u v : ℕ) : diagonal (entryPacket c a b u v) ↔ a = b := by
  simp only [diagonal, idx_entryPacket, shift_entryPacket, MacaulayBits.fromBits_encode]

lemma upperInput_packet (L : Layout) (c : List Bool) (a b u v : ℕ) :
    upperInput L (entryPacket c a ((L.arity c + 1) * FixedWidthPolynomial.count (L.arity c) (L.width c) + b) u v) =
      entryPacket c a b u v := by
  simp only [upperInput, ctx_entryPacket, idx_entryPacket, shift_entryPacket, uv_entryPacket,
    rowCut_eq, BinaryNat.sub_pair, MacaulayBits.fromBits_encode, Nat.add_sub_cancel_left]
  rfl
lemma lowerInput_packet (L : Layout) (c : List Bool) (a b u v : ℕ) :
    lowerInput L (entryPacket c ((L.arity c + 1) * FixedWidthPolynomial.count (L.arity c) (L.width c) + a) b u v) =
      entryPacket c b a u v := by
  simp only [lowerInput, ctx_entryPacket, idx_entryPacket, shift_entryPacket, uv_entryPacket,
    rowCut_eq, BinaryNat.sub_pair, MacaulayBits.fromBits_encode, Nat.add_sub_cancel_left]
  rfl

lemma unit_packet (modulus : List Bool → List Bool) (c : List Bool) (a b u v : ℕ) :
    unit modulus (entryPacket c a b u v) = scalar modulus c u v 1 := by
  simp only [unit, entryPacket, uv, ctx, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode]
  rw [BinaryNat.succ_eq_bits]
  by_cases hu : u = 0 <;> by_cases hv : v = 0
  · subst u; subst v
    simpa only [and_self, ite_true, scalar, Polynomial.coeff_one_zero, Int.cast_one, BinaryNatCode.encode] using
      ArithmeticBits.one_residueBits (Nat.fromBitsLE (modulus c) + 1)
  all_goals simp [hu, hv, scalar, Polynomial.coeff_one, residueBits, BinaryNatCode.encode]

lemma rawSourceInput_packet (L : Layout) (c : List Bool) (i a b u v : ℕ)
    (ha : a < FixedWidthPolynomial.count (L.arity c) (L.width c)) :
    rawSourceInput L (entryPacket c (i * FixedWidthPolynomial.count (L.arity c) (L.width c) + a) b u v) =
      packet c i a b u v := by
  have hC : 0 < FixedWidthPolynomial.count (L.arity c) (L.width c) := by
    unfold FixedWidthPolynomial.count
    positivity
  simp only [rawSourceInput, entryPacket, ctx, idx, shift, uv, pairFst_pair, pairSnd_pair,
    columnsCode_eq, BinaryNat.divMod_pair, MacaulayBits.fromBits_encode]
  rw [Nat.mul_comm i (FixedWidthPolynomial.count (L.arity c) (L.width c)), Nat.mul_add_div hC, Nat.div_eq_of_lt ha, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt ha]
  rfl

lemma rawPaddingInput_packet (L : Layout) (c : List Bool) (a b u v : ℕ) :
    rawPaddingInput L (entryPacket c (L.arity c * FixedWidthPolynomial.count (L.arity c) (L.width c) + a) b u v) =
      packet c 0 a b u v := by
  simp only [rawPaddingInput, entryPacket, ctx, idx, shift, uv, pairFst_pair, pairSnd_pair,
    sourceCut_eq, BinaryNat.sub_pair, MacaulayBits.fromBits_encode, Nat.add_sub_cancel_left]
  rfl

lemma total_packet_iff (L : Layout) (c : List Bool) (i u v : ℕ)
    (a b : Macaulay.Index (L.arity c) (L.width c)) :
    total L (packet c i a.val b.val u v) = L.level c ↔
      (FixedWidthPolynomial.vector _ _ a).degree = L.level c := by
  simp only [total, ctx_packet]
  rw [MacaulayBits.sum_min_eq_iff, Finset.sum_range]
  simp only [shiftAt_packet, Finsupp.degree_eq_sum]

variable (L : Layout) (modulus coefficient : List Bool → List Bool) (c : List Bool)
variable (p : Fin (L.arity c) → MvPolynomial (Fin (L.arity c)) Coefficient)
variable (hlevel : L.level c = Macaulay.level (fun i : Fin (L.arity c) => L.degree c i.val))
variable (hc : ∀ (i : Fin (L.arity c)) r u v, coefficient
    (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode r)
      (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))) =
    scalar modulus c u v ((p i).coeff (RationalSubstitution.Indexed.exponentVector
      (L.arity c) (FixedWidthPolynomial.entry (L.width c) r))))

include hlevel hc in
lemma rawEntry_source_packet (i : Fin (L.arity c))
    (a b : Macaulay.Index (L.arity c) (L.width c)) (u v : ℕ) :
    rawEntry L modulus coefficient (entryPacket c
      (i.val * FixedWidthPolynomial.count (L.arity c) (L.width c) + a.val) b.val u v) =
    scalar modulus c u v (MacaulayFullBox.matrix p (fun i => L.degree c i.val) (L.width c) (.inl (i,a)) b) := by
  have hlt : i.val * FixedWidthPolynomial.count (L.arity c) (L.width c) + a.val <
      L.arity c * FixedWidthPolynomial.count (L.arity c) (L.width c) := by
    have H := Nat.mul_le_mul_right (FixedWidthPolynomial.count (L.arity c) (L.width c)) i.isLt
    have ha := a.isLt
    rw [Nat.succ_mul] at H
    omega
  have hs : isSource L (entryPacket c
      (i.val * FixedWidthPolynomial.count (L.arity c) (L.width c) + a.val) b.val u v) := by
    simpa only [isSource, entryPacket, ctx, idx, pairFst_pair, pairSnd_pair,
      sourceCut_eq, MacaulayBits.fromBits_encode] using hlt
  rw [rawEntry, ite_eq_left hs, rawSourceInput_packet L c i.val a.val b.val u v a.isLt]
  rw [shifted_packet L c u v p (scalar modulus c u v) coefficient (scalar_zero _ _ _ _)
    (fun i r => hc i r u v)]
  change (if _ then _ else []) = scalar modulus c u v (if _ then _ else 0)
  rw [← hlevel]
  split_ifs <;> simp only [scalar_zero]

include hlevel in
lemma rawEntry_padding_packet (a b : Macaulay.Index (L.arity c) (L.width c)) (u v : ℕ) :
    rawEntry L modulus coefficient (entryPacket c
      (L.arity c * FixedWidthPolynomial.count (L.arity c) (L.width c) + a.val) b.val u v) =
    scalar modulus c u v (MacaulayFullBox.matrix p (fun i => L.degree c i.val) (L.width c) (.inr a) b) := by
  have hs : ¬ isSource L (entryPacket c
      (L.arity c * FixedWidthPolynomial.count (L.arity c) (L.width c) + a.val) b.val u v) := by
    simp only [isSource, entryPacket, ctx, idx, pairFst_pair, pairSnd_pair,
      sourceCut_eq, MacaulayBits.fromBits_encode]
    omega
  have hp : isPadding L (entryPacket c
      (L.arity c * FixedWidthPolynomial.count (L.arity c) (L.width c) + a.val) b.val u v) ↔
      (FixedWidthPolynomial.vector _ _ a).degree ≠ L.level c ∧ a = b := by
    unfold isPadding
    rw [rawPaddingInput_packet]
    simp only [ctx_entryPacket, idx_entryPacket, shift_entryPacket, sourceCut_eq,
      MacaulayBits.fromBits_encode, Nat.add_sub_cancel_left, ne_eq, total_packet_iff, Fin.ext_iff]
  rw [rawEntry, ite_eq_right hs]
  simp only [hp]
  change (if _ then _ else []) = scalar modulus c u v (if _ then (if _ then 1 else 0) else 0)
  rw [← hlevel]
  by_cases hab : a = b
  · subst b
    by_cases ha : (FixedWidthPolynomial.vector _ _ a).degree = L.level c <;>
      simp [ha, unit_packet, scalar_zero]
  · simp [hab, scalar_zero]

def rowNumber (n W : ℕ) : MacaulayFullBox.Row n W → ℕ
  | .inl (i,a) => i.val * FixedWidthPolynomial.count n W + a.val
  | .inr a => n * FixedWidthPolynomial.count n W + a.val

lemma rowNumber_eq (n W : ℕ) (a : MacaulayFullBox.Row n W) :
    rowNumber n W a = (MacaulayFullBoxFinite.rowEquiv n W a).val := by
  rcases a with ⟨i,a⟩ | a <;>
    simp [rowNumber, MacaulayFullBoxFinite.rowEquiv, finSumFinEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

lemma rowNumber_lt (n W : ℕ) (a : MacaulayFullBox.Row n W) :
    rowNumber n W a < (n + 1) * FixedWidthPolynomial.count n W := by
  rw [rowNumber_eq]
  exact (MacaulayFullBoxFinite.rowEquiv n W a).isLt

lemma rowNumber_injective (n W : ℕ) : Function.Injective (rowNumber n W) := by
  intro a b h
  apply (MacaulayFullBoxFinite.rowEquiv n W).injective
  apply Fin.ext
  simpa only [← rowNumber_eq] using h

lemma blockRow_number (n W : ℕ) (a : MacaulayFullBox.Row n W) :
    (MacaulayFullBoxFinite.blockEquiv n W (.inl a)).val = rowNumber n W a := by
  rcases a with ⟨i,a⟩ | a
  · exact MacaulayFullBoxFinite.source_code i a
  · exact MacaulayFullBoxFinite.padding_code a

include hlevel hc in
lemma rawEntry_row_packet (a : MacaulayFullBox.Row (L.arity c) (L.width c))
    (b : Macaulay.Index (L.arity c) (L.width c)) (u v : ℕ) :
    rawEntry L modulus coefficient (entryPacket c (rowNumber _ _ a) b.val u v) =
    scalar modulus c u v (MacaulayFullBox.matrix p (fun i => L.degree c i.val) (L.width c) a b) := by
  rcases a with ⟨i,a⟩ | a
  · exact rawEntry_source_packet L modulus coefficient c p hlevel hc i a b u v
  · exact rawEntry_padding_packet L modulus coefficient c p hlevel a b u v

lemma negate_scalar (modulus : List Bool → List Bool) (c : List Bool) (u v : ℕ) (a : Coefficient) :
    ArithmeticBits.negate (pair (BinaryNat.succ (modulus c)) (scalar modulus c u v a)) =
      scalar modulus c u v (-a) := by
  let m := Nat.fromBitsLE (modulus c) + 1
  let : NeZero m := ⟨by dsimp [m]; omega⟩
  rw [BinaryNat.succ_eq_bits]
  simpa only [scalar, Polynomial.coeff_neg, Int.cast_neg, m, BinaryNatCode.encode] using
    ArithmeticBits.negate_residueBits m (((a.coeff v).coeff u : ℤ) : ZMod m)

include hlevel hc in
lemma blockEntry_typed_packet
    (a b : Sum (MacaulayFullBox.Row (L.arity c) (L.width c)) (MacaulayFullBox.Column (L.arity c) (L.width c)))
    (u v : ℕ) :
    blockEntry L modulus coefficient (entryPacket c
      (MacaulayFullBoxFinite.blockEquiv _ _ a).val
      (MacaulayFullBoxFinite.blockEquiv _ _ b).val u v) =
    scalar modulus c u v (ProjectiveGramEliminant.block
      (MacaulayFullBox.matrix p (fun i => L.degree c i.val) (L.width c)) a b) := by
  rcases a with a | a <;> rcases b with b | b
  · rw [blockRow_number, blockRow_number]
    have ha := rowNumber_lt (L.arity c) (L.width c) a
    have hb := rowNumber_lt (L.arity c) (L.width c) b
    have he : rowNumber (L.arity c) (L.width c) a = rowNumber _ _ b ↔ a = b :=
      (rowNumber_injective _ _).eq_iff
    simp only [blockEntry, top_packet, left_packet, diagonal_packet, ha, hb, ite_true, he]
    change (if a = b then _ else []) = scalar modulus c u v (if a = b then 1 else 0)
    by_cases hab : a = b <;> simp only [hab, ite_true, ite_false, unit_packet, scalar_zero]
  · rw [blockRow_number, MacaulayFullBoxFinite.column_code]
    have ha := rowNumber_lt (L.arity c) (L.width c) a
    have hb : ¬ (L.arity c + 1) * FixedWidthPolynomial.count (L.arity c) (L.width c) + b.val <
      (L.arity c + 1) * FixedWidthPolynomial.count (L.arity c) (L.width c) := by omega
    simp only [blockEntry, top_packet, left_packet, ha, hb, ite_true, ite_false]
    rw [upperInput_packet, rawEntry_row_packet L modulus coefficient c p hlevel hc]
    rfl
  · rw [MacaulayFullBoxFinite.column_code, blockRow_number]
    have hb := rowNumber_lt (L.arity c) (L.width c) b
    have ha : ¬ (L.arity c + 1) * FixedWidthPolynomial.count (L.arity c) (L.width c) + a.val <
      (L.arity c + 1) * FixedWidthPolynomial.count (L.arity c) (L.width c) := by omega
    simp only [blockEntry, top_packet, left_packet, ha, hb, ite_true, ite_false]
    simp only [negateEntry, Function.comp_apply, ctx_entryPacket]
    rw [lowerInput_packet, rawEntry_row_packet L modulus coefficient c p hlevel hc, negate_scalar]
    rfl
  · rw [MacaulayFullBoxFinite.column_code, MacaulayFullBoxFinite.column_code]
    have ha : ¬ (L.arity c + 1) * FixedWidthPolynomial.count (L.arity c) (L.width c) + a.val <
      (L.arity c + 1) * FixedWidthPolynomial.count (L.arity c) (L.width c) := by omega
    have hb : ¬ (L.arity c + 1) * FixedWidthPolynomial.count (L.arity c) (L.width c) + b.val <
      (L.arity c + 1) * FixedWidthPolynomial.count (L.arity c) (L.width c) := by omega
    simp only [blockEntry, top_packet, left_packet, ha, hb, ite_false]
    exact (scalar_zero modulus c u v).symm

include hlevel hc in
lemma blockEntry_packet
    (a b : Fin ((L.arity c + 2) * FixedWidthPolynomial.count (L.arity c) (L.width c))) (u v : ℕ) :
    blockEntry L modulus coefficient (entryPacket c a.val b.val u v) =
    scalar modulus c u v (MacaulayFullBoxFinite.matrix p (fun i => L.degree c i.val) (L.width c) a b) := by
  have H := blockEntry_typed_packet L modulus coefficient c p hlevel hc
    ((MacaulayFullBoxFinite.blockEquiv _ _).symm a) ((MacaulayFullBoxFinite.blockEquiv _ _).symm b) u v
  simpa only [Equiv.apply_symm_apply, MacaulayFullBoxFinite.matrix, Matrix.submatrix_apply] using H

end LeanCanny.Algebra.MacaulayFullBoxBits
