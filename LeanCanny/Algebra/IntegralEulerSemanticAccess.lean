/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalScriptEuler
/-! # Native Euler metadata with actual semantic leaves -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralEulerSemanticBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false
open scoped Classical

structure Controls (S : IntegralEulerBits.Source) : Prop where
  arity : UnaryFn S.arity
  free : UnaryFn S.free
  offset : UnaryFn S.offset
  sourceWidth : UnaryFn S.sourceWidth
  targetWidth : UnaryFn S.targetWidth
  rank : BinaryFn S.rank
  allowance : BinaryFn S.allowance
  target : BinaryFn S.target
  row : BinaryFn (fun q => (S.row q).val)
  col : BinaryFn (fun q => (S.col q).val)
  modulus : BinaryFn S.modulus
  degree : BinaryFn S.degree
  objective : BinaryFn (fun q => (S.objective q).val)

noncomputable def coefficientAt (S : IntegralEulerBits.Source) (q : List Bool) (k r t : ℕ) : List Bool := by
  let := S.ring q
  have HP : 0 < S.rank q := (Nat.zero_le (S.row q).val).trans_lt (S.row q).isLt
  exact residueBits ((Algebra.leftMulMatrix (S.basis q) ((S.polynomial q).coeff
    (RationalSubstitution.Indexed.exponentVector (S.arity q) (FixedWidthPolynomial.entry (S.sourceWidth q) k)))
    ⟨r % S.rank q, Nat.mod_lt _ HP⟩ ⟨t % S.rank q, Nat.mod_lt _ HP⟩ : ℤ) : ZMod (S.modulus q))

noncomputable def coefficient (S : IntegralEulerBits.Source) (p : List Bool) : List Bool :=
  coefficientAt S (IntegralCriticalOriginalCoefficientBits.original p) (Nat.fromBitsLE (pairSnd p))
    (Nat.fromBitsLE (IntegralCriticalOriginalCoefficientBits.rowWord p)) (Nat.fromBitsLE (IntegralCriticalOriginalCoefficientBits.colWord p))

theorem coefficient_packet (S : IntegralEulerBits.Source) (q : List Bool) (k : ℕ) (r t : Fin (S.rank q)) :
    letI := S.ring q
    coefficient S (pair (IntegralClearedCoefficientBits.context q r.val t.val) (BinaryNatCode.encode k)) =
      residueBits ((Algebra.leftMulMatrix (S.basis q) ((S.polynomial q).coeff
        (RationalSubstitution.Indexed.exponentVector (S.arity q) (FixedWidthPolynomial.entry (S.sourceWidth q) k))) r t : ℤ) : ZMod (S.modulus q)) := by
  let := S.ring q
  unfold coefficient
  simp only [IntegralCriticalOriginalCoefficientBits.original, IntegralCriticalOriginalCoefficientBits.rowWord,
    IntegralCriticalOriginalCoefficientBits.colWord, IntegralClearedCoefficientBits.context,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold coefficientAt
  simp only [Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt t.isLt]

noncomputable def access (S : IntegralEulerBits.Source) (h : Controls S) : IntegralEulerBits.Access S where
  arity := h.arity
  free := h.free
  offset := h.offset
  sourceWidth := h.sourceWidth
  targetWidth := h.targetWidth
  rank := h.rank
  allowance := h.allowance
  target := h.target
  row := h.row
  col := h.col
  modulus := h.modulus
  coefficient := coefficient S
  height := IntegralCriticalScriptEulerBits.heightReader S.toGradient.toFrozen.toSource
  denominator q := residueBits (S.denominator q : ZMod (S.modulus q))
  coefficient_eq := coefficient_packet S
  height_eq := IntegralCriticalScriptEulerBits.height_packet _
  denominator_eq _ := rfl
  leading q := residueBits (S.leading q : ZMod (S.modulus q))
  leading_eq _ := rfl
  degree := h.degree
  objective := h.objective
end LeanCanny.Algebra.IntegralEulerSemanticBits
