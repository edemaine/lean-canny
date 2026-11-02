/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.SizedCollectedCoefficient
public import LeanCanny.Algebra.FixedWidthPolynomial
/-! # Streamed original integer coefficients at literal fixed-width packets -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralOriginalTermCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

noncomputable def scalar (A W M : List Bool → ℕ)
    (integer : (q : List Bool) → MvPolynomial (Fin (A q)) ℤ) (p : List Bool) : List Bool :=
  residueBits ((integer (pairFst p)).coeff
    (RationalSubstitution.Indexed.exponentVector (A (pairFst p))
      (FixedWidthPolynomial.entry (W (pairFst p)) (Nat.fromBitsLE (pairSnd p)))) : ZMod (M (pairFst p)))

theorem evaluator (A W M : List Bool → ℕ)
    (hA : UnaryFn A) (hW : UnaryFn W) (hM : BinaryFn M) (hpos : ∀ q, M q ≠ 0)
    (integer : (q : List Bool) → MvPolynomial (Fin (A q)) ℤ)
    (word : List Bool → List Bool) (hword : word ∈ FP)
    (hs : ∀ q, (ETR.TermView.term (word q)).arity ≤ A q)
    (hp : ∀ q, (ETR.TermView.term (word q)).finitePolynomial (A q) = integer q) :
    SpaceFunction (scalar A W M integer) := by
  have HM : BinaryFn (fun p => M (pairFst p)) := hM.comp pairFst_mem_FP
  have E := ETR.SizedCollectedCoefficient.evaluator (hA.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP hword) (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)
    ((HM.sub (BinaryFn.const 1)).bits_mem_FP) (fun p => hs (pairFst p))
  apply E.congr
  funext p
  have Hmod : Nat.fromBitsLE (BinaryNatCode.encode (M (pairFst p) - 1)) + 1 = M (pairFst p) := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    have H := hpos (pairFst p)
    omega
  unfold ETR.SizedCollectedCoefficient.value
  rw [Hmod]
  simp only [Function.comp_apply]
  rw [hp]
  have HC : FixedWidthQuery.coordinate (fun z => W (pairFst z)) (BinaryNat.normalize ∘ pairSnd) p =
      FixedWidthPolynomial.entry (W (pairFst p)) (Nat.fromBitsLE (pairSnd p)) := by
    funext i
    simp only [FixedWidthQuery.coordinate, Function.comp_apply, BinaryNat.normalize_eq_bits, FixedWidthPolynomial.entry]
  rw [HC]
  rfl

end LeanCanny.Algebra.IntegralOriginalTermCoefficientBits
