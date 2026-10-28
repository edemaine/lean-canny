/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogenizationPolynomialSpace
public import LeanCanny.Algebra.AffineCoordinateLinearSpace

/-! # Native access to the coordinate-augmented homogeneous system

One selected original integer row reader supplies the homogenized tail.
The extra coordinate row has an explicit native reader. Degree allowances
are binary throughout.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineCoordinateRowsBits
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial MatrixPower
open scoped Classical

def tailRow (N : List Bool → ℕ) (hpos : ∀ c, 0 < N c)
    (row : (c : List Bool) → Fin (N c + 1)) (c : List Bool) : Fin (N c) :=
  ⟨min ((row c).val - 1) (N c - 1), by have := hpos c; omega⟩

theorem tailRow_succ (N : List Bool → ℕ) (hpos : ∀ c, 0 < N c)
    (row : (c : List Bool) → Fin (N c + 1)) (c : List Bool) (hi : (row c).val ≠ 0) :
    (tailRow N hpos row c).succ = row c := by
  apply Fin.ext
  have := (row c).isLt
  change min ((row c).val - 1) (N c - 1) + 1 = (row c).val
  omega

theorem tailRow_unary {N : List Bool → ℕ} (hN : UnaryFn N) (hpos : ∀ c, 0 < N c)
    (row : (c : List Bool) → Fin (N c + 1)) (hi : UnaryFn (fun c => (row c).val)) :
    UnaryFn (fun c => (tailRow N hpos row c).val) :=
  (hi.sub (UnaryFn.const 1)).min (hN.sub (UnaryFn.const 1))

noncomputable def value (N W D : List Bool → ℕ)
    (Q : (c : List Bool) → Fin (N c) → MvPolynomial (Fin (N c)) ℤ)
    (coordinate : (c : List Bool) → Fin (N c)) (row : (c : List Bool) → Fin (N c + 1))
    (parameter modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  residueBits ((((AffineCoordinateSystem.rows (Q (pairFst q)) (fun _ => D (pairFst q))
    (coordinate (pairFst q)) (row (pairFst q))).coeff
      (nativeExponent (Equiv.refl _) (W (pairFst q)) (Nat.fromBitsLE (pairSnd q)))).coeff
        (Nat.fromBitsLE (parameter (pairFst q))) : ℤ) : ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1))

theorem value_packet (N W D : List Bool → ℕ)
    (Q : (c : List Bool) → Fin (N c) → MvPolynomial (Fin (N c)) ℤ)
    (coordinate : (c : List Bool) → Fin (N c)) (row : (c : List Bool) → Fin (N c + 1))
    (parameter modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    value N W D Q coordinate row parameter modulus (pair c (BinaryNatCode.encode r)) =
      residueBits ((((AffineCoordinateSystem.rows (Q c) (fun _ => D c) (coordinate c) (row c)).coeff
        (nativeExponent (Equiv.refl _) (W c) r)).coeff (Nat.fromBitsLE (parameter c)) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  generalize hz : pair c (BinaryNatCode.encode r) = z
  have hc : pairFst z = c := by rw [← hz, pairFst_pair]
  have hr : Nat.fromBitsLE (pairSnd z) = r := by rw [← hz, pairSnd_pair, MacaulayBits.fromBits_encode]
  subst c
  subst r
  rfl

theorem evaluator {N W D : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W) (hD : BinaryFn D)
    (hpos : ∀ c, 0 < N c) (hwpos : ∀ c, 0 < W c)
    (Q : (c : List Bool) → Fin (N c) → MvPolynomial (Fin (N c)) ℤ)
    (coordinate : (c : List Bool) → Fin (N c)) (hc : UnaryFn (fun c => (coordinate c).val))
    (row : (c : List Bool) → Fin (N c + 1)) (hi : UnaryFn (fun c => (row c).val))
    {parameter modulus : List Bool → List Bool} (hk : parameter ∈ FP) (hm : modulus ∈ FP)
    (E : SpaceFunction (HomogenizationPolynomialBits.integerValue N W
      (fun c => Q c (tailRow N hpos row c)) modulus)) :
    SpaceFunction (value N W D Q coordinate row parameter modulus) := by
  have EL := AffineCoordinateLinearBits.evaluator hN hW hwpos coordinate hc hk hm
  have ER := HomogenizationPolynomialBits.evaluator hN hW hD _ parameter modulus hk E
  have hz := FPPred.eq (hi.comp pairFst_mem_FP) (UnaryFn.const 0)
  refine (SpaceFunction.branch _ hz.flag_mem_FP EL ER).congr (funext fun q => ?_)
  simp only [decide_eq_true_eq]
  by_cases hi0 : (row (pairFst q)).val = 0
  · rw [ite_eq_left hi0]
    have hrow : row (pairFst q) = 0 := Fin.ext hi0
    unfold value
    rw [hrow, ← AffineCoordinateLinearBits.polynomial_eq N coordinate (pairFst q)
      (Q (pairFst q)) (fun _ => D (pairFst q)), nativeExponent_refl]
    rfl
  · rw [ite_eq_right hi0]
    unfold value
    rw [← tailRow_succ N hpos row (pairFst q) hi0]
    rfl

end LeanCanny.Algebra.AffineCoordinateRowsBits
