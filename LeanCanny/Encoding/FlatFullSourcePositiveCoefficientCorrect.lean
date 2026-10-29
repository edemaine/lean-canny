/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourcePositiveCoefficient

/-! # Exact coefficients of the positive-dimensional completion

The native reader evaluates every old row and the dummy row of the existing
padded system, at arbitrary fixed-width monomials and raw moduli. It rejects
indices beyond the dummy row. The empty tower retains the valid dummy row.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourcePositiveCoefficient
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatFullSourceTower (Inputs count degree)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourceTower.system

theorem embedded_packet (F : Inputs) (W : List Bool → ℕ) (row target modulus : List Bool → List Bool)
    (c : List Bool) (i : Fin (count F c)) (hi : Nat.fromBitsLE (row c) = i.val)
    (hW : degree F c < 2 ^ W c) :
    embedded F W row target modulus c = MatrixPower.residueBits
      (((rename Fin.castSucc (FlatFullSourceTower.system F c i)).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (FlatFullSourcePositive.count F c))) (W c)
          (Nat.fromBitsLE (target c))) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  have hfit : 0 + count F c ≤ FlatFullSourcePositive.count F c := by
    unfold FlatFullSourcePositive.count
    omega
  have H := FixedWidthBlockRenameBits.packet (count F) (FlatFullSourcePositive.count F) (fun _ => 0) W target
    (FlatFullSourceTower.system F c i) hfit (reader F W row modulus) c _ rfl rfl rfl
    (reader_packet F W row modulus c i hi hW)
  have he : BlockRenameCoefficient.shift (count F c) (FlatFullSourcePositive.count F c) 0 hfit =
      Fin.castSucc := by
    funext j
    apply Fin.ext
    change 0 + j.val = j.val
    omega
  rw [he] at H
  exact H

theorem dummy_packet (F : Inputs) (W : List Bool → ℕ) (target modulus : List Bool → List Bool) (c : List Bool) :
    dummy F W target modulus c = MatrixPower.residueBits
      (((X (Fin.last (count F c)) : MvPolynomial (Fin (FlatFullSourcePositive.count F c)) ℤ).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (FlatFullSourcePositive.count F c))) (W c)
          (Nat.fromBitsLE (target c))) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) :=
  FixedWidthLinearCoefficientBits.packet (FlatFullSourcePositive.count F) W (count F) target
    (FlatFullSourceCriticalCoefficient.modulusCode modulus) c (Fin.last (count F c)) rfl _
    (FlatFullSourceCriticalCoefficient.modulusCode_eq modulus c)

theorem packet (F : Inputs) (W : List Bool → ℕ) (row target modulus : List Bool → List Bool)
    (c : List Bool) (i : Fin (FlatFullSourcePositive.count F c)) (hi : Nat.fromBitsLE (row c) = i.val)
    (hW : degree F c < 2 ^ W c) :
    value F W row target modulus c = MatrixPower.residueBits
      (((FlatFullSourcePositive.system F c i).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (FlatFullSourcePositive.count F c))) (W c)
          (Nat.fromBitsLE (target c))) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  by_cases hd : i.val = count F c
  · have he : i = Fin.last (count F c) := Fin.ext hd
    rw [value, ite_eq_left (hi.trans hd), dummy_packet]
    change _ = MatrixPower.residueBits
      (((PositivePolynomialSystem.system (FlatFullSourceTower.system F c) i).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (FlatFullSourcePositive.count F c))) (W c)
          (Nat.fromBitsLE (target c))) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))
    rw [he, PositivePolynomialSystem.new_row]
    rfl
  · have hil : i.val < count F c := by
      have hil := i.isLt
      change i.val < count F c + 1 at hil
      omega
    let old : Fin (count F c) := ⟨i.val, hil⟩
    have he : i = old.castSucc := Fin.ext rfl
    rw [value, ite_eq_right (fun h => hd (hi.symm.trans h)), ite_eq_left (by omega),
      embedded_packet F W row target modulus c old hi hW]
    change _ = MatrixPower.residueBits
      (((PositivePolynomialSystem.system (FlatFullSourceTower.system F c) i).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (FlatFullSourcePositive.count F c))) (W c)
          (Nat.fromBitsLE (target c))) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))
    rw [he, PositivePolynomialSystem.old_row]

theorem invalid (F : Inputs) (W : List Bool → ℕ) (row target modulus : List Bool → List Bool)
    (c : List Bool) (h : FlatFullSourcePositive.count F c ≤ Nat.fromBitsLE (row c)) :
    value F W row target modulus c = [] := by
  have hn : count F c + 1 ≤ Nat.fromBitsLE (row c) := h
  rw [value, ite_eq_right (by omega), ite_eq_right (by omega)]

end LeanCanny.Encoding.FlatFullSourcePositiveCoefficient
