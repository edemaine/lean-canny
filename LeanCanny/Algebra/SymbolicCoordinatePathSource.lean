/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicCoordinatePathMatrix
public import LeanCanny.Algebra.PolynomialMatrixProductSpace
public import LeanCanny.Algebra.RationalCoordinatePathMatrix
public import LeanCanny.Algebra.SymbolicFixedTableEntrySpace

/-! # Indexed symbolic paths with binary envelope controls -/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicCoordinatePathBits
open Polynomial SymbolicBalancedCoordinate
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

structure Source where
  inner : List Bool → ℕ → Coordinate
  exponent : List Bool → ℕ → ℕ
  cap : List Bool → ℕ
  depth : List Bool → ℕ
  innerBound : List Bool → ℕ
  exponent_le : ∀ c s, exponent c s ≤ cap c
  numeratorInner : ∀ c s k, ((inner c s).numerator.coeff k).natDegree ≤ innerBound c
  denominatorInner : ∀ c s k, ((inner c s).denominator.coeff k).natDegree ≤ innerBound c

noncomputable def Source.coordinate (F : Source) (c : List Bool) : Coordinate :=
  SymbolicCoordinatePath.path (F.exponent c) (F.inner c) (F.depth c)

noncomputable def Source.component (F : Source) (numerator : Bool) (c : List Bool) : Polynomial (Polynomial ℤ) :=
  if numerator then (F.coordinate c).numerator else (F.coordinate c).denominator

def original (q : List Bool) : List Bool := pairFst (pairFst q)
def rootWord (q : List Bool) : List Bool := pairSnd (pairSnd q)
def alphaWord (q : List Bool) : List Bool := pairFst (pairSnd q)
def width (F : Source) (q : List Bool) : ℕ := F.cap (original q) + Nat.fromBitsLE (rootWord q) + 2

theorem original_FP : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem rootWord_FP : rootWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem alphaWord_FP : alphaWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP

theorem width_binary (F : Source) (hcap : BinaryFn F.cap) : BinaryFn (width F) := by
  have h : BinaryFn (fun q => F.cap (original q)) := hcap.comp original_FP
  exact (h.add (BinaryFn.fromBits rootWord_FP)).add (BinaryFn.const 2)

noncomputable def factor (F : Source) (q : List Bool) (s : ℕ) :
    Matrix (Fin (width F q)) (Fin (width F q)) (Polynomial ℤ) :=
  SymbolicClearingMatrix.clearingMatrix (width F q) (F.exponent (original q) s)
    (F.inner (original q) s).numerator (F.inner (original q) s).denominator

noncomputable def productFamily (F : Source) (numerator : Bool) : PolynomialMatrixProductBits.Family where
  width := width F
  count q := F.depth (original q)
  modulus q := Nat.fromBitsLE (pairSnd (pairFst q)) + 1
  degree q := Nat.fromBitsLE (alphaWord q)
  row q := ⟨if numerator then 1 else 0, by unfold width; split_ifs <;> omega⟩
  col q := ⟨Nat.fromBitsLE (rootWord q), by unfold width; omega⟩
  factor q s := (factor F q s).map (Polynomial.mapRingHom (Int.castRingHom _))
  modulus_ne_zero _ := Nat.succ_ne_zero _

lemma value_eq (F : Source) (numerator : Bool) :
    (productFamily F numerator).value = SymbolicFixedTableEntryBits.coefficient (F.component numerator) := by
  funext q
  have H := SymbolicCoordinatePath.product_entries (width F q) (F.exponent (original q))
    (F.inner (original q)) (F.depth (original q)) (by unfold width; omega)
    (fun s _ => by have := F.exponent_le (original q) s; unfold width; omega)
    ⟨Nat.fromBitsLE (rootWord q), by unfold width; omega⟩
  have he : MatrixProduct.product ((productFamily F numerator).factor q) 0 (F.depth (original q)) =
      (MatrixProduct.product (SymbolicCoordinatePath.matrices (width F q)
        (F.exponent (original q)) (F.inner (original q))) 0 (F.depth (original q))).map
          (Polynomial.mapRingHom (Int.castRingHom _)) :=
    MatrixProduct.product_map _ _ _ _
  change residueBits (((MatrixProduct.product ((productFamily F numerator).factor q) 0
    (F.depth (original q))) ((productFamily F numerator).row q) ((productFamily F numerator).col q)).coeff
      (Nat.fromBitsLE (alphaWord q))) = _
  rw [he]
  change residueBits (((MatrixProduct.product
    (SymbolicCoordinatePath.matrices (width F q) (F.exponent (original q)) (F.inner (original q)))
    0 (F.depth (original q)) ⟨if numerator then 1 else 0, by unfold width; split_ifs <;> omega⟩
      ⟨Nat.fromBitsLE (rootWord q), by unfold width; omega⟩).map
        (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd (pairFst q)) + 1)))).coeff
          (Nat.fromBitsLE (alphaWord q))) = _
  rw [coeff_map]
  simp only [Int.coe_castRingHom]
  cases numerator
  · simpa only [productFamily, Source.component, Bool.false_eq_true, ite_false,
      Source.coordinate, SymbolicFixedTableEntryBits.coefficient, original, rootWord, alphaWord,
      SymbolicFixedTableEntryBits.integerResidue] using congrArg
        (fun p : Polynomial ℤ => residueBits ((p.coeff (Nat.fromBitsLE (alphaWord q)) : ℤ) :
          ZMod (Nat.fromBitsLE (pairSnd (pairFst q)) + 1))) H.2
  · simpa only [productFamily, Source.component, ite_true, Source.coordinate,
      SymbolicFixedTableEntryBits.coefficient, original, rootWord, alphaWord,
      SymbolicFixedTableEntryBits.integerResidue] using congrArg
        (fun p : Polynomial ℤ => residueBits ((p.coeff (Nat.fromBitsLE (alphaWord q)) : ℤ) :
          ZMod (Nat.fromBitsLE (pairSnd (pairFst q)) + 1))) H.1

end LeanCanny.Algebra.SymbolicCoordinatePathBits
