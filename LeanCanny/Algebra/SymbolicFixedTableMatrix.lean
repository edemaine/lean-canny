/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTablePolynomialTree
public import LeanCanny.Algebra.BerkowitzPolynomialBranch

/-! # Encoded symbolic matrices for the uniform coefficient graph

The matrix dimension may be zero. Encoding is performed on matrix entries and
commutes with the determinant; slicing is used only to implement each entry.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTableEntryBits
open Polynomial SymbolicScaledSquarefree SymbolicFixedTable
open LeanCanny.Encoding LeanCanny.Computation MatrixPower

noncomputable def Family.encodedMatrixFamily (F : Family) (radix degree : List Bool → ℕ) :
    BerkowitzPolynomial.ModularFamily where
  dimension q := F.leftOrder (pairFst q) + F.rightOrder (pairFst q)
  modulus q := Nat.fromBitsLE (pairSnd q) + 1
  degree := degree
  matrix q := (Polynomial.sylvester (shiftFamily (F.left (pairFst q)) (F.direction (pairFst q)))
    ((F.right (pairFst q)).map C) (F.leftOrder (pairFst q)) (F.rightOrder (pairFst q))).map
      ((Polynomial.mapRingHom (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1)))).comp
        (PolynomialKronecker.encode (radix q)))
  modulus_ne_zero _ := by omega

noncomputable def Family.encodedMatrixAccess (F : Family) (radix degree : List Bool → ℕ)
    (E : List Bool → ℕ)
    (hl : ∀ c k, ((F.left c).coeff k).natDegree ≤ E c)
    (hr : ∀ c k, ((F.right c).coeff k).natDegree ≤ E c)
    (hB : ∀ q, E (pairFst q) < radix q) :
    BerkowitzPolynomial.ModularAccess (F.encodedMatrixFamily radix degree) where
  dimension q := BinaryNatCode.encode (F.leftOrder (pairFst q) + F.rightOrder (pairFst q))
  modulus q := BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q) + 1)
  degree q := BinaryNatCode.encode (degree q)
  entry := F.encodedEntry (fun q => BinaryNatCode.encode (radix q))
  dimension_eq _ := rfl
  modulus_eq _ := rfl
  degree_eq _ := rfl
  entry_eq q i j d := by
    have h := F.encodedEntry_correct (fun _ => BinaryNatCode.encode (radix q))
      (pairFst q) (pairSnd q) (E (pairFst q)) (hl (pairFst q)) (hr (pairFst q))
      (by simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using hB q) i j d
    -- The actual matrix context need not be a well-formed encoded pair.
    -- Both entry implementations use only its two projections.
    change F.encodedEntry _ _ = integerResidue _ (Nat.fromBitsLE (pairSnd q) + 1) at h
    change F.encodedEntry _ _ = residueBits
      ((((PolynomialKronecker.encode (radix q))
        (Polynomial.sylvester (shiftFamily (F.left (pairFst q)) (F.direction (pairFst q)))
          ((F.right (pairFst q)).map C) (F.leftOrder (pairFst q)) (F.rightOrder (pairFst q)) i j)).map
            (Int.castRingHom _)).coeff d)
    rw [Polynomial.coeff_map]
    change F.encodedEntry _ _ = integerResidue _ (Nat.fromBitsLE (pairSnd q) + 1)
    simpa only [Family.encodedEntry, Function.comp_apply, splitInput, entryDegree, entryQuery,
      Family.entry, pairFst_pair, pairSnd_pair, Family.encodedMatrixFamily, Matrix.map_apply,
      RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Int.coe_castRingHom,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
      using h

theorem Family.encodedMatrix_controls (F : Family) (radix degree E : List Bool → ℕ)
    (hl : ∀ c k, ((F.left c).coeff k).natDegree ≤ E c)
    (hr : ∀ c k, ((F.right c).coeff k).natDegree ≤ E c)
    (hB : ∀ q, E (pairFst q) < radix q)
    (hm : BinaryFn F.leftOrder) (hn : BinaryFn F.rightOrder) (hd : BinaryFn degree) :
    (F.encodedMatrixAccess radix degree E hl hr hB).ControlsPolyTime := by
  constructor
  · exact mem_FP_comp (f := pairFst) (g := fun c => BinaryNatCode.encode (F.leftOrder c + F.rightOrder c))
      pairFst_mem_FP (hm.add hn).bits_mem_FP
  · exact mem_FP_comp (f := pairSnd) (g := fun c => BinaryNatCode.encode (Nat.fromBitsLE c + 1))
      pairSnd_mem_FP ((BinaryFn.fromBits id_mem_FP).add (BinaryFn.const 1)).bits_mem_FP
  · exact hd.bits_mem_FP

theorem Family.encodedMatrixAccess_entry (F : Family) (radix degree E : List Bool → ℕ)
    (hl : ∀ c k, ((F.left c).coeff k).natDegree ≤ E c)
    (hr : ∀ c k, ((F.right c).coeff k).natDegree ≤ E c)
    (hB : ∀ q, E (pairFst q) < radix q) :
    (F.encodedMatrixAccess radix degree E hl hr hB).entry =
      F.encodedEntry (fun q => BinaryNatCode.encode (radix q)) := rfl

theorem Family.encodedMatrix_value (F : Family) (radix degree : List Bool → ℕ) (q : List Bool) :
    (F.encodedMatrixFamily radix degree).value q = integerResidue
      ((PolynomialKronecker.encode (radix q)
        (cannyResultantWithDegrees (F.left (pairFst q)) (F.right (pairFst q))
          (F.direction (pairFst q)) (F.leftOrder (pairFst q)) (F.rightOrder (pairFst q)))).coeff (degree q))
      (Nat.fromBitsLE (pairSnd q) + 1) := by
  let φ : Polynomial Coefficient →+* Polynomial (ZMod (Nat.fromBitsLE (pairSnd q) + 1)) :=
    (Polynomial.mapRingHom (Int.castRingHom _)).comp (PolynomialKronecker.encode (radix q))
  change residueBits (((Polynomial.sylvester _ _ _ _).map φ).det.coeff _) = _
  have hd : φ (Polynomial.sylvester (shiftFamily (F.left (pairFst q)) (F.direction (pairFst q)))
      ((F.right (pairFst q)).map C) (F.leftOrder (pairFst q)) (F.rightOrder (pairFst q))).det =
      ((Polynomial.sylvester (shiftFamily (F.left (pairFst q)) (F.direction (pairFst q)))
      ((F.right (pairFst q)).map C) (F.leftOrder (pairFst q)) (F.rightOrder (pairFst q))).map φ).det :=
    φ.map_det _
  rw [← hd]
  change residueBits (((PolynomialKronecker.encode (radix q)
    (cannyResultantWithDegrees (F.left (pairFst q)) (F.right (pairFst q))
      (F.direction (pairFst q)) (F.leftOrder (pairFst q)) (F.rightOrder (pairFst q)))).map
        (Int.castRingHom _)).coeff (degree q)) = _
  rw [Polynomial.coeff_map]
  rfl

end LeanCanny.Algebra.SymbolicFixedTableEntryBits
