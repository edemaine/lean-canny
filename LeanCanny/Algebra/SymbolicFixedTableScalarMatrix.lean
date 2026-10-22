/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableMatrix

/-! # One-dimensional encoded symbolic leaf matrices -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace LeanCanny.Algebra.SymbolicFixedTableScalarMatrix
open LeanCanny.Encoding LeanCanny.Computation
open Polynomial MatrixPower SymbolicScaledSquarefree
open SymbolicFixedTableEntryBits

noncomputable def family (P : List Bool → Polynomial Coefficient) (radix degree : List Bool → ℕ) :
    BerkowitzPolynomial.ModularFamily where
  dimension _ := 1
  modulus q := Nat.fromBitsLE (pairSnd q) + 1
  degree := degree
  matrix q := fun _ _ => (PolynomialKronecker.encode (radix q) (P (pairFst q))).map
    (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
  modulus_ne_zero _ := by omega

def query (radix : List Bool → ℕ) (q : List Bool) : List Bool :=
  let d := Nat.fromBitsLE (pairSnd (pairSnd (pairSnd q)))
  pair (pair (pairFst (pairFst q)) (pairSnd (pairFst q)))
    (pair (BinaryNatCode.encode (d % radix (pairFst q))) (BinaryNatCode.encode (d / radix (pairFst q))))

theorem query_FP (radix : List Bool → ℕ) (hB : BinaryFn radix) : query radix ∈ FP := by
  have hd := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
  have hb := mem_FP_comp pairFst_mem_FP hB.bits_mem_FP
  have hp := mem_FP_pair hd hb
  exact mem_FP_of_eq (mem_FP_pair
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP))
    (mem_FP_pair (mem_FP_comp hp BinaryNat.mod_mem_FP) (mem_FP_comp hp BinaryNat.div_mem_FP)))
    (fun q => by simp only [Function.comp_apply, query, BinaryNat.mod_pair, BinaryNat.div_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits])

noncomputable def access (P : List Bool → Polynomial Coefficient) (radix degree : List Bool → ℕ)
    (hP : ∀ q k, ((P (pairFst q)).coeff k).natDegree < radix q) :
    BerkowitzPolynomial.ModularAccess (family P radix degree) where
  dimension _ := [true]
  modulus q := BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q) + 1)
  degree q := BinaryNatCode.encode (degree q)
  entry := coefficient P ∘ query radix
  dimension_eq _ := by simp only [family, BinaryNatCode.encode, Nat.one_bits]
  modulus_eq _ := rfl
  degree_eq _ := rfl
  entry_eq q i j d := by
    have hB : 0 < radix q := (Nat.zero_le _).trans_lt (hP q 0)
    have h := PolynomialKronecker.coefficient_any (radix q) hB (P (pairFst q)) (hP q) d
    change coefficient P (query radix _) = residueBits
      (((PolynomialKronecker.encode (radix q) (P (pairFst q))).map (Int.castRingHom _)).coeff d)
    rw [Polynomial.coeff_map]
    change coefficient P (query radix _) = integerResidue _ (Nat.fromBitsLE (pairSnd q) + 1)
    simp only [query, coefficient, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, h]

theorem controls (P : List Bool → Polynomial Coefficient) (radix degree : List Bool → ℕ)
    (hP : ∀ q k, ((P (pairFst q)).coeff k).natDegree < radix q) (hd : BinaryFn degree) :
    (access P radix degree hP).ControlsPolyTime := by
  refine ⟨constFn_mem_FP [true], ?_, hd.bits_mem_FP⟩
  exact mem_FP_comp (f := pairSnd) (g := fun c => BinaryNatCode.encode (Nat.fromBitsLE c + 1))
    pairSnd_mem_FP ((BinaryFn.fromBits id_mem_FP).add (BinaryFn.const 1)).bits_mem_FP

theorem entry_space (P : List Bool → Polynomial Coefficient) (radix degree : List Bool → ℕ)
    (hP : ∀ q k, ((P (pairFst q)).coeff k).natDegree < radix q) (hB : BinaryFn radix)
    (A : SpaceFunction (coefficient P)) : SpaceFunction (access P radix degree hP).entry :=
  A.precompose (query radix) (query_FP radix hB)

theorem value_eq (P : List Bool → Polynomial Coefficient) (radix degree : List Bool → ℕ) (q : List Bool) :
    (family P radix degree).value q = integerResidue
      ((PolynomialKronecker.encode (radix q) (P (pairFst q))).coeff (degree q))
      (Nat.fromBitsLE (pairSnd q) + 1) := by
  change residueBits ((Matrix.det (fun (_ _ : Fin 1) =>
    (PolynomialKronecker.encode (radix q) (P (pairFst q))).map (Int.castRingHom _))).coeff _) = _
  rw [Matrix.det_fin_one, Polynomial.coeff_map]
  rfl

end LeanCanny.Algebra.SymbolicFixedTableScalarMatrix
