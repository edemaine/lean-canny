/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCoordinateBasisFin
public import LeanCanny.Algebra.FixedWidthRowArithmetic

/-! # Native canonical coefficients from regular-representation matrices

An actual algebra element is represented in its bounded monomial basis.
Each requested polynomial coefficient reads one original matrix entry in
column zero. All matrix-reader space is charged; no representative is stored.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCoordinateCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
universe u

structure Family where
  arity : List Bool → ℕ
  width : List Bool → ℕ
  carrier : List Bool → Type u
  ring : ∀ c, CommRing (carrier c)
  basis : ∀ c, @IntegralCoordinateBasis (carrier c) (ring c) (arity c) (2 ^ width c)
  element : ∀ c, carrier c

noncomputable def Family.polynomial (F : Family) (c : List Bool) : MvPolynomial (Fin (F.arity c)) ℤ := by
  letI := F.ring c
  exact (F.basis c).representative (F.element c)

noncomputable def Family.matrix (F : Family) (c : List Bool) :
    Matrix (Fin (count (F.arity c) (F.width c))) (Fin (count (F.arity c) (F.width c))) ℤ := by
  letI := F.ring c
  exact Algebra.leftMulMatrix (F.basis c).finBasis (F.element c)

theorem Family.coefficient (F : Family) (c : List Bool) (r : Fin (count (F.arity c) (F.width c))) :
    (F.polynomial c).coeff (vector (F.arity c) (F.width c) r) =
      F.matrix c r (IntegralCoordinateBasis.zeroFin (F.arity c) (F.width c)) := by
  let := F.ring c
  exact (F.basis c).coefficient_finMatrix (F.element c) r

def query (F : Family) (target modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  pair (pair c (modulus c))
    (pair (BinaryNat.normalize (FixedWidthQuery.repack F.arity F.width F.arity F.width target c)) [])

theorem query_FP (F : Family) (target modulus : List Bool → List Bool)
    (hA : UnaryFn F.arity) (hW : UnaryFn F.width) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    query F target modulus ∈ FP :=
  mem_FP_pair (mem_FP_pair id_mem_FP hm) (mem_FP_pair
    (mem_FP_comp (FixedWidthQuery.repack_mem_FP hA hW hA hW ht) BinaryNat.normalize_mem_FP) (constFn_mem_FP []))

theorem packet (F : Family) (target modulus entry : List Bool → List Bool)
    (he : ∀ c mw (i j : Fin (count (F.arity c) (F.width c))),
      entry (pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
        residueBits ((F.matrix c i j : ℤ) : ZMod (Nat.fromBitsLE mw + 1))) (c : List Bool) :
    entry (query F target modulus c) = FixedWidthRowBits.value F.arity F.width F.polynomial target modulus c := by
  let word := FixedWidthQuery.repack F.arity F.width F.arity F.width target c
  let rank := Nat.fromBitsLE word
  have HR : rank < count (F.arity c) (F.width c) := by
    have H := Nat.fromBitsLE_lt_pow_length word
    rw [FixedWidthQuery.repack_length] at H
    simpa only [count, ← pow_mul, Nat.mul_comm (F.width c)] using H
  have HV : vector (F.arity c) (F.width c) ⟨rank, HR⟩ =
      nativeExponent (Equiv.refl _) (F.width c) (Nat.fromBitsLE (target c)) := by
    calc
      _ = nativeExponent (Equiv.refl _) (F.width c) rank :=
        ((nativeExponent_refl _ _ _).trans (entry_vector _ _ ⟨rank, HR⟩)).symm
      _ = _ := nativeExponent_repack (Equiv.refl _) F.width F.width target c le_rfl
  have HQ : query F target modulus c = pair (pair c (modulus c))
      (pair (BinaryNatCode.encode (⟨rank, HR⟩ : Fin (count (F.arity c) (F.width c))).val)
        (BinaryNatCode.encode (IntegralCoordinateBasis.zeroFin (F.arity c) (F.width c)).val)) := by
    simp only [query, IntegralCoordinateBasis.zeroFin, BinaryNat.normalize_eq_bits]
    rfl
  rw [HQ, he]
  have HC : F.matrix c ⟨rank, HR⟩ (IntegralCoordinateBasis.zeroFin (F.arity c) (F.width c)) =
      (F.polynomial c).coeff (nativeExponent (Equiv.refl _) (F.width c) (Nat.fromBitsLE (target c))) := by
    rw [← F.coefficient c ⟨rank, HR⟩, HV]
  rw [HC]
  rfl

theorem evaluator (F : Family) (target modulus entry : List Bool → List Bool)
    (hA : UnaryFn F.arity) (hW : UnaryFn F.width) (ht : target ∈ FP) (hm : modulus ∈ FP)
    (E : SpaceFunction entry)
    (he : ∀ c mw (i j : Fin (count (F.arity c) (F.width c))),
      entry (pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
        residueBits ((F.matrix c i j : ℤ) : ZMod (Nat.fromBitsLE mw + 1))) :
    SpaceFunction (FixedWidthRowBits.value F.arity F.width F.polynomial target modulus) :=
  (E.precompose _ (query_FP F target modulus hA hW ht hm)).congr (funext fun c => packet F target modulus entry he c)

end LeanCanny.Algebra.IntegralCoordinateCoefficientBits
