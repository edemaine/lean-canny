/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMonomialTermSource

/-! # Algebra values of original cleared-monomial factor products -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMonomialTermBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def Source.scalar (S : Source) (c : List Bool) : S.carrier c := by
  letI := S.ring c
  exact S.coefficient c * (S.denominator c : S.carrier c) ^ (S.allowance c - degree S c) *
    ∏ i : Fin (S.arity c), ClearedCoordinateBlock.scalarAtom (S.denominator c : S.carrier c)
      (S.height c) (S.offset c) (S.free c) i.val (S.exponent c i.val)

theorem factor_product (S : Source) (c : List Bool) :
    letI := S.ring c
    IntegralPowerProductBits.ordered (fun s => factor S c s ^ factorExponent S c s) 0 (S.arity c + 2) = S.scalar c := by
  let := S.ring c
  have H0 : factor S c 0 = S.coefficient c := by rw [factor, ite_eq_left rfl]
  have H1 : factor S c 1 = (S.denominator c : S.carrier c) := by
    rw [factor, ite_eq_right (by decide : (1 : ℕ) ≠ 0), ite_eq_left rfl]
  have E0 : factorExponent S c 0 = 1 := by rw [factorExponent, ite_eq_left rfl]
  have E1 : factorExponent S c 1 = S.allowance c - degree S c := by
    rw [factorExponent, ite_eq_right (by decide : (1 : ℕ) ≠ 0), ite_eq_left rfl]
  have HT : IntegralPowerProductBits.ordered (fun s => factor S c s ^ factorExponent S c s) 2 (S.arity c) =
      ∏ i : Fin (S.arity c), ClearedCoordinateBlock.scalarAtom (S.denominator c : S.carrier c)
        (S.height c) (S.offset c) (S.free c) i.val (S.exponent c i.val) := by
    rw [IntegralPowerProductBits.ordered_finprod]
    apply Finset.prod_congr rfl
    intro i _
    have h0 : 2 + i.val ≠ 0 := by omega
    have h1 : 2 + i.val ≠ 1 := by omega
    have h2 : 2 + i.val - 2 = i.val := by omega
    simp only [factor, factorExponent, ite_eq_right h0, ite_eq_right h1, h2, ite_eq_left i.isLt]
    unfold ClearedCoordinateBlock.scalarAtom isFree
    split_ifs <;> rfl
  rw [IntegralPowerProductBits.ordered, IntegralPowerProductBits.ordered, H0, E0, pow_one, H1, E1, HT]
  exact (mul_assoc _ _ _).symm

noncomputable def Source.value (S : Source) (c : List Bool) : List Bool := by
  letI := S.ring c
  exact residueBits ((Algebra.leftMulMatrix (S.basis c) (S.scalar c) (S.row c) (S.col c) : ℤ) : ZMod (S.modulus c))

theorem family_value (S : Source) : (family S).value = S.value := by
  funext c
  let := S.ring c
  have H := congrArg (fun x : S.carrier c => residueBits
    ((Algebra.leftMulMatrix (S.basis c) x (S.row c) (S.col c) : ℤ) : ZMod (S.modulus c))) (factor_product S c)
  exact H

end LeanCanny.Algebra.IntegralMonomialTermBits
