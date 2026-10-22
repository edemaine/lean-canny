/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SymbolicScaledSquarefreeSpace

/-! # Total symbolic squarefree leaf programs with supplied metadata

Malformed metadata still defines a polynomial and a native reader. Equality to
the genuine symbolic squarefree part requires exact prepared degree and order
only at the semantic boundary.
-/
@[expose] public section
namespace LeanCanny.Algebra.SymbolicFormalSquarefreeBits
open Polynomial SymbolicScaledSquarefree
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open SymbolicScaledQuotientBits (original modulus alpha target coefficient original_FP modulus_FP alpha_FP target_FP)
open SymbolicSquarefreeBits (zeroWord_fppred sub_binary oneEvaluator derivativeEvaluator)
open scoped Classical
attribute [local irreducible] Matrix.det
set_option backward.isDefEq.respectTransparency false

def order (D K : ℕ) : ℕ := min K (D-1)
noncomputable def gcd (p : Polynomial Coefficient) (D K : ℕ) : Polynomial Coefficient :=
  if D=0 then 1 else PrincipalSubresultant.coefficientForm p p.derivative D (D-1) (order D K)
noncomputable def polynomial (p : Polynomial Coefficient) (D K : ℕ) : Polynomial Coefficient :=
  ScaledPolynomialQuotient.quotient (gcd p D K) p (order D K) (D-order D K)

theorem order_binary {D K : List Bool → ℕ} (hD : BinaryFn D) (hK : BinaryFn K) :
    BinaryFn (fun c => order (D c) (K c)) := by
  apply BinaryFn.of_bits
  have H := PrincipalCoefficientBits.minimum_mem_FP hK.bits_mem_FP (sub_binary hD (BinaryFn.const 1)).bits_mem_FP
  refine mem_FP_of_eq H (fun c => ?_)
  simp only [PrincipalCoefficientBits.minimum_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits, order]

noncomputable def gcdFamily (p : List Bool → Polynomial Coefficient) (D K : List Bool → ℕ) :
    SymbolicCoefficientFormBits.Family where
  left := p
  right c := (p c).derivative
  leftDegree c := if D c=0 then 1 else D c
  rightDegree c := D c-1
  order c := order (D c) (K c)
  order_left c := by have h := Nat.min_le_right (K c) (D c-1); dsimp [order]; split_ifs <;> omega
  order_right c := Nat.min_le_right _ _
  dimension_pos c := by have h := Nat.min_le_right (K c) (D c-1); dsimp [order]; split_ifs <;> omega

theorem gcdEvaluator (p : List Bool → Polynomial Coefficient) (D K E : List Bool → ℕ)
    (hE : ∀ c k, ((p c).coeff k).natDegree ≤ E c)
    (hD : BinaryFn D) (hK : BinaryFn K) (hB : BinaryFn E) (P : SpaceFunction (coefficient p)) :
    SpaceFunction (coefficient (fun c => gcd (p c) (D c) (K c))) := by
  have hz : FPPred (fun c => D c=0) :=
    (zeroWord_fppred hD.bits_mem_FP).of_iff (fun c => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits])
  have hm : BinaryFn (gcdFamily p D K).leftDegree := by
    apply BinaryFn.of_bits
    have H := hz.ite_mem_FP (constFn_mem_FP (BinaryNatCode.encode 1)) hD.bits_mem_FP
    refine mem_FP_of_eq H (fun c => ?_)
    dsimp only [gcdFamily]
    split_ifs <;> rfl
  have hn : BinaryFn (gcdFamily p D K).rightDegree := sub_binary hD (BinaryFn.const 1)
  have G := (gcdFamily p D K).evaluator E hE (fun c k => derivative_inner_degree (p c) (E c) (hE c) k)
    hm hn (order_binary hD hK) hB P (derivativeEvaluator p P)
  have R := SpaceFunction.branch (fun q => decide (D (original q)=0))
    (hz.comp original_FP).flag_mem_FP oneEvaluator G
  refine R.congr (funext fun q => ?_)
  simp only [decide_eq_true_eq, SymbolicCoefficientFormBits.Family.value, coefficient,
    SymbolicFixedTableEntryBits.coefficient]
  change (if D (original q)=0 then _ else _) =
    SymbolicFixedTableEntryBits.integerResidue
      (((gcd (p (original q)) (D (original q)) (K (original q))).coeff (Nat.fromBitsLE (target q))).coeff
        (Nat.fromBitsLE (alpha q))) (Nat.fromBitsLE (modulus q)+1)
  by_cases hd : D (original q)=0
  · simp only [original] at hd
    simp only [original, modulus, alpha, target, hd, ite_true, gcd]
  · simp only [original] at hd
    simp only [original, modulus, alpha, target, hd, ite_false, gcd, gcdFamily]

theorem gcd_inner_degree (p : Polynomial Coefficient) (D K E k : ℕ)
    (hE : ∀ k, (p.coeff k).natDegree ≤ E) : ((gcd p D K).coeff k).natDegree ≤ (2*D+1)*E := by
  rw [gcd]
  split_ifs
  · simp only [coeff_one]
    split_ifs <;> simp
  · rw [PrincipalSubresultant.coefficientForm_coeff]
    split_ifs
    · rw [PrincipalSubresultant.subresultantCoeff_eq_minor_det]
      apply (Subresultant.minor_natDegree_le p p.derivative D (D-1) (order D K) k E E hE
        (derivative_inner_degree p E hE)).trans
      have h1 := Nat.sub_le D (order D K)
      have h2 := (Nat.sub_le (D-1) (order D K)).trans (Nat.sub_le D 1)
      nlinarith
    · simp

noncomputable def quotientFamily (p : List Bool → Polynomial Coefficient) (D K : List Bool → ℕ) :
    SymbolicScaledQuotientBits.Family where
  divisor c := gcd (p c) (D c) (K c)
  dividend := p
  divisorDegree c := order (D c) (K c)
  quotientDegree c := D c-order (D c) (K c)

theorem evaluator (p : List Bool → Polynomial Coefficient) (D K E : List Bool → ℕ)
    (hE : ∀ c k, ((p c).coeff k).natDegree ≤ E c)
    (hD : BinaryFn D) (hK : BinaryFn K) (hB : BinaryFn E) (P : SpaceFunction (coefficient p)) :
    SpaceFunction (coefficient (fun c => polynomial (p c) (D c) (K c))) := by
  let B := fun c => (2*D c+1)*E c
  have hG c k : ((gcd (p c) (D c) (K c)).coeff k).natDegree ≤ B c := gcd_inner_degree _ _ _ _ _ (hE c)
  have hP c k : ((p c).coeff k).natDegree ≤ B c := (hE c k).trans (by dsimp [B]; nlinarith)
  have hb : BinaryFn B := (((BinaryFn.const 2).mul hD).add (BinaryFn.const 1)).mul hB
  exact (quotientFamily p D K).evaluator B hG hP (order_binary hD hK)
    (sub_binary hD (order_binary hD hK)) hb (gcdEvaluator p D K E hE hD hK hB P) P

theorem polynomial_natDegree_le (p : Polynomial Coefficient) (D K : ℕ) :
    (polynomial p D K).natDegree ≤ D :=
  (ScaledPolynomialQuotient.quotient_degree _ _ _ _).trans (Nat.sub_le _ _)

theorem polynomial_inner_degree (p : Polynomial Coefficient) (D K E k : ℕ)
    (hE : ∀ k, (p.coeff k).natDegree ≤ E) :
    ((polynomial p D K).coeff k).natDegree ≤ (D+1)*((2*D+1)*E) := by
  rw [polynomial, ScaledPolynomialQuotient.quotient_coeff]
  split_ifs with hk
  · let N := D-order D K+1
    let B := (2*D+1)*E
    have hp (i : ℕ) : (p.coeff i).natDegree ≤ B := (hE i).trans (by dsimp [B]; nlinarith)
    have hg (i : ℕ) : ((gcd p D K).coeff i).natDegree ≤ B := gcd_inner_degree p D K E i hE
    have he (i j : Fin N) :
        (((ScaledPolynomialQuotient.matrix (gcd p D K) (order D K) (D-order D K)).updateCol
          ⟨k, hk⟩ (ScaledPolynomialQuotient.input p (order D K) (D-order D K))) i j).natDegree ≤ B := by
      rw [ScaledPolynomialQuotient.selected_entry]
      split_ifs
      · exact hp _
      · exact hg _
      · simp
    have h := det_natDegree_le _ (fun _ : Fin N => B) he
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
    exact h.trans (Nat.mul_le_mul_right B (by dsimp [N]; omega))
  · simp

theorem polynomial_eq (p : Polynomial Coefficient) :
    polynomial p p.natDegree (SymbolicScaledSquarefree.degree p)=SymbolicScaledSquarefree.polynomial p := by
  have hk := SymbolicSquarefreeBits.order_le_derivative p
  simp only [polynomial, gcd, order, min_eq_left hk, SymbolicScaledSquarefree.polynomial,
    SymbolicScaledSquarefree.gcd, natDegree_derivative]

end LeanCanny.Algebra.SymbolicFormalSquarefreeBits
