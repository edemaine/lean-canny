/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SymbolicCoefficientFormSpace
public import LeanCanny.Algebra.SymbolicScaledSquarefreeBounds
public import LeanCanny.Algebra.ModularResidueSpace

/-! # Native symbolic squarefree leaf coefficients

Exact degree and GCD-order metadata may be retained in a prepared input table.
The two nested determinants charge their original coefficient readers through
native space composition. No degree or GCD oracle is asserted to be FP.
-/
@[expose] public section
namespace LeanCanny.Algebra.SymbolicSquarefreeBits
open Polynomial SymbolicScaledSquarefree
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open SymbolicScaledQuotientBits (original modulus alpha target coefficient original_FP modulus_FP alpha_FP target_FP)
open scoped Classical
attribute [local irreducible] Matrix.det
set_option backward.isDefEq.respectTransparency false

def derivativeQuery (q : List Bool) : List Bool :=
  pair (pairFst q) (pair (alpha q) (BinaryNat.succ (target q)))
theorem derivativeQuery_FP : derivativeQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair alpha_FP
    (mem_FP_comp (f := target) (g := BinaryNat.succ) target_FP BinaryNat.succ_mem_FP))

theorem derivativeEvaluator (p : List Bool → Polynomial Coefficient)
    (E : SpaceFunction (coefficient p)) : SpaceFunction (coefficient (fun c => (p c).derivative)) := by
  let a := fun q => (((p (original q)).coeff (Nat.fromBitsLE (target q)+1)).coeff (Nat.fromBitsLE (alpha q)) : ℤ)
  let b := fun q => Nat.fromBitsLE (target q)+1
  have A : SpaceFunction (fun q => residueBits ((a q : ℤ) : ZMod (Nat.fromBitsLE (modulus q)+1))) := by
    refine (E.precompose derivativeQuery derivativeQuery_FP).congr (funext fun q => ?_)
    simp only [Function.comp_apply, coefficient, SymbolicFixedTableEntryBits.coefficient,
      derivativeQuery, original, modulus, alpha, target, pairFst_pair, pairSnd_pair,
      BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits, a]
    rfl
  have hB := mem_FP_comp (mem_FP_pair
    (mem_FP_comp (f := target) (g := BinaryNat.succ) target_FP BinaryNat.succ_mem_FP)
    (mem_FP_comp (f := modulus) (g := BinaryNat.succ) modulus_FP BinaryNat.succ_mem_FP)) BinaryNat.mod_mem_FP
  have B : SpaceFunction (fun q => residueBits ((b q : ℕ) : ZMod (Nat.fromBitsLE (modulus q)+1))) := by
    apply SpaceFunction.ofFP
    refine mem_FP_of_eq hB (fun q => ?_)
    simp only [Function.comp_apply, BinaryNat.mod_pair, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits,
      residueBits, BinaryNatCode.encode, ZMod.val_natCast, b]
  have M := ModularResidueSpace.mulEvaluator modulus _ _ modulus_FP A B
  refine M.congr (funext fun q => ?_)
  simp only [coefficient, SymbolicFixedTableEntryBits.coefficient, coeff_derivative,
    ← Nat.cast_add_one, a, b]
  change residueBits (((_ : ℤ) : ZMod _)* ((_ : ℕ) : ZMod _)) = _
  change _ = SymbolicFixedTableEntryBits.integerResidue
    ((((p (original q)).coeff (Nat.fromBitsLE (target q)+1))*
      ((Nat.fromBitsLE (target q)+1 : ℕ) : Polynomial ℤ)).coeff (Nat.fromBitsLE (alpha q)))
    (Nat.fromBitsLE (modulus q)+1)
  rw [show ((Nat.fromBitsLE (target q)+1 : ℕ) : Polynomial ℤ) = C (((Nat.fromBitsLE (target q)+1 : ℕ) : ℤ)) by simp]
  rw [coeff_mul_C]
  simp only [SymbolicFixedTableEntryBits.integerResidue, Int.cast_mul, Int.cast_natCast]

theorem order_le_derivative (p : Polynomial Coefficient) : SymbolicScaledSquarefree.degree p ≤ p.natDegree-1 := by
  by_cases hd : p.natDegree=0
  · simp only [SymbolicScaledSquarefree.degree, hd, dite_true]
    omega
  · have hdeg : (fractionPolynomial p).natDegree=p.natDegree :=
      natDegree_map_eq_of_injective embedding_injective p
    have hne : (fractionPolynomial p).derivative ≠ 0 := derivative_ne_zero.mpr (by omega)
    have h := natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right (fractionPolynomial p) (fractionPolynomial p).derivative) hne
    rw [natDegree_derivative, hdeg] at h
    simpa only [degree_eq_common, SquarefreePart.common] using h

noncomputable def gcdFamily (p : List Bool → Polynomial Coefficient) : SymbolicCoefficientFormBits.Family where
  left := p
  right c := (p c).derivative
  leftDegree c := if (p c).natDegree=0 then 1 else (p c).natDegree
  rightDegree c := (p c).natDegree-1
  order c := SymbolicScaledSquarefree.degree (p c)
  order_left c := by
    have h := order_le_derivative (p c)
    split_ifs <;> omega
  order_right c := order_le_derivative (p c)
  dimension_pos c := by
    have h := order_le_derivative (p c)
    split_ifs <;> omega

theorem zeroWord_fppred {w : List Bool → List Bool} (hw : w ∈ FP) :
    FPPred (fun q => Nat.fromBitsLE (w q)=0) :=
  (BinaryNat.lt_fppred hw (constFn_mem_FP (BinaryNatCode.encode 1))).of_iff (fun q => by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)

theorem sub_binary {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) :
    BinaryFn (fun c => f c-g c) := by
  apply BinaryFn.of_bits
  refine mem_FP_of_eq (mem_FP_comp (mem_FP_pair hf.bits_mem_FP hg.bits_mem_FP) BinaryNat.sub_mem_FP) (fun c => ?_)
  simp only [Function.comp_apply, BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem oneEvaluator : SpaceFunction (coefficient (fun _ => (1 : Polynomial Coefficient))) := by
  let oneValue := fun q => BinaryNat.mod (pair (BinaryNatCode.encode 1) (BinaryNat.succ (modulus q)))
  have ho : oneValue ∈ FP := mem_FP_comp
    (f := fun q => pair (BinaryNatCode.encode 1) (BinaryNat.succ (modulus q))) (g := BinaryNat.mod)
    (mem_FP_pair (constFn_mem_FP (BinaryNatCode.encode 1))
      (mem_FP_comp (f := modulus) (g := BinaryNat.succ) modulus_FP BinaryNat.succ_mem_FP)) BinaryNat.mod_mem_FP
  have hmask := (zeroWord_fppred target_FP).and (zeroWord_fppred alpha_FP)
  have R := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (target q)=0 ∧ Nat.fromBitsLE (alpha q)=0))
    hmask.flag_mem_FP (SpaceFunction.ofFP oneValue ho) (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  refine R.congr (funext fun q => ?_)
  simp only [decide_eq_true_eq, coefficient, SymbolicFixedTableEntryBits.coefficient]
  change _ = SymbolicFixedTableEntryBits.integerResidue
    (((1 : Polynomial Coefficient).coeff (Nat.fromBitsLE (target q))).coeff (Nat.fromBitsLE (alpha q)))
    (Nat.fromBitsLE (modulus q)+1)
  by_cases ht : Nat.fromBitsLE (target q)=0 <;> by_cases ha : Nat.fromBitsLE (alpha q)=0
  · simp only [ht, ha, and_self, ite_true, coeff_one_zero, oneValue, BinaryNat.mod_pair,
      BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits, SymbolicFixedTableEntryBits.integerResidue,
      residueBits, BinaryNatCode.encode, Int.cast_one, ZMod.val_one_eq_one_mod]
  all_goals simp [ht, ha, coeff_one, SymbolicFixedTableEntryBits.integerResidue, residueBits, BinaryNatCode.encode]

theorem gcdEvaluator (p : List Bool → Polynomial Coefficient) (E : List Bool → ℕ)
    (hE : ∀ c k, ((p c).coeff k).natDegree ≤ E c)
    (hD : BinaryFn (fun c => (p c).natDegree)) (hK : BinaryFn (fun c => SymbolicScaledSquarefree.degree (p c)))
    (hB : BinaryFn E) (P : SpaceFunction (coefficient p)) :
    SpaceFunction (coefficient (fun c => SymbolicScaledSquarefree.gcd (p c))) := by
  have hz : FPPred (fun c => (p c).natDegree=0) :=
    (zeroWord_fppred hD.bits_mem_FP).of_iff (fun c => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits])
  have hm : BinaryFn (gcdFamily p).leftDegree := by
    apply BinaryFn.of_bits
    have H := hz.ite_mem_FP (constFn_mem_FP (BinaryNatCode.encode 1)) hD.bits_mem_FP
    refine mem_FP_of_eq H (fun c => ?_)
    dsimp only [gcdFamily]
    split_ifs <;> rfl
  have hn : BinaryFn (gcdFamily p).rightDegree := sub_binary hD (BinaryFn.const 1)
  have G := (gcdFamily p).evaluator E hE (fun c k => derivative_inner_degree (p c) (E c) (hE c) k)
    hm hn hK hB P (derivativeEvaluator p P)
  have R := SpaceFunction.branch (fun q => decide ((p (original q)).natDegree=0))
    (hz.comp original_FP).flag_mem_FP oneEvaluator G
  refine R.congr (funext fun q => ?_)
  simp only [decide_eq_true_eq, SymbolicCoefficientFormBits.Family.value, coefficient,
    SymbolicFixedTableEntryBits.coefficient]
  change (if (p (original q)).natDegree=0 then _ else _) =
    SymbolicFixedTableEntryBits.integerResidue
      (((SymbolicScaledSquarefree.gcd (p (original q))).coeff (Nat.fromBitsLE (target q))).coeff
        (Nat.fromBitsLE (alpha q))) (Nat.fromBitsLE (modulus q)+1)
  by_cases hd : (p (original q)).natDegree=0
  · simp only [original] at hd
    simp only [original, modulus, alpha, target, hd, ite_true, SymbolicScaledSquarefree.gcd]
  · simp only [original] at hd
    simp only [original, modulus, alpha, target, hd, ite_false, SymbolicScaledSquarefree.gcd, gcdFamily, natDegree_derivative]

noncomputable def quotientFamily (p : List Bool → Polynomial Coefficient) : SymbolicScaledQuotientBits.Family where
  divisor c := SymbolicScaledSquarefree.gcd (p c)
  dividend := p
  divisorDegree c := SymbolicScaledSquarefree.degree (p c)
  quotientDegree c := (p c).natDegree-SymbolicScaledSquarefree.degree (p c)

/-- This is a native leaf routine on a context retaining exact degree and GCD
order metadata. Both determinant levels account for the original reader. -/
theorem evaluator (p : List Bool → Polynomial Coefficient) (E : List Bool → ℕ)
    (hE : ∀ c k, ((p c).coeff k).natDegree ≤ E c)
    (hD : BinaryFn (fun c => (p c).natDegree)) (hK : BinaryFn (fun c => SymbolicScaledSquarefree.degree (p c)))
    (hB : BinaryFn E) (P : SpaceFunction (coefficient p)) :
    SpaceFunction (coefficient (fun c => SymbolicScaledSquarefree.polynomial (p c))) := by
  let B := fun c => (2*(p c).natDegree+1)*E c
  have hG c k : ((SymbolicScaledSquarefree.gcd (p c)).coeff k).natDegree ≤ B c :=
    (gcd_inner_degree (p c) (E c) (hE c) k).trans (by dsimp [B]; nlinarith)
  have hP c k : ((p c).coeff k).natDegree ≤ B c := (hE c k).trans (by dsimp [B]; nlinarith)
  have hb : BinaryFn B := (((BinaryFn.const 2).mul hD).add (BinaryFn.const 1)).mul hB
  exact (quotientFamily p).evaluator B hG hP hK (sub_binary hD hK) hb (gcdEvaluator p E hE hD hK hB P) P

end LeanCanny.Algebra.SymbolicSquarefreeBits
