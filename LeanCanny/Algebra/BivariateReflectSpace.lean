/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialReflectSpace
public import LeanCanny.Algebra.SymbolicFixedTableEntrySpace

/-! # Native bivariate coefficients after reciprocal reflection

The inner parameter degree is retained. The outer coefficient index is zero
or one original index determined by a binary degree allowance. No actual
degree scan or integer coefficient reconstruction is needed.
-/

@[expose] public section
namespace LeanCanny.Algebra.BivariateReflectBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryNat.sub

def base (q : List Bool) := pairFst (pairFst q)
def inner (q : List Bool) := pairFst (pairSnd q)
def outer (q : List Bool) := pairSnd (pairSnd q)
lemma base_FP : base ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
lemma inner_FP : inner ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
lemma outer_FP : outer ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

def valid (D : List Bool → ℕ) (q : List Bool) : Prop :=
  0 < Nat.fromBitsLE (outer q) ∧ Nat.fromBitsLE (outer q) ≤ D (base q) + 1
instance (D : List Bool → ℕ) : DecidablePred (valid D) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

lemma valid_FP {D : List Bool → ℕ} (hD : BinaryFn D) : FPPred (valid D) := by
  have ho := BinaryFn.fromBits outer_FP
  have hd : BinaryFn (fun q => D (base q) + 1) := (hD.add (BinaryFn.const 1)).comp base_FP
  exact (((BinaryFn.const 0).lt ho).and (ho.le hd)).of_iff (fun _ => Iff.rfl)

def query (D : List Bool → ℕ) (q : List Bool) : List Bool :=
  pair (pairFst q) (pair (inner q)
    (BinaryNat.sub (pair (BinaryNatCode.encode (D (base q) + 1)) (outer q))))

lemma query_FP {D : List Bool → ℕ} (hD : BinaryFn D) : query D ∈ FP := by
  have hd := mem_FP_comp base_FP (hD.add (BinaryFn.const 1)).bits_mem_FP
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair inner_FP
    (mem_FP_comp (mem_FP_pair hd outer_FP) BinaryNat.sub_mem_FP))

noncomputable def polynomial (p : List Bool → Polynomial (Polynomial ℤ)) (D : List Bool → ℕ)
    (c : List Bool) : Polynomial (Polynomial ℤ) := Polynomial.X * (p c).reflect (D c)

/-- Native access to the nested determinant transfers to its reflected
annihilator with the same original source costs. -/
theorem evaluator (p : List Bool → Polynomial (Polynomial ℤ)) (D : List Bool → ℕ)
    (hp : ∀ c, (p c).natDegree ≤ D c) (hD : BinaryFn D)
    (E : SpaceFunction (SymbolicFixedTableEntryBits.coefficient p)) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient (polynomial p D)) := by
  have R := SpaceFunction.branch (fun q => decide (valid D q)) (valid_FP hD).flag_mem_FP
    (E.precompose (query D) (query_FP hD)) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine R.congr (funext fun q => ?_)
  simp only [decide_eq_true_eq, Function.comp_apply]
  by_cases hq : valid D q
  · rw [ite_eq_left hq]
    simp only [SymbolicFixedTableEntryBits.coefficient, polynomial]
    rw [PolynomialReflectBits.coefficient_eq _ _ (hp _)]
    rw [ite_eq_left (show 0 < Nat.fromBitsLE (pairSnd (pairSnd q)) ∧
      Nat.fromBitsLE (pairSnd (pairSnd q)) ≤ D (pairFst (pairFst q)) + 1 from hq)]
    simp only [query, base, inner, outer, pairFst_pair, pairSnd_pair,
      BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  · rw [ite_eq_right hq]
    simp only [SymbolicFixedTableEntryBits.coefficient, polynomial]
    rw [PolynomialReflectBits.coefficient_eq _ _ (hp _)]
    rw [ite_eq_right (show ¬(0 < Nat.fromBitsLE (pairSnd (pairSnd q)) ∧
      Nat.fromBitsLE (pairSnd (pairSnd q)) ≤ D (pairFst (pairFst q)) + 1) from hq)]
    simp [SymbolicFixedTableEntryBits.integerResidue, residueBits, BinaryNatCode.encode]

end LeanCanny.Algebra.BivariateReflectBits
