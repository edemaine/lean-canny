/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitivePairReaders
public import Mathlib.Algebra.Polynomial.Reverse
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Native coefficient access after fixed-degree reciprocal reflection

A binary degree allowance determines reflection. Each requested coefficient
is zero or one original coefficient, so the original space reader is charged
without needing the polynomial's actual degree.
-/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialReflectBits
open LeanCanny.Encoding LeanCanny.Computation
open RationalSubstitution.IntegerBits (context selectedDegree mValue coefficientResidue)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryNat.add BinaryNat.sub

noncomputable def polynomial (p : List Bool → Polynomial ℤ) (D : List Bool → ℕ) (c : List Bool) : Polynomial ℤ :=
  Polynomial.X * (p c).reflect (D c)

lemma coefficient_eq {R : Type*} [Semiring R] (p : Polynomial R) (D : ℕ) (hp : p.natDegree ≤ D) (j : ℕ) :
    (Polynomial.X * p.reflect D).coeff j = if 0 < j ∧ j ≤ D + 1 then p.coeff (D + 1 - j) else 0 := by
  cases j with
  | zero => simp
  | succ j =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_reflect]
    by_cases hj : j ≤ D
    · rw [Polynomial.revAt_le hj, ite_eq_left (by omega)]
      congr 1
      omega
    · rw [Polynomial.revAt_eq_self_of_lt (by omega), ite_eq_right (by omega)]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

def valid (D : List Bool → ℕ) (q : List Bool) : Prop :=
  0 < Nat.fromBitsLE (selectedDegree q) ∧ Nat.fromBitsLE (selectedDegree q) ≤ D (context q) + 1

instance (D : List Bool → ℕ) : DecidablePred (valid D) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

private theorem context_FP : context ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
private theorem degree_FP : selectedDegree ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

theorem valid_FP {D : List Bool → ℕ} (hD : BinaryFn D) : FPPred (valid D) := by
  have hpos := BinaryNat.lt_fppred (constFn_mem_FP []) degree_FP
  have hc : BinaryFn (fun q => D (context q)) := hD.comp context_FP
  have hbound := BinaryNat.le_fppred degree_FP ((hc.add (BinaryFn.const 1)).bits_mem_FP)
  exact (hpos.and hbound).of_iff (fun q => by simp only [valid, show Nat.fromBitsLE [] = 0 from rfl, BinaryNatCode.encode, Nat.fromBitsLE_bits])

def query (D : List Bool → ℕ) (q : List Bool) : List Bool :=
  pair (pair (context q) (BinaryNat.sub (pair (BinaryNatCode.encode (D (context q) + 1)) (selectedDegree q)))) (pairSnd q)

theorem query_FP {D : List Bool → ℕ} (hD : BinaryFn D) : query D ∈ FP := by
  have hc : BinaryFn (fun q => D (context q)) := hD.comp context_FP
  have hd := (hc.add (BinaryFn.const 1)).bits_mem_FP
  exact mem_FP_pair (mem_FP_pair context_FP (mem_FP_comp (mem_FP_pair hd degree_FP) BinaryNat.sub_mem_FP)) pairSnd_mem_FP

noncomputable def value (p : List Bool → Polynomial ℤ) (D : List Bool → ℕ) (q : List Bool) : List Bool :=
  if valid D q then PrimitivePairBits.coefficient p (query D q) else []

theorem value_eq (p : List Bool → Polynomial ℤ) (D : List Bool → ℕ)
    (hp : ∀ c, (p c).natDegree ≤ D c) (q : List Bool) :
    value p D q = PrimitivePairBits.coefficient (polynomial p D) q := by
  unfold value PrimitivePairBits.coefficient polynomial
  rw [coefficient_eq _ _ (hp _)]
  unfold valid
  by_cases hq : 0 < Nat.fromBitsLE (selectedDegree q) ∧ Nat.fromBitsLE (selectedDegree q) ≤ D (context q) + 1
  · rw [ite_eq_left hq, ite_eq_left hq]
    simp only [query, context, selectedDegree, mValue, pairFst_pair, pairSnd_pair, BinaryNat.sub_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
  · rw [ite_eq_right hq, ite_eq_right hq]
    simp [coefficientResidue, MatrixPower.residueBits, BinaryNatCode.encode]

/-- A space-bounded original reader and a binary allowance suffice on all
raw query words, including zero and out-of-range coefficient requests. -/
theorem evaluator (p : List Bool → Polynomial ℤ) (D : List Bool → ℕ)
    (hp : ∀ c, (p c).natDegree ≤ D c) (hD : BinaryFn D)
    (E : SpaceFunction (PrimitivePairBits.coefficient p)) :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial p D)) := by
  have h := SpaceFunction.branch (fun q => decide (valid D q)) (valid_FP hD).flag_mem_FP
    (E.precompose (query D) (query_FP hD)) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact h.congr (funext fun q => by
    simpa only [Function.comp_apply, decide_eq_true_eq, value] using value_eq p D hp q)

end LeanCanny.Algebra.PolynomialReflectBits
