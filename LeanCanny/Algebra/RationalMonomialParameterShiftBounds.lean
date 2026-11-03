/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RationalMonomialParameterShiftReader
public import LeanCanny.Algebra.CommonDenominatorMass
/-! # Degree and mass budgets for actual denominator-cleared parameter shifts -/
@[expose] public section
namespace LeanCanny.Algebra.RationalMonomialParameterShift
open LeanCanny.Encoding LeanCanny.Computation RationalMonomialWindowQuery
open scoped BigOperators Classical

private theorem base_mass (F : Family) (c : List Bool) : MvMass.mass (base F c)≤2^F.scalars.mass c :=by
  unfold base FixedWidthMonomialBits.polynomial
  split_ifs
  · simpa only [MvMass.monomial] using F.scalars.numerator_bound c
  · simp

private theorem parameter_mass (F : Family) (negative : Bool) (c : List Bool) :
    MvMass.mass (parameterNumerator F negative c)≤2^(F.scalars.mass c+1) :=by
  have HD : MvMass.mass (MvPolynomial.C (F.scalars.denominator c)*
      (MvPolynomial.X 0 : MvPolynomial (Fin (F.arity c+1)) ℤ))≤2^F.scalars.mass c :=by
    exact (MvMass.mul_le _ _).trans (by simpa only [MvMass.C,MvMass.X,Nat.mul_one] using F.scalars.denominator_bound c)
  have HE : MvMass.mass (if negative then -(MvPolynomial.C (F.scalars.denominator c)*
      (MvPolynomial.X 0 : MvPolynomial (Fin (F.arity c+1)) ℤ))
      else MvPolynomial.C (F.scalars.denominator c)*MvPolynomial.X 0)≤2^F.scalars.mass c :=by
    cases negative <;> simpa only [Bool.false_eq_true,ite_true,ite_false,MvMass.neg] using HD
  have H:=(MvMass.add_le (MvPolynomial.rename Fin.succ (base F c))
    (if negative then -(MvPolynomial.C (F.scalars.denominator c)*MvPolynomial.X 0)
      else MvPolynomial.C (F.scalars.denominator c)*MvPolynomial.X 0)).trans
    (Nat.add_le_add ((MvMass.rename_le Fin.succ (base F c)).trans (base_mass F c)) HE)
  exact H.trans_eq (by rw [pow_succ];omega)

theorem numerator_mass (F : Family) (negative : Bool) (c : List Bool) (i : Fin (F.arity c+1)) :
    MvMass.mass (numerator F negative c i)≤2^(F.scalars.mass c+1) :=by
  refine Fin.cases (parameter_mass F negative c) (fun j=>?_) i
  change MvMass.mass (MvPolynomial.C (F.scalars.denominator c)*MvPolynomial.X j.succ)≤_
  exact (MvMass.mul_le _ _).trans
    (by simpa only [MvMass.C,MvMass.X,Nat.mul_one] using
      (F.scalars.denominator_bound c).trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)))

theorem mass (F : Family) (negative : Bool) (c : List Bool) (D H : ℕ)
    (p : MvPolynomial (Fin (F.arity c+1)) ℤ) (hp : p.totalDegree≤2*D) (hm : MvMass.mass p≤2^H) :
    MvMass.mass (clear F negative c D p)≤2^(H+2*D*(F.scalars.mass c+1)) :=by
  have HQ : (F.scalars.denominator c).natAbs≤2^(F.scalars.mass c+1) :=
    (F.scalars.denominator_bound c).trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
  exact ((CommonDenominatorSpecialization.mass _ _ _ _ hp _ HQ (numerator_mass F negative c)).trans
    (Nat.mul_le_mul_right _ hm)).trans_eq (by rw [←pow_mul,←pow_add];congr 1;ring)

def sourceDegree (F : Family) (W : List Bool→ℕ) (c : List Bool) :=(F.arity c+1)*2^W c

theorem source_degree (F : Family) (W : List Bool→ℕ)
    (p : (c : List Bool)→MvPolynomial (Fin (F.arity c+1)) ℤ)
    (hfit : ∀ c i,(p c).degreeOf i<2^W c) (c : List Bool) : (p c).totalDegree≤sourceDegree F W c :=by
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro e he
  change e.degree≤(F.arity c+1)*2^W c
  rw [Finsupp.degree_eq_sum]
  calc
    _≤∑ i : Fin (F.arity c+1),2^W c :=Finset.sum_le_sum (fun i _=>
      (MvPolynomial.monomial_le_degreeOf i he).trans ((hfit c i).le))
    _=_:=by simp

theorem sourceDegree_binary (F : Family) (W : List Bool→ℕ) (hA : UnaryFn F.arity) (hW : UnaryFn W) :
    BinaryFn (sourceDegree F W) :=
  ((BinaryFn.ofUnary hA).add (BinaryFn.const 1)).mul ((BinaryFn.const 2).powUnary hW)

def nativeTargetWidth (F : Family) (W : List Bool→ℕ) (c : List Bool) :=
  (sourceDegree F W c*(F.weight c+1)+(F.weight c+1)).size

theorem nativeTargetWidth_unary (F : Family) (W : List Bool→ℕ)
    (hA : UnaryFn F.arity) (hW : UnaryFn W) (hw : BinaryFn F.weight) : UnaryFn (nativeTargetWidth F W) :=
  (UnaryFn.length (((sourceDegree_binary F W hA hW).mul (hw.add (BinaryFn.const 1))).add
    (hw.add (BinaryFn.const 1))).bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)

theorem numerator_fit (F : Family) (W : List Bool→ℕ) (c : List Bool) :
    F.weight c+1<2^nativeTargetWidth F W c :=
  (Nat.le_add_left _ _).trans_lt (Nat.lt_size_self _)

theorem target_fit (F : Family) (W : List Bool→ℕ) (c : List Bool) :
    sourceDegree F W c*(F.weight c+1)<2^nativeTargetWidth F W c :=
  (Nat.le_add_right _ _).trans_lt (Nat.lt_size_self _)

theorem source_mass (F : Family) (negative : Bool) (W V : List Bool→ℕ)
    (p : (c : List Bool)→MvPolynomial (Fin (F.arity c+1)) ℤ) (hfit : ∀ c i,(p c).degreeOf i<2^W c)
    (H : ℕ) (c : List Bool) (hm : MvMass.mass (p c)≤2^H) :
    MvMass.mass ((sourceFamily F negative W V p hfit).polynomial c)≤
      2^(H+2*sourceDegree F W c*(F.scalars.mass c+1)) :=by
  rw [sourceFamily_polynomial]
  exact mass F negative c _ H _ ((source_degree F W p hfit c).trans (by dsimp [sourceDegree];omega)) hm

end LeanCanny.Algebra.RationalMonomialParameterShift
