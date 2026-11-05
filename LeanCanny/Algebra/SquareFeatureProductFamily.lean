/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.MvCoefficientMass
public import LeanCanny.Algebra.SquareFeatureProductPositive
public import LeanCanny.Algebra.FixedWidthRowArithmetic
/-! # Literal formal feature products and input-only size bounds

The coefficient ring remains integer multivariate polynomials. Real-center
specialization is performed only after the original degree/mass estimates.
-/
@[expose] public section
namespace LeanCanny.Algebra.SquareFeatureProductFamily
open MvPolynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical BigOperators

structure Family where
  arity : List Bool → ℕ
  count : List Bool → ℕ
  degree : List Bool → ℕ
  mass : List Bool → ℕ
  feature : (c : List Bool) → ℕ → MvPolynomial (Fin (arity c)) ℤ
  feature_degree : ∀ c i, i < count c → (feature c i).totalDegree ≤ degree c
  feature_mass : ∀ c i, i < count c → MvMass.mass (feature c i) ≤ 2^mass c

noncomputable def inputWidth (F : Family) (c : List Bool) := (F.degree c+1).size
noncomputable def degree (F : Family) (c : List Bool) := F.count c*(2*F.degree c+1)
noncomputable def mass (F : Family) (c : List Bool) := F.count c*(2*F.mass c+1)
noncomputable def width (F : Family) (c : List Bool) := (degree F c+1).size
noncomputable def factor (F : Family) (c : List Bool) (i : ℕ) : MvPolynomial (Fin (F.arity c+1)) ℤ :=
  X 0 + (rename Fin.succ (F.feature c i))^2
noncomputable def polynomial (F : Family) (c : List Bool) : MvPolynomial (Fin (F.arity c+1)) ℤ :=
  ∏ i ∈ Finset.range (F.count c), factor F c i

private theorem totalDegree_prod_le {ι σ : Type*} (s : Finset ι) (p : ι → MvPolynomial σ ℤ) :
    (∏ i ∈ s, p i).totalDegree ≤ ∑ i ∈ s, (p i).totalDegree := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact (totalDegree_mul _ _).trans (Nat.add_le_add_left ih _)

theorem factor_degree (F : Family) (c : List Bool) (i : ℕ) (hi : i<F.count c) :
    (factor F c i).totalDegree ≤ 2*F.degree c+1 := by
  have HF := (totalDegree_rename_le Fin.succ (F.feature c i)).trans (F.feature_degree c i hi)
  have HS := (totalDegree_pow (rename Fin.succ (F.feature c i)) 2).trans (Nat.mul_le_mul_left 2 HF)
  exact (totalDegree_add _ _).trans (max_le (by simp) (by omega))

theorem polynomial_degree (F : Family) (c : List Bool) : (polynomial F c).totalDegree ≤ degree F c := by
  unfold polynomial degree
  exact (totalDegree_prod_le _ _).trans ((Finset.sum_le_sum (fun i hi =>
    factor_degree F c i (Finset.mem_range.mp hi))).trans_eq (by simp))

theorem factor_mass (F : Family) (c : List Bool) (i : ℕ) (hi : i<F.count c) :
    MvMass.mass (factor F c i) ≤ 2^(2*F.mass c+1) := by
  have HF := (MvMass.rename_le Fin.succ (F.feature c i)).trans (F.feature_mass c i hi)
  have HS := (MvMass.pow_le (rename Fin.succ (F.feature c i)) 2).trans (Nat.pow_le_pow_left HF 2)
  have HE : (2^F.mass c)^2 = 2^(2*F.mass c) := by rw [←pow_mul, Nat.mul_comm]
  have HB : 0<2^(2*F.mass c) := by positivity
  calc
    _ ≤ 1+(2^F.mass c)^2 := (MvMass.add_le _ _).trans (by simpa only [MvMass.X] using Nat.add_le_add_left HS 1)
    _ = 1+2^(2*F.mass c) := by rw [HE]
    _ ≤ 2^(2*F.mass c+1) := by rw [pow_succ]; omega

theorem polynomial_mass (F : Family) (c : List Bool) : MvMass.mass (polynomial F c) ≤ 2^mass F c := by
  unfold polynomial mass
  calc
    _ ≤ ∏ i ∈ Finset.range (F.count c), MvMass.mass (factor F c i) := MvMass.prod_le _ _
    _ ≤ ∏ _i ∈ Finset.range (F.count c), 2^(2*F.mass c+1) :=
      Finset.prod_le_prod (fun i hi => factor_mass F c i (Finset.mem_range.mp hi))
    _ = _ := by simp [←pow_mul, Nat.mul_comm]

theorem fit (F : Family) (c : List Bool) : (polynomial F c).totalDegree < 2^width F c := by
  exact (polynomial_degree F c).trans_lt ((Nat.lt_succ_self _).trans (Nat.lt_size_self _))

structure Access (F : Family) where
  arity : UnaryFn F.arity
  count : BinaryFn F.count
  degree : BinaryFn F.degree
  mass : BinaryFn F.mass
  coefficient : List Bool → List Bool
  evaluator : SpaceFunction coefficient
  packet : ∀ c i, i<F.count c → ∀ bits modulus,
    coefficient (pair (pair (pair c (BinaryNatCode.encode i)) bits) modulus) =
      residueBits (((F.feature c i).coeff (nativeExponent (Equiv.refl _) (inputWidth F c) (Nat.fromBitsLE bits)) : ℤ) :
        ZMod (Nat.fromBitsLE modulus+1))

theorem degree_binary (F : Family) (A : Access F) : BinaryFn (degree F) := A.count.mul
  (((BinaryFn.const 2).mul A.degree).add (BinaryFn.const 1))
theorem mass_binary (F : Family) (A : Access F) : BinaryFn (mass F) := A.count.mul
  (((BinaryFn.const 2).mul A.mass).add (BinaryFn.const 1))
theorem inputWidth_unary (F : Family) (A : Access F) : UnaryFn (inputWidth F) :=
  (UnaryFn.length (A.degree.add (BinaryFn.const 1)).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
theorem width_unary (F : Family) (A : Access F) : UnaryFn (width F) :=
  (UnaryFn.length ((degree_binary F A).add (BinaryFn.const 1)).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)

end LeanCanny.Algebra.SquareFeatureProductFamily
