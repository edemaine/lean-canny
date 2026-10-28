/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalSubstitutionResidue
public import LeanCanny.Algebra.RationalSubstitutionSignWith
public import LeanCanny.Algebra.IndexedRationalSubstitutionBounds
public import LeanCanny.Algebra.FixedWidthPolynomialLayout
public import LeanCanny.Computation.PolyTimeBinaryNat
public import LeanCanny.Algebra.PrimitivePairSpace

/-! # Native rational substitution of implicit fixed-width polynomials

The dense source is streamed by binary monomial rank. Arity and exponent
width are unary, while term counts and all clearing bounds are binary.
The source and coordinate coefficient programs are charged by the existing
denominator-clearing machine. Fixed even powers preserve zeros and signs.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedWidthRationalSubstitutionBits
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial MatrixPower
open RationalSubstitution.Indexed
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

structure Family where
  arity : List Bool → ℕ
  width : List Bool → ℕ
  source : (c : List Bool) → MvPolynomial (Fin (arity c)) ℤ
  numerator : List Bool → ℕ → Polynomial ℤ
  denominator : List Bool → ℕ → Polynomial ℤ
  degree_fit : ∀ c i, (source c).degreeOf i < 2 ^ width c

def Family.grid (F : Family) (c : List Bool) : ℕ := 2 ^ F.width c
def Family.terms (F : Family) (c : List Bool) : ℕ := count (F.arity c) (F.width c)
noncomputable def Family.coefficient (F : Family) (c : List Bool) (r : ℕ) : ℤ :=
  (F.source c).coeff (exponentVector (F.arity c) (entry (F.width c) r))

noncomputable def Family.indexed (F : Family) : RationalSubstitution.IntegerBits.Family where
  arity := F.arity
  width c := 2 * F.grid c
  terms := F.terms
  coefficient := F.coefficient
  exponent c := entry (F.width c)
  numerator := F.numerator
  denominator := F.denominator
  exponent_le c _ _ i _ := (entry_lt (F.width c) _ i).le.trans (by unfold Family.grid; omega)

noncomputable def Family.polynomial (F : Family) (c : List Bool) : Polynomial ℤ :=
  RationalSubstitution.clearedWith (fun _ => F.grid c) (F.source c)
    (fun i => F.numerator c i.val) (fun i => F.denominator c i.val)

theorem Family.source_eq (F : Family) (c : List Bool) :
    RationalSubstitution.Indexed.source (F.arity c) (F.terms c) (F.coefficient c) (entry (F.width c)) = F.source c :=
  indexed_source_eq _ _ _ (fun _ hm i => (MvPolynomial.monomial_le_degreeOf i hm).trans_lt (F.degree_fit c i))

theorem Family.polynomial_eq (F : Family) (c : List Bool) : F.indexed.polynomial c = F.polynomial c := by
  unfold RationalSubstitution.IntegerBits.Family.polynomial
  rw [Family.indexed, cleared_eq_clearedWith_source, F.source_eq]
  rfl

structure Access (F : Family) where
  arity : UnaryFn F.arity
  width : UnaryFn F.width
  coefficient : List Bool → List Bool
  evaluator : SpaceFunction coefficient
  coefficient_eq : ∀ c r m, 0 < m →
    coefficient (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      residueBits ((F.coefficient c r : ℤ) : ZMod m)
  coordinates : RationalSubstitution.IntegerBits.CoordinateReaders F.arity F.numerator F.denominator

noncomputable def Access.indexed {F : Family} (A : Access F) : RationalSubstitution.IntegerBits.Access F.indexed where
  arity c := BinaryNatCode.encode (F.arity c)
  width c := BinaryNatCode.encode (2 * F.grid c)
  terms := countCode F.arity F.width
  exponent := exponentRead F.arity F.width
  coefficient := A.coefficient
  numerator := A.coordinates.numerator
  denominator := A.coordinates.denominator
  arity_eq _ := Nat.fromBitsLE_bits _
  width_eq _ := Nat.fromBitsLE_bits _
  terms_eq c := by rw [countCode_code]; exact Nat.fromBitsLE_bits _
  exponent_eq c r _ i hi := by
    rw [exponentRead_packet F.arity F.width c r i (show i < F.arity c from hi)]
    exact Nat.fromBitsLE_bits _
  coefficient_eq c r _ m hm := A.coefficient_eq c r m hm
  numerator_eq := A.coordinates.numerator_eq
  denominator_eq := A.coordinates.denominator_eq

theorem Access.grid_binary {F : Family} (A : Access F) : BinaryFn F.grid :=
  (BinaryFn.const 2).powUnary A.width

theorem Access.terms_binary {F : Family} (A : Access F) : BinaryFn F.terms :=
  BinaryFn.of_bits (mem_FP_of_eq (countCode_mem_FP A.arity A.width) (countCode_code F.arity F.width))

theorem Access.polynomialEvaluator {F : Family} (A : Access F) :
    SpaceFunction (PrimitivePairBits.coefficient F.polynomial) := by
  have R := A.indexed.evaluator
    ⟨(BinaryFn.ofUnary A.arity).bits_mem_FP, ((BinaryFn.const 2).mul A.grid_binary).bits_mem_FP,
      countCode_mem_FP A.arity A.width, exponentRead_mem_FP A.arity A.width⟩
    A.evaluator A.coordinates.numeratorEvaluator A.coordinates.denominatorEvaluator
  exact R.congr (funext fun q => by
    simp only [RationalSubstitution.IntegerBits.Family.value, Family.polynomial_eq, PrimitivePairBits.coefficient])

theorem Family.eval {K : Type*} [Field K] [CharZero K] (F : Family) (c : List Bool) (theta : K)
    (hd : ∀ i : Fin (F.arity c), (F.denominator c i.val).eval₂ (Int.castRingHom K) theta ≠ 0) :
    (F.polynomial c).eval₂ (Int.castRingHom K) theta =
      (∏ i : Fin (F.arity c), (F.denominator c i.val).eval₂ (Int.castRingHom K) theta ^ (2 * F.grid c)) *
        (F.source c).eval₂ (Int.castRingHom K)
          (fun i => (F.numerator c i.val).eval₂ (Int.castRingHom K) theta /
            (F.denominator c i.val).eval₂ (Int.castRingHom K) theta) :=
  RationalSubstitution.eval₂_clearedWith _ _ _ _ _ _ (fun i => (F.degree_fit c i).le) hd

theorem Family.zero_iff {K : Type*} [Field K] [CharZero K] (F : Family) (c : List Bool) (theta : K)
    (hd : ∀ i : Fin (F.arity c), (F.denominator c i.val).eval₂ (Int.castRingHom K) theta ≠ 0) :
    (F.polynomial c).eval₂ (Int.castRingHom K) theta = 0 ↔
      (F.source c).eval₂ (Int.castRingHom K)
        (fun i => (F.numerator c i.val).eval₂ (Int.castRingHom K) theta /
          (F.denominator c i.val).eval₂ (Int.castRingHom K) theta) = 0 := by
  rw [F.eval c theta hd, mul_eq_zero]
  have hprod : (∏ i : Fin (F.arity c), (F.denominator c i.val).eval₂ (Int.castRingHom K) theta ^ (2 * F.grid c)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hd i))
  simp only [hprod, false_or]

theorem Family.sign (F : Family) (c : List Bool) (theta : ℝ)
    (hd : ∀ i : Fin (F.arity c), (F.denominator c i.val).eval₂ (Int.castRingHom ℝ) theta ≠ 0) :
    SignType.sign ((F.polynomial c).eval₂ (Int.castRingHom ℝ) theta) =
      SignType.sign ((F.source c).eval₂ (Int.castRingHom ℝ)
        (fun i => (F.numerator c i.val).eval₂ (Int.castRingHom ℝ) theta /
          (F.denominator c i.val).eval₂ (Int.castRingHom ℝ) theta)) :=
  RationalSubstitution.sign_eval₂_clearedWith _ _ _ _ _ _ (fun i => (F.degree_fit c i).le) hd

def Family.degree (F : Family) (E : List Bool → ℕ) (c : List Bool) : ℕ := F.arity c * (2 * F.grid c) * E c
def Family.mass (F : Family) (b s : List Bool → ℕ) (c : List Bool) : ℕ :=
  (F.terms c).size + b c + F.arity c * (2 * F.grid c) * s c

theorem Family.polynomial_degree (F : Family) (E : List Bool → ℕ)
    (hn : ∀ c i, i < F.arity c → (F.numerator c i).natDegree ≤ E c)
    (hd : ∀ c i, i < F.arity c → (F.denominator c i).natDegree ≤ E c) (c : List Bool) :
    (F.polynomial c).natDegree ≤ F.degree E c := by
  rw [← F.polynomial_eq]
  exact natDegree_cleared_le _ _ _ _ _ _ _ _ (F.indexed.exponent_le c) (hn c) (hd c)

theorem Family.polynomial_mass (F : Family) (b s : List Bool → ℕ)
    (hc : ∀ c r, r < F.terms c → (F.coefficient c r).natAbs ≤ 2 ^ b c)
    (hn : ∀ c i, i < F.arity c → coefficientMass (F.numerator c i) ≤ 2 ^ s c)
    (hd : ∀ c i, i < F.arity c → coefficientMass (F.denominator c i) ≤ 2 ^ s c) (c : List Bool) :
    coefficientMass (F.polynomial c) ≤ 2 ^ F.mass b s c := by
  rw [← F.polynomial_eq]
  exact coefficientMass_cleared_le_pow _ _ _ _ _ _ _ _ _ (F.indexed.exponent_le c) (hc c) (hn c) (hd c)

theorem Access.degree_binary {F : Family} (A : Access F) {E : List Bool → ℕ} (hE : BinaryFn E) : BinaryFn (F.degree E) :=
  ((BinaryFn.ofUnary A.arity).mul ((BinaryFn.const 2).mul A.grid_binary)).mul hE

theorem Access.mass_binary {F : Family} (A : Access F) {b s : List Bool → ℕ} (hb : BinaryFn b) (hs : BinaryFn s) :
    BinaryFn (F.mass b s) :=
  (A.terms_binary.size.add hb).add (((BinaryFn.ofUnary A.arity).mul ((BinaryFn.const 2).mul A.grid_binary)).mul hs)

end LeanCanny.Algebra.FixedWidthRationalSubstitutionBits
