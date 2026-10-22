/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteLeafCoordinateCorrect
public import LeanCanny.Algebra.RationalSubstitutionWith

/-! # Filtering the computed leaf coordinates by polynomial constraints

Even denominator clearing preserves zeros and real signs at parameter roots.
The resulting scalar-root criterion uses the coordinates with native readers,
rather than assuming coefficient access to the earlier flattened polynomials.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteLeafCoordinateBits
open Polynomial
open LeanCanny.Encoding
open SeparableBits (Family)
open scoped BigOperators

variable (B : Family) (count D b : List Bool → ℕ)
variable (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
variable (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
variable (hheight : ∀ c i, i < count c → B.height (pair c (BinaryNatCode.encode i)) ≤ b c)

noncomputable def numerator (c : List Bool) (i : Fin (count c)) : ℤ[X] :=
  (coordinate B count D b hne (pair c (BinaryNatCode.encode i.val))).numerator

noncomputable def denominator (c : List Bool) (i : Fin (count c)) : ℤ[X] :=
  (coordinate B count D b hne (pair c (BinaryNatCode.encode i.val))).denominator

noncomputable def constraint (c : List Bool) (A : Fin (count c) → ℕ) (f : MvPolynomial (Fin (count c)) ℤ) : ℤ[X] :=
  RationalSubstitution.clearedWith A f (numerator B count D b hne c) (denominator B count D b hne c)

variable {K : Type*} [Field K] [CharZero K]

include hdegree hheight in
theorem constraint_eval (c : List Bool) (A : Fin (count c) → ℕ) (f : MvPolynomial (Fin (count c)) ℤ)
    (hA : ∀ i, f.degreeOf i ≤ A i) (theta : K)
    (ht : (FiniteAnnihilatorBits.finiteParameter B count hne c).eval₂ (Int.castRingHom K) theta = 0) :
    (constraint B count D b hne c A f).eval₂ (Int.castRingHom K) theta =
      (∏ i, (denominator B count D b hne c i).eval₂ (Int.castRingHom K) theta ^ (2 * A i)) *
        f.eval₂ (Int.castRingHom K)
          (FiniteAnnihilatorTree.decode (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c) theta) := by
  rw [constraint, RationalSubstitution.eval₂_clearedWith _ _ A f
    (numerator B count D b hne c) (denominator B count D b hne c) hA
    (fun i => (finite_decode_spec B count D b hne hdegree hheight c i theta ht).1)]
  congr 1
  exact congrArg (fun x : Fin (count c) → K => f.eval₂ (Int.castRingHom K) x)
    (funext fun i => (finite_decode_spec B count D b hne hdegree hheight c i theta ht).2)

include hdegree hheight in
theorem constraint_zero_iff (c : List Bool) (A : Fin (count c) → ℕ) (f : MvPolynomial (Fin (count c)) ℤ)
    (hA : ∀ i, f.degreeOf i ≤ A i) (theta : K)
    (ht : (FiniteAnnihilatorBits.finiteParameter B count hne c).eval₂ (Int.castRingHom K) theta = 0) :
    (constraint B count D b hne c A f).eval₂ (Int.castRingHom K) theta = 0 ↔
      f.eval₂ (Int.castRingHom K)
        (FiniteAnnihilatorTree.decode (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c) theta) = 0 := by
  have hf : (∏ i, (denominator B count D b hne c i).eval₂ (Int.castRingHom K) theta ^ (2 * A i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (finite_decode_spec B count D b hne hdegree hheight c i theta ht).1)
  rw [constraint_eval B count D b hne hdegree hheight c A f hA theta ht]
  simp only [mul_eq_zero, hf, false_or]

include hdegree hheight in
theorem constraint_sign (c : List Bool) (A : Fin (count c) → ℕ) (f : MvPolynomial (Fin (count c)) ℤ)
    (hA : ∀ i, f.degreeOf i ≤ A i) (theta : ℝ)
    (ht : (FiniteAnnihilatorBits.finiteParameter B count hne c).eval₂ (Int.castRingHom ℝ) theta = 0) :
    SignType.sign ((constraint B count D b hne c A f).eval₂ (Int.castRingHom ℝ) theta) =
      SignType.sign (f.eval₂ (Int.castRingHom ℝ)
        (FiniteAnnihilatorTree.decode (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c) theta)) := by
  have hf : 0 < ∏ i, (denominator B count D b hne c i).eval₂ (Int.castRingHom ℝ) theta ^ (2 * A i) := by
    apply Finset.prod_pos
    intro i _
    rw [pow_mul]
    exact pow_pos (sq_pos_of_ne_zero (finite_decode_spec B count D b hne hdegree hheight c i theta ht).1) _
  rw [constraint_eval B count D b hne hdegree hheight c A f hA theta ht, sign_mul, sign_pos hf, one_mul]

include hdegree hheight in
theorem exists_system_iff (c : List Bool) {τ : Type*} (A : τ → Fin (count c) → ℕ)
    (f : τ → MvPolynomial (Fin (count c)) ℤ) (hA : ∀ t i, (f t).degreeOf i ≤ A t i)
    (ha : ∀ x : Fin (count c) → K, (∀ t, (f t).eval₂ (Int.castRingHom K) x = 0) →
      ∀ i, (B.polynomial (pair c (BinaryNatCode.encode i.val))).eval₂ (Int.castRingHom K) (x i) = 0) :
    (∃ x : Fin (count c) → K, ∀ t, (f t).eval₂ (Int.castRingHom K) x = 0) ↔
      ∃ theta : K, (FiniteAnnihilatorBits.finiteParameter B count hne c).eval₂ (Int.castRingHom K) theta = 0 ∧
        ∀ t, (constraint B count D b hne c (A t) (f t)).eval₂ (Int.castRingHom K) theta = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    have hp := ha x hx
    let theta := FiniteAnnihilatorTree.encode (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c) x
    have ht := FiniteAnnihilatorTree.encode_root (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c) x hp
    refine ⟨theta, ht, fun t => ?_⟩
    apply (constraint_zero_iff B count D b hne hdegree hheight c (A t) (f t) (hA t) theta ht).mpr
    rw [FiniteAnnihilatorTree.decode_encode _ _ _ x hp]
    exact hx t
  · rintro ⟨theta, ht, hf⟩
    refine ⟨FiniteAnnihilatorTree.decode _ _ (hne c) theta, fun t => ?_⟩
    exact (constraint_zero_iff B count D b hne hdegree hheight c (A t) (f t) (hA t) theta ht).mp (hf t)

end LeanCanny.Algebra.FiniteLeafCoordinateBits
