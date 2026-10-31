/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PurePowerReductionCorrect

/-! # Pure-power reduction entries under additive coefficient maps

An old multiplication-matrix entry is an additive map of algebra elements,
not a ring homomorphism. Reduction entries only select or negate one lower
coefficient, so the existing native integer entry program applies to these
additive coefficient images without changing the reduction dimension.
-/

@[expose] public section
namespace LeanCanny.Algebra.PurePowerReductionBits
open LeanCanny.Encoding
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R]

noncomputable def coefficientPolynomial {n : ℕ} (f : R →+ ℤ) (p : MvPolynomial (Fin n) R) : MvPolynomial (Fin n) ℤ :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange f f.map_zero (AddMonoidAlgebra.coeff p))

theorem coefficientPolynomial_coeff {n : ℕ} (f : R →+ ℤ) (p : MvPolynomial (Fin n) R) (m : Fin n →₀ ℕ) :
    (coefficientPolynomial f p).coeff m = f (p.coeff m) := rfl

theorem matrix_coefficient {n B : ℕ} (f : R →+ ℤ) (fallback : Fin n) (d : Fin n → ℕ)
    (low : Fin n → MvPolynomial (Fin n) R) (c : R) (bound : ℕ)
    (i j : PurePowerReductionMatrix.Index n B) :
    PurePowerReductionMatrix.matrix fallback d (fun r => coefficientPolynomial f (low r)) (f c) bound i j =
      f (PurePowerReductionMatrix.matrix fallback d low c bound i j) := by
  unfold PurePowerReductionMatrix.matrix
  by_cases hn : PurePowerReductionMatrix.Normal d (FixedWidthPolynomial.vector n B j)
  · simp only [ite_eq_left hn]
    by_cases hij : i = j
    · simp only [ite_eq_left hij]
    · simp only [ite_eq_right hij, map_zero]
  · simp only [ite_eq_right hn]
    by_cases hv : (FixedWidthPolynomial.vector n B j).degree ≤ bound
    · simp only [ite_eq_left hv, MonicMonomialReduction.step_coefficient]
      split_ifs <;> simp only [coefficientPolynomial_coeff, map_neg, map_zero]
    · simp only [ite_eq_right hv, map_zero]

theorem entry_packet_coefficient (L : Layout) (bound : List Bool → ℕ)
    (constant coefficient : List Bool → List Bool) (q : List Bool) (f : R →+ ℤ)
    (low : Fin (L.arity (pairFst q)) → MvPolynomial (Fin (L.arity (pairFst q))) R)
    (c : R) (fallback : Fin (L.arity (pairFst q)))
    (hconstant : constant q = MatrixPower.residueBits (f c : ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
    (hcoefficient : ∀ (i : Fin (L.arity (pairFst q))) (k : ℕ),
      coefficient (packet q i.val k) = MatrixPower.residueBits
        (f ((low i).coeff (RationalSubstitution.Indexed.exponentVector (L.arity (pairFst q))
          (FixedWidthPolynomial.entry (L.width (pairFst q)) k))) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
    (r s : Indices L q) :
    entry L bound constant coefficient (packet q r.val s.val) = MatrixPower.residueBits
      ((f (PurePowerReductionMatrix.matrix fallback (Degrees L (pairFst q)) low c (bound (pairFst q)) s r) : ℤ) :
        ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  have HC : ∀ (i : Fin (L.arity (pairFst q))) (k : ℕ),
      coefficient (packet q i.val k) = MatrixPower.residueBits
        (((coefficientPolynomial f (low i)).coeff
          (RationalSubstitution.Indexed.exponentVector (L.arity (pairFst q))
          (FixedWidthPolynomial.entry (L.width (pairFst q)) k))) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
    simpa only [coefficientPolynomial_coeff] using hcoefficient
  rw [entry_packet L bound constant coefficient q (fun i => coefficientPolynomial f (low i)) (f c) fallback hconstant HC,
    matrix_coefficient]

end LeanCanny.Algebra.PurePowerReductionBits
