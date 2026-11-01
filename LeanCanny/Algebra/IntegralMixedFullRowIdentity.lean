/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedFullRowMultiplier

/-! # Literal full-row entries from low entries and integer Fermat scales -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullRowIdentity
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial MatrixPower
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource
open IntegralMixedVirtualSweepSource IntegralMixedVirtualOriginalRows IntegralMixedFullRowMultiplier
open scoped Classical BigOperators

theorem integer_entry {A : Type*} [CommRing A] {M : ℕ} (b : Module.Basis (Fin M) ℤ A)
    (z : ℤ) (r t : Fin M) : Algebra.leftMulMatrix b (z : A) r t = z * (if r = t then 1 else 0) := by
  rw [map_intCast, Matrix.intCast_apply]
  split_ifs <;> simp only [mul_one, mul_zero] <;> rfl

theorem sum_entry {A : Type*} [CommRing A] {M n : ℕ} (b : Module.Basis (Fin M) ℤ A)
    (z : ℤ) (P : Fin n → Prop) [DecidablePred P] (r t : Fin M) :
    Algebra.leftMulMatrix b ((z : A) * ∑ i, if P i then 1 else 0) r t =
      z * ((if r = t then ∑ i : Fin n, if P i then 1 else 0 else 0 : ℕ) : ℤ) := by
  have HS : (z : A) * (∑ i : Fin n, if P i then (1 : A) else 0) =
      ((z * (∑ i : Fin n, if P i then 1 else 0 : ℕ) : ℤ) : A) := by
    push_cast
    rfl
  rw [HS, integer_entry]
  split_ifs <;> simp only [mul_one, mul_zero, Nat.cast_zero]

theorem equation_entry {A : Type*} [CommRing A] {M n : ℕ} (b : Module.Basis (Fin M) ℤ A)
    (p l : MvPolynomial (Fin n) A) (z : ℤ) (D : ℕ) (e : Fin n →₀ ℕ)
    (h : p.coeff e = l.coeff e + (z : A) * ∑ j, if Finsupp.single j D = e then 1 else 0)
    (r t : Fin M) :
    Algebra.leftMulMatrix b (p.coeff e) r t = Algebra.leftMulMatrix b (l.coeff e) r t +
      z * ((if r = t then ∑ j : Fin n, if Finsupp.single j D = e then 1 else 0 else 0 : ℕ) : ℤ) := by
  rw [h, map_add, Matrix.add_apply, sum_entry]

theorem derivative_entry {A : Type*} [CommRing A] {M n : ℕ} (b : Module.Basis (Fin M) ℤ A)
    (p l : MvPolynomial (Fin n) A) (z : ℤ) (D : ℕ) (j : Fin n) (e : Fin n →₀ ℕ)
    (h : p.coeff e = l.coeff e + if Finsupp.single j D = e then (z : A) else 0)
    (r t : Fin M) :
    Algebra.leftMulMatrix b (p.coeff e) r t = Algebra.leftMulMatrix b (l.coeff e) r t +
      z * ((if Finsupp.single j D = e ∧ r = t then 1 else 0 : ℕ) : ℤ) := by
  rw [h, map_add, Matrix.add_apply]
  by_cases HP : Finsupp.single j D = e <;> by_cases HR : r = t <;>
    simp only [HP, HR, and_false, and_true, ite_true, ite_false,
      integer_entry, map_zero, Matrix.zero_apply, Nat.cast_one, Nat.cast_zero, mul_one, mul_zero]

theorem row_entry (F : Family) (I : Indices F) (W : List Bool → ℕ) (q : List Bool) :
    Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      ((row F q (I.coordinate q)).coeff (exponent F I W q)) (I.row q) (I.col q) =
      Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
        ((low F I q).coeff (exponent F I W q)) (I.row q) (I.col q) +
          scalar F I q * (multiplier F I W q : ℤ) := by
  by_cases HQ : isEquation F I q
  · have HE := equation_entry (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      (row F q (I.coordinate q)) (frozen F I q) (originalScale F q) (F.spatial q).degree (exponent F I W q)
      (equation_coefficient F I q (I.coordinate q) HQ (exponent F I W q)) (I.row q) (I.col q)
    have HM := FixedWidthPowerMonomial.multiplicity_eq (free F) W (degree F) (target F I) q
    have HT : Nat.fromBitsLE (target F I q) = I.target q := Nat.fromBitsLE_bits _
    rw [HT] at HM
    have HN : multiplier F I W q = if I.row q = I.col q then
        ∑ j : Fin (free F q), if Finsupp.single j (F.spatial q).degree = exponent F I W q then 1 else 0 else 0 := by
      simp only [multiplier, highMultiplicity, HQ, ite_true]
      exact congrArg (fun v : ℕ => if I.row q = I.col q then v else 0) HM
    simp only [low, scalar, HQ]
    exact HE.trans (congrArg (fun v : ℕ =>
      Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
        ((frozen F I q).coeff (exponent F I W q)) (I.row q) (I.col q) + originalScale F q * (v : ℤ)) HN.symm)
  · have HE := derivative_entry (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      (row F q (I.coordinate q)) (gradient F I q (I.coordinate q))
      (originalScale F q * (F.spatial q).degree) ((F.spatial q).degree - 1) (I.coordinate q) (exponent F I W q)
      (derivative_coefficient F I q (I.coordinate q) HQ (exponent F I W q)) (I.row q) (I.col q)
    have HM : FixedWidthPowerMonomial.Matches (free F) W (fun q => degree F q - 1) (selected F I) (target F I) q ↔
        Finsupp.single (I.coordinate q) ((F.spatial q).degree - 1) = exponent F I W q := by
      have H := FixedWidthPowerMonomial.matches_iff (free F) W (fun q => degree F q - 1)
        (selected F I) (target F I) q (I.coordinate q).isLt
      simpa only [IntegralMixedFullRowMultiplier.selected, target, BinaryNatCode.encode,
        Nat.fromBitsLE_bits, exponent] using (H.trans eq_comm)
    have HN : multiplier F I W q = if Finsupp.single (I.coordinate q) ((F.spatial q).degree - 1) = exponent F I W q ∧
        I.row q = I.col q then 1 else 0 := by
      simp only [multiplier, highMultiplicity, HQ, ite_false, HM]
      split_ifs <;> simp_all
    simp only [low, scalar, HQ]
    exact HE.trans (congrArg (fun v : ℕ =>
      Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
        ((gradient F I q (I.coordinate q)).coeff (exponent F I W q)) (I.row q) (I.col q) +
          (originalScale F q * (F.spatial q).degree) * (v : ℤ)) HN.symm)

theorem low_entry (F : Family) (I : Indices F) (W : List Bool → ℕ) (q : List Bool) :
    (if lowFits F I W q then
      Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
        ((low F I q).coeff (nativeExponent (Equiv.refl (Fin (free F q))) (canonicalWidth F q) (lowTarget F I W q)))
          (I.row q) (I.col q) else 0) =
    Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      ((low F I q).coeff (exponent F I W q)) (I.row q) (I.col q) := by
  let read (z : Coefficient F q) : ℤ :=
    Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis z (I.row q) (I.col q)
  have H := congrArg read (low_coefficient F I W q)
  by_cases HF : lowFits F I W q
  · simpa only [HF, ite_true] using H
  · simpa only [HF, ite_false, read, map_zero, Matrix.zero_apply] using H

end LeanCanny.Algebra.IntegralMixedFullRowIdentity
