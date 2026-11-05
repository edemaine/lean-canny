/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialBankCenterSpace
public import LeanCanny.Encoding.IntegralFramedBankNumeratorAtWidth
/-! # Charged integer polynomial sources evaluated at one chronological bank

Source access includes an exact arbitrary-modulus coefficient protocol. The
same bank and reference table are retained when only the test datum varies.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankPolynomialModel
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask MatrixPower FixedWidthPolynomial
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

structure Source where
  arity : List Bool → ℕ
  width : List Bool → ℕ
  degree : List Bool → ℕ
  mass : List Bool → ℕ
  polynomial : (z : List Bool) → MvPolynomial (Fin (arity z)) ℤ
  fit : ∀ z i, (polynomial z).degreeOf i < 2 ^ width z
  polynomial_degree : ∀ z, (polynomial z).totalDegree ≤ degree z
  polynomial_mass : ∀ z, MvMass.mass (polynomial z) ≤ 2 ^ mass z

structure Access (S : Source) where
  arity : UnaryFn S.arity
  width : UnaryFn S.width
  degree : BinaryFn S.degree
  mass : BinaryFn S.mass
  coefficient : List Bool → List Bool
  evaluator : SpaceFunction coefficient
  packet : ∀ z bits modulus, coefficient (pair (pair z bits) modulus) =
    residueBits ((((S.polynomial z).coeff (nativeExponent (Equiv.refl _) (S.width z) (Nat.fromBitsLE bits))) : ℤ) :
      ZMod (Nat.fromBitsLE modulus + 1))

noncomputable def allowance (S : Source) (read : List Bool → List Bool) (c d : List Bool) :=
  S.arity (read (pair c d)) * (2 * 2 ^ S.width (read (pair c d)))
noncomputable def numerator (B : Bank) (refs : List Bool → List Bool) (c : List Bool) (i : ℕ) :=
  IntegralMixedFramedBankTermBits.numeratorPolynomial B.parameters B.plan B.data (B.key c)
    (Nat.fromBitsLE (WordList.get (refs c) i))
noncomputable def denominator (B : Bank) (c : List Bool) := (atKey B.parameters B.plan B.data (B.key c)).common
noncomputable def polynomial (S : Source) (B : Bank) (read refs : List Bool → List Bool) (c d : List Bool) :
    MvPolynomial (Fin ((atKey B.parameters B.plan B.data (B.key c)).count)) ℤ :=
  CommonDenominatorSpecialization.clear (allowance S read c d) (denominator B c)
    (fun i : Fin (S.arity (read (pair c d))) => numerator B refs c i.val) (S.polynomial (read (pair c d)))
noncomputable def degree (S : Source) (B : Bank) (read : List Bool → List Bool) (c d : List Bool) :=
  S.degree (read (pair c d)) * IntegralMixedFramedBankTermBits.maxPower B.parameters B.plan B.data (B.key c)
noncomputable def coordinateMass (B : Bank) (c : List Bool) :=
  IntegralMixedFramedBankTermBits.coordinateMass B.parameters B.plan B.data B.nodes B.factor B.seed (B.key c)
noncomputable def mass (S : Source) (B : Bank) (read : List Bool → List Bool) (c d : List Bool) :=
  S.mass (read (pair c d)) + coordinateMass B c * allowance S read c d

theorem allowance_degree (S : Source) (read : List Bool → List Bool) (c d : List Bool) :
    (S.polynomial (read (pair c d))).totalDegree ≤ allowance S read c d := by
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro e he
  rw [Finsupp.sum_fintype _ _ (by simp)]
  calc
    _ ≤ ∑ _ : Fin (S.arity (read (pair c d))), 2 * 2 ^ S.width (read (pair c d)) :=
      Finset.sum_le_sum (fun i _ => (MvPolynomial.monomial_le_degreeOf i he).trans
        ((S.fit _ i).le.trans (by omega)))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, allowance]

theorem degree_bound (S : Source) (B : Bank) (read refs : List Bool → List Bool) (c d : List Bool) :
    (polynomial S B read refs c d).totalDegree ≤ degree S B read c d := by
  exact (CommonDenominatorSpecialization.degree_mul (allowance S read c d) (denominator B c)
    (fun i : Fin (S.arity (read (pair c d))) => numerator B refs c i.val)
    (IntegralMixedFramedBankTermBits.maxPower B.parameters B.plan B.data (B.key c))
    (fun i => IntegralMixedFramedBankTermBits.numerator_degree _ _ _ _ _) (S.polynomial (read (pair c d)))).trans
      (Nat.mul_le_mul_right _ (S.polynomial_degree _))

theorem mass_bound (S : Source) (B : Bank) (read refs : List Bool → List Bool) (c d : List Bool) :
    MvMass.mass (polynomial S B read refs c d) ≤ 2 ^ mass S B read c d := by
  have HQ : (denominator B c).natAbs ≤ 2 ^ coordinateMass B c := by
    have H := IntegralMixedFramedBankTermBits.denominator_mass B.parameters B.plan B.data
      B.nodes B.factor B.seed B.bounds (B.key c) 0
    simpa only [IntegralMixedFramedBankTermBits.denominatorPolynomial, MvMass.C, denominator, coordinateMass] using H
  have HN (i : Fin (S.arity (read (pair c d)))) : MvMass.mass (numerator B refs c i.val) ≤ 2 ^ coordinateMass B c :=
    IntegralMixedFramedBankTermBits.numerator_mass _ _ _ _ _ _ B.bounds _ _
  have H := CommonDenominatorSpecialization.mass (allowance S read c d) (denominator B c)
    (fun i : Fin (S.arity (read (pair c d))) => numerator B refs c i.val)
    (S.polynomial (read (pair c d))) (allowance_degree S read c d) (2 ^ coordinateMass B c) HQ HN
  exact H.trans ((Nat.mul_le_mul_right _ (S.polynomial_mass _)).trans_eq (by rw [← pow_mul, ← pow_add]; rfl))

theorem sign (S : Source) (B : Bank) (read refs : List Bool → List Bool) (c d : List Bool)
    (raw : Fin ((atKey B.parameters B.plan B.data (B.key c)).count) → ℝ) :
    SignType.sign ((polynomial S B read refs c d).eval₂ (Int.castRingHom ℝ) raw) =
      SignType.sign ((S.polynomial (read (pair c d))).eval₂ (Int.castRingHom ℝ)
        (fun i => IntegralMixedFramedBankTermSign.point B.parameters B.plan B.data (B.key c) raw
          (Nat.fromBitsLE (WordList.get (refs c) i.val)))) := by
  have HQ : (denominator B c : ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr (IntegralMixedFramedBankTermSign.common_ne_zero _ _ _ _)
  have HP : 0 < (denominator B c : ℝ) ^ allowance S read c d := by
    change 0 < (denominator B c : ℝ) ^ (S.arity (read (pair c d)) * (2 * 2 ^ S.width (read (pair c d))))
    rw [show S.arity (read (pair c d)) * (2 * 2 ^ S.width (read (pair c d))) =
      2 * (S.arity (read (pair c d)) * 2 ^ S.width (read (pair c d))) by ring, pow_mul]
    exact pow_pos (sq_pos_of_ne_zero HQ) _
  have HE := CommonDenominatorSpecialization.eval (Int.castRingHom ℝ) (allowance S read c d) (denominator B c)
    (fun i : Fin (S.arity (read (pair c d))) => numerator B refs c i.val) (S.polynomial (read (pair c d)))
    (allowance_degree S read c d) HQ raw
  rw [polynomial, HE, sign_mul]
  change SignType.sign ((denominator B c : ℝ) ^ allowance S read c d) * _ = _
  rw [sign_pos HP, one_mul]
  apply congrArg (fun v => SignType.sign ((S.polynomial (read (pair c d))).eval₂ (Int.castRingHom ℝ) v))
  funext i
  have H := IntegralMixedFramedBankTermSign.ratio B.parameters B.plan B.data (B.key c) raw
    (Nat.fromBitsLE (WordList.get (refs c) i.val))
  simpa only [IntegralMixedFramedBankTermBits.denominatorPolynomial, MvPolynomial.eval₂_C, numerator, denominator] using H

end LeanCanny.Encoding.IntegralFramedBankPolynomialModel
