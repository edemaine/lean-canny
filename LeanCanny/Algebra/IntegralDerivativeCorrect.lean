/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralDerivativeSource

/-! # Correctness of native algebra-valued partial coefficients

An integer coefficient polynomial extracts one requested old basis entry.
Additivity suffices to commute this extraction with differentiation. The
native scalar derivative program therefore reads the actual derivative
over the parameter algebra from the original coefficient reader.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralDerivativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem exponent_eq (S : Source) (z : List Bool) :
    FixedWidthDerivativeBits.exponent (width S) pairSnd (Equiv.refl (Fin (S.arity (original z)))) z =
      RationalSubstitution.Indexed.exponentVector (S.arity (original z))
        (FixedWidthPolynomial.entry (S.sourceWidth (original z)) (Nat.fromBitsLE (pairSnd z))) := by
  apply Finsupp.ext
  intro i
  change FixedWidthQuery.coordinate (width S) pairSnd z i.val = _
  rw [FixedWidthQuery.coordinate_eq_entry]
  rfl

theorem packet (S : Source) (a : Access S) (c : List Bool) (k : ℕ) (r t : Fin (S.rank c)) :
    letI := S.ring c
    value S a (pair (IntegralClearedCoefficientBits.context c r.val t.val) (BinaryNatCode.encode k)) =
      residueBits ((Algebra.leftMulMatrix (S.basis c)
        ((MvPolynomial.pderiv (S.selected c) (S.polynomial c)).coeff
          (RationalSubstitution.Indexed.exponentVector (S.arity c) (FixedWidthPolynomial.entry (S.sourceWidth c) k)))
        r t : ℤ) : ZMod (S.modulus c)) := by
  let := S.ring c
  generalize hz : pair (IntegralClearedCoefficientBits.context c r.val t.val) (BinaryNatCode.encode k) = z
  have ho : original z = c := by
    rw [original, ← hz]
    simp only [IntegralClearedCoefficientBits.context, pairFst_pair]
  have HQ : pairFst z = IntegralClearedCoefficientBits.context c r.val t.val := by rw [← hz, pairFst_pair]
  have HK : pairSnd z = BinaryNatCode.encode k := by rw [← hz, pairSnd_pair]
  subst c
  let f := IntegralPurePowerReductionBits.coefficientHom (S.basis (original z)) r t
  let P := PurePowerReductionBits.coefficientPolynomial f (S.polynomial (original z))
  have HD : P.totalDegree ≤ degree S z :=
    (PurePowerReductionBits.coefficientPolynomial_degree f (S.polynomial (original z))).trans (S.degree_le (original z))
  have HC : ∀ m, (a.coefficient ∘ coefficientQuery) (pair z (BinaryNatCode.encode m)) =
      residueBits ((P.coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (S.arity (original z)))) (width S z) m) : ℤ) :
        ZMod (S.modulus (original z))) := by
    intro m
    have HP : coefficientQuery (pair z (BinaryNatCode.encode m)) =
        pair (IntegralClearedCoefficientBits.context (original z) r.val t.val) (BinaryNatCode.encode m) :=
      (coefficientQuery_packet z m).trans (congrArg (fun b => pair b (BinaryNatCode.encode m)) HQ)
    rw [Function.comp_apply, HP, a.coefficient_eq]
    unfold P
    rw [PurePowerReductionBits.coefficientPolynomial_coeff]
    rfl
  have H := FixedWidthDerivativeBits.packet (arity S) (width S) (width S) (degree S) (selected S) pairSnd (modulus S)
    (Equiv.refl (Fin (S.arity (original z)))) (a.coefficient ∘ coefficientQuery) z P (S.selected (original z)) (S.modulus (original z))
    rfl rfl (S.degree_pos (original z)) HD (S.degree_lt (original z)) rfl HC
  dsimp only [P] at H
  rw [← PurePowerReductionBits.coefficientPolynomial_pderiv, PurePowerReductionBits.coefficientPolynomial_coeff,
    exponent_eq, HK, BinaryNatCode.encode, Nat.fromBitsLE_bits] at H
  exact H

end LeanCanny.Algebra.IntegralDerivativeBits
