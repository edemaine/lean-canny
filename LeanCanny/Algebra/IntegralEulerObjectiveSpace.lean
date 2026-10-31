/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralEulerTermSpace
public import LeanCanny.Algebra.IntegralClearedLowerSpace
public import LeanCanny.Algebra.IntegralCriticalLeadingSpace

/-! # Native actual integral Euler objective coefficients

The objective lower polynomial is D times the cleared source lower part
minus the constructed sum of other spatial-coordinate gradient products.
All four original reader costs are charged; no critical-row coefficient
reader or modular inverse is supplied.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralEulerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def Source.objectivePolynomial (S : Source) (c : List Bool) :
    letI := S.ring c
    MvPolynomial (Fin (S.free c)) (S.carrier c) := by
  letI := S.ring c
  exact MvPolynomial.C (S.allowance c : S.carrier c) * S.toGradient.toFrozen.lowerPolynomial c - S.sumPolynomial c

noncomputable def Source.objectiveValue (S : Source) (c : List Bool) : List Bool := by
  letI := S.ring c
  exact residueBits ((Algebra.leftMulMatrix (S.basis c)
    ((S.objectivePolynomial c).coeff (S.targetExponent c)) (S.row c) (S.col c) : ℤ) : ZMod (S.modulus c))

theorem objective_coefficient {A : Type*} [CommRing A] {M N : ℕ} (b : Module.Basis (Fin M) ℤ A)
    (low other : MvPolynomial (Fin N) A) (D : ℕ) (e : Fin N →₀ ℕ) (r t : Fin M) :
    Algebra.leftMulMatrix b ((MvPolynomial.C (D : A) * low - other).coeff e) r t =
      (D : ℤ) * Algebra.leftMulMatrix b (low.coeff e) r t - Algebra.leftMulMatrix b (other.coeff e) r t := by
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul, map_sub, Matrix.sub_apply]
  congr 1
  rw [← nsmul_eq_mul, map_nsmul, Matrix.smul_apply, nsmul_eq_mul]

def subtractPost (S : Source) (z : List Bool) : List Bool :=
  ArithmeticBits.addMod (pair (BinaryNatCode.encode (S.modulus (pairFst z)))
    (pair (pairFst (pairSnd z)) (ArithmeticBits.negate
      (pair (BinaryNatCode.encode (S.modulus (pairFst z))) (pairSnd (pairSnd z))))))

attribute [local irreducible] ArithmeticBits.addMod ArithmeticBits.negate

theorem subtractPost_FP (S : Source) (a : Access S) : subtractPost S ∈ FP := by
  have HM : BinaryFn (fun z => S.modulus (pairFst z)) := a.modulus.comp pairFst_mem_FP
  have HX := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have HY := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have HN := mem_FP_comp (mem_FP_pair HM.bits_mem_FP HY) ArithmeticBits.negate_mem_FP
  exact mem_FP_comp (mem_FP_pair HM.bits_mem_FP (mem_FP_pair HX HN)) ArithmeticBits.addMod_mem_FP

theorem subtractPost_packet (S : Source) (c : List Bool) (x y : ZMod (S.modulus c)) :
    subtractPost S (pair c (pair (residueBits x) (residueBits y))) = residueBits (x - y) := by
  let : NeZero (S.modulus c) := ⟨S.modulus_ne_zero c⟩
  simp only [subtractPost, pairFst_pair, pairSnd_pair, ArithmeticBits.negate_residueBits,
    ArithmeticBits.addMod_residueBits, sub_eq_add_neg]

theorem objective_value (S : Source) (c : List Bool) :
    subtractPost S (pair c (pair
      (IntegralCriticalLeadingBits.degreePost S.toGradient.toFrozen (pair c (S.toGradient.toFrozen.lowerValue c)))
      (S.sumValue c))) = S.objectiveValue c := by
  let := S.ring c
  unfold IntegralFrozenPowerBits.Source.lowerValue Source.sumValue Source.objectiveValue Source.objectivePolynomial
  rw [IntegralCriticalLeadingBits.degreePost_packet, subtractPost_packet, objective_coefficient,
    Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  congr 1
  dsimp only [Source.targetExponent, IntegralClearedCoefficientBits.Source.targetExponent]
  ring

attribute [local irreducible] Source.objectiveValue Source.sumValue IntegralFrozenPowerBits.Source.lowerValue subtractPost

theorem objective_evaluator (S : Source) (a : Access S) (EC : SpaceFunction a.coefficient)
    (EH : SpaceFunction a.height) (EQ : SpaceFunction a.denominator) (EA : SpaceFunction a.leading) :
    SpaceFunction S.objectiveValue := by
  have EL := IntegralFrozenPowerBits.lower_evaluator S.toGradient.toFrozen a.toGradient.toFrozen EC EH EQ EA
  have ED := EL.withInput.postcompose (IntegralCriticalLeadingBits.degreePost S.toGradient.toFrozen)
    (IntegralCriticalLeadingBits.degreePost_FP S.toGradient.toFrozen a.toGradient.toFrozen)
  have ES := sum_evaluator S a EC EH EQ
  refine ((ED.pairOutputs ES).withInput.postcompose (subtractPost S) (subtractPost_FP S a)).congr (funext fun c => ?_)
  exact objective_value S c

end LeanCanny.Algebra.IntegralEulerBits
