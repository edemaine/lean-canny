/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralClearedCriticalBounds

/-! # The constructed critical polynomial has an integer top coefficient

The relative characteristic polynomial is monic in its spatial dimension.
Rescaling therefore makes its top coefficient an explicit power of the
common integer row leading coefficient. That integer has a native modular
reader using only the original denominator and leading readers.
-/

@[expose] public section
namespace LeanCanny.Algebra.PurePowerRelativeAnnihilator
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n W : ℕ} {R : Type*} [CommRing R] [Nontrivial R]

theorem top_coefficient (fallback : Fin n) (d : Fin n → ℕ) (low : Fin n → MvPolynomial (Fin n) R)
    (c : R) (bound : ℕ) (hgrid : PurePowerReductionMatrix.gridBound d + 1 ≤ bound)
    (hbound : bound < 2 ^ W) (r : Fin n) :
    (polynomial fallback d low c bound hgrid hbound r).coeff (FixedWidthPolynomial.count n W) =
      c ^ ((bound + 1) * FixedWidthPolynomial.count n W) := by
  unfold polynomial
  rw [ScaledGradedReductionAnnihilator.coefficient]
  have H := (Matrix.charpoly_monic (actionMatrix fallback d low c bound hgrid hbound r)).coeff_natDegree
  have HE : (actionMatrix fallback d low c bound hgrid hbound r).charpoly.coeff
      (FixedWidthPolynomial.count n W) = 1 := by
    simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] using H
  rw [HE, one_mul]

end LeanCanny.Algebra.PurePowerRelativeAnnihilator

namespace LeanCanny.Algebra.IntegralClearedCriticalLeadingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralClearedCriticalBits
set_option backward.isDefEq.respectTransparency false

def exponent (S : Source) (c : List Bool) : ℕ := (S.bound c + 1) * IntegralClearedCriticalBounds.dimension S c
noncomputable def integer (S : Source) (c : List Bool) : ℤ := IntegralClearedCriticalBounds.commonLeading S c ^ exponent S c
noncomputable def value (S : Source) (c : List Bool) : List Bool := residueBits (integer S c : ZMod (S.modulus c))

theorem exponent_binary (S : Source) (a : Access S) : BinaryFn (exponent S) :=
  (a.bound.add (BinaryFn.const 1)).mul (IntegralClearedCriticalBounds.dimension_binary S a)

theorem coefficient (S : Source) (c : List Bool) :
    letI := S.ring c
    (S.annihilator c).coeff (IntegralClearedCriticalBounds.dimension S c) = (integer S c : S.carrier c) := by
  let := S.ring c
  let : Nontrivial (S.carrier c) := (relativeSource S).nontrivial c
  rw [IntegralClearedCriticalBits.annihilator_eq]
  unfold IntegralClearedCriticalBounds.dimension
  rw [PurePowerRelativeAnnihilator.top_coefficient]
  simp only [integer, IntegralClearedCriticalBounds.commonLeading, exponent,
    IntegralClearedCriticalBounds.dimension, Int.cast_pow]

theorem integer_height (S : Source) (c : List Bool) (H : ℕ)
    (hp : letI := S.ring c
      ∀ k r t, (Algebra.leftMulMatrix (S.basis c) ((S.annihilator c).coeff k) r t).natAbs ≤ 2 ^ H) :
    (integer S c).natAbs ≤ 2 ^ H := by
  let := S.ring c
  have HE := hp (IntegralClearedCriticalBounds.dimension S c) (S.row c) (S.row c)
  rw [coefficient] at HE
  simpa only [map_intCast, Matrix.intCast_apply, ite_true, Int.cast_id] using HE

theorem integer_ne_zero (S : Source) (c : List Bool) (ha : S.leading c ≠ 0) (hq : S.denominator c ≠ 0)
    (hD : S.allowance c ≠ 0) : integer S c ≠ 0 := by
  apply pow_ne_zero
  exact mul_ne_zero (mul_ne_zero ha (pow_ne_zero _ hq)) (Int.natCast_ne_zero.mpr hD)

def powerPost (S : Source) (z : List Bool) : List Bool :=
  BinaryNat.powMod (pair (pairSnd z) (pair (BinaryNatCode.encode (exponent S (pairFst z)))
    (BinaryNatCode.encode (S.modulus (pairFst z) - 1))))

theorem powerPost_FP (S : Source) (a : Access S) : powerPost S ∈ FP := by
  have HE : BinaryFn (fun z => exponent S (pairFst z)) := (exponent_binary S a).comp pairFst_mem_FP
  have HM : BinaryFn (fun z => S.modulus (pairFst z) - 1) := (a.modulus.sub (BinaryFn.const 1)).comp pairFst_mem_FP
  exact mem_FP_comp (mem_FP_pair pairSnd_mem_FP (mem_FP_pair HE.bits_mem_FP HM.bits_mem_FP)) BinaryNat.powMod_mem_FP

theorem powerPost_packet (S : Source) (c : List Bool) (x : ZMod (S.modulus c)) :
    powerPost S (pair c (residueBits x)) = residueBits (x ^ exponent S c) := by
  simp only [powerPost, pairFst_pair, pairSnd_pair]
  exact IntegralScaledCharacteristicBits.pow_residue _ _ (S.modulus_ne_zero c) x

attribute [local irreducible] value powerPost IntegralCriticalLeadingBits.value

theorem evaluator (S : Source) (a : Access S) (EQ : SpaceFunction a.denominator) (EA : SpaceFunction a.leading) :
    SpaceFunction (value S) := by
  have E := IntegralCriticalLeadingBits.evaluator S.toEuler.toGradient.toFrozen a.toEuler.toGradient.toFrozen EQ EA
  refine (E.withInput.postcompose (powerPost S) (powerPost_FP S a)).congr (funext fun c => ?_)
  change powerPost S (pair c (IntegralCriticalLeadingBits.value S.toEuler.toGradient.toFrozen c)) = value S c
  unfold IntegralCriticalLeadingBits.value
  rw [powerPost_packet]
  unfold value integer IntegralClearedCriticalBounds.commonLeading
  simp only [Int.cast_pow]

end LeanCanny.Algebra.IntegralClearedCriticalLeadingBits
