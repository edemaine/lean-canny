/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MonicParameterHeadCoefficients

/-! # One native old-coefficient query selects a monic lower-row coefficient

The newest block is divided by its fixed birth power. A nonzero remainder or
an excessive polynomial index gives zero. The accepted old query is exactly
the tail of the original exponent word.
-/

@[expose] public section
namespace LeanCanny.Algebra.MonicParameterRows
open MvPolynomial FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {ι R : Type*} [CommRing R]

theorem coefficient_lower_off_power (p : Polynomial (MvPolynomial ι R)) (N : ℕ)
    (w : ι→ℕ) (W : ℕ) (e : ι→₀ℕ) (l : ℕ) (hl : ¬W∣l) :
    (lower p N w W).coeff (appendExponent e l)=0 := by
  have HE (k : ℕ) : ¬k*W=l := by
    intro H
    apply hl
    exact H ▸ dvd_mul_left W k
  simp only [lower,coeff_sum,coefficient_block,ite_eq_right (HE _),Finset.sum_const_zero]

theorem native_lower_coefficient {m : ℕ}
    (p : Polynomial (MvPolynomial (Fin m) R)) (N : ℕ) (hp : p.Monic) (hd : p.natDegree=N)
    (w : Fin m→ℕ) (W : ℕ) (hW : 0<W) (V : ℕ) (bits : List Bool) :
    (rename (headEquiv m) (lower p N w W)).coeff
      (nativeExponent (Equiv.refl (Fin (m+1))) V (Nat.fromBitsLE bits)) =
      if entry V (Nat.fromBitsLE bits) 0 % W=0 ∧ entry V (Nat.fromBitsLE bits) 0 / W<N then
        (CoordinatePowerSubstitution.substitute w (p.coeff (entry V (Nat.fromBitsLE bits) 0 / W))).coeff
          (nativeExponent (Equiv.refl (Fin m)) V (Nat.fromBitsLE (bits.drop V))) else 0 := by
  have HT : p.coeff N=1 := by
    calc
      p.coeff N=p.coeff p.natDegree := congrArg (fun k=>p.coeff k) hd.symm
      _ = 1 := by rw [Polynomial.coeff_natDegree,hp.leadingCoeff]
  rw [coefficient_native_head]
  let l := entry V (Nat.fromBitsLE bits) 0
  let e := nativeExponent (Equiv.refl (Fin m)) V (Nat.fromBitsLE (bits.drop V))
  change (lower p N w W).coeff (appendExponent e l)=
    if l%W=0 ∧ l/W<N then (CoordinatePowerSubstitution.substitute w (p.coeff (l/W))).coeff e else 0
  by_cases HL : l%W=0
  · have HE : l=l/W*W := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero HL)).symm
    conv_lhs => rw [HE]
    rw [coefficient_lower p N w W hW]
    by_cases HK : l/W<N
    · simp only [HL,HK,and_self,ite_true,coefficient,HT,one_pow,mul_one]
    · simp only [HK,and_false,ite_false]
  · rw [coefficient_lower_off_power p N w W e l (by simpa only [Nat.dvd_iff_mod_eq_zero] using HL)]
    simp only [HL,false_and,ite_false]

end LeanCanny.Algebra.MonicParameterRows
