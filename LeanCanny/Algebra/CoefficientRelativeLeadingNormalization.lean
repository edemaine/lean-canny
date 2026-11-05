/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralRelativeLeadingNormalization
public import LeanCanny.Algebra.IntegralParameterInverseSpecialization
/-! # Relative leading normalization at a fixed coefficient index

The coefficient index is explicit. It can therefore be chosen after a
specialization that kills earlier coefficients of the characteristic polynomial.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientRelativeLeadingNormalization
open Polynomial
open scoped Classical
variable {R A I :Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Fintype I] [DecidableEq I]

noncomputable def denominatorAt (b :Module.Basis I R A) (a :A) (τ :ℕ) :R:=
  (Algebra.leftMulMatrix b a).charpoly.coeff τ

noncomputable def inverseValueAt (b :Module.Basis I R A) (a :A) (τ :ℕ) :A:=
  (IntegralParameterInverse.inverseAt (Algebra.leftMulMatrix b a).charpoly τ).eval₂
    (algebraMap R A) a

noncomputable def normalizeAt (b :Module.Basis I R A) (p :A[X]) (d τ :ℕ) :A[X]:=
  monomial d (algebraMap R A (denominatorAt b (p.coeff d) τ))+
    C (inverseValueAt b (p.coeff d) τ)*(p-monomial d (p.coeff d))

theorem coefficient (b :Module.Basis I R A) (p :A[X]) (d τ :ℕ) :
    (normalizeAt b p d τ).coeff d=algebraMap R A (denominatorAt b (p.coeff d) τ):=by
  simp only [normalizeAt,coeff_add,coeff_monomial,ite_true,coeff_C_mul,coeff_sub,
    sub_self,mul_zero,add_zero]

theorem natDegree_le (b :Module.Basis I R A) (p :A[X]) (d τ :ℕ)
    (hd :p.natDegree≤d) :(normalizeAt b p d τ).natDegree≤d:=by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  have H :d≠k:=by omega
  simp only [normalizeAt,coeff_add,coeff_monomial,H,ite_false,coeff_C_mul,coeff_sub,
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt hk),sub_zero,mul_zero,add_zero]

 theorem denominatorAt_native (b :Module.Basis I ℤ A) (a :A) :
    denominatorAt b a (Algebra.leftMulMatrix b a).charpoly.natTrailingDegree=
      IntegralRelativeLeadingNormalization.denominator b a:=rfl

 theorem inverseValueAt_native (b :Module.Basis I ℤ A) (a :A) :
    inverseValueAt b a (Algebra.leftMulMatrix b a).charpoly.natTrailingDegree=
      IntegralRelativeLeadingNormalization.inverseValue b a:=by
  rw [inverseValueAt,IntegralParameterInverse.inverseAt_natTrailingDegree]
  rfl

 theorem normalizeAt_native (b :Module.Basis I ℤ A) (p :A[X]) (d :ℕ) :
    normalizeAt b p d (Algebra.leftMulMatrix b (p.coeff d)).charpoly.natTrailingDegree=
      IntegralRelativeLeadingNormalization.normalize b p d:=by
  rw [normalizeAt,denominatorAt_native,inverseValueAt_native]
  rfl

end LeanCanny.Algebra.CoefficientRelativeLeadingNormalization
