/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedHistory

/-! # Common-denominator height banks over a coefficient ring

The bank has only actual numerators and denominators. Clearing and affine
expressions use the native finite product and native expression syntax.
-/

@[expose] public section
namespace LeanCanny.Algebra
open scoped Classical BigOperators

structure CoefficientHeightBank (R A : Type*) [CommRing R] [CommRing A] (m : ℕ) where
  numerator : Fin m → A
  denominator : Fin m → R

namespace CoefficientHeightBank
variable {R A S B : Type*} [CommRing R] [CommRing A] [CommRing S] [CommRing B]
  [Algebra R A] [Algebra S B] {m : ℕ}

noncomputable def commonDenominator (x : CoefficientHeightBank R A m) : R :=
  ∏ i, x.denominator i

noncomputable def cofactor (x : CoefficientHeightBank R A m) (i : Fin m) : R :=
  ∏ j ∈ Finset.univ.erase i, x.denominator j

noncomputable def cleared (x : CoefficientHeightBank R A m) (i : Fin m) : A :=
  x.numerator i * algebraMap R A (x.cofactor i)

noncomputable def expression (x : CoefficientHeightBank R A m) : IntegralMixedHistory.AffineExpr → A
  | .constant c => algebraMap R A x.commonDenominator * (c : A)
  | .reference j => if hj : j < m then x.cleared ⟨j, hj⟩ else 0
  | .add a b => x.expression a + x.expression b
  | .scale c a => (c : A) * x.expression a

omit [Algebra R A] in
theorem commonDenominator_split (x : CoefficientHeightBank R A m) (i : Fin m) :
    x.commonDenominator = x.denominator i * x.cofactor i := by
  classical
  exact (Finset.mul_prod_erase Finset.univ (fun j => x.denominator j) (Finset.mem_univ i)).symm

omit [Algebra R A] in
theorem commonDenominator_ne_zero [Nontrivial R] [NoZeroDivisors R] (x : CoefficientHeightBank R A m)
    (h : ∀ i, x.denominator i ≠ 0) : x.commonDenominator ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => h i)

structure Specializes (φ : R →+* S) (ψ : A →+* B)
    (x : CoefficientHeightBank R A m) (y : CoefficientHeightBank S B m) : Prop where
  coefficients : ∀ r, ψ (algebraMap R A r) = algebraMap S B (φ r)
  numerator : ∀ i, ψ (x.numerator i) = y.numerator i
  denominator : ∀ i, φ (x.denominator i) = y.denominator i

namespace Specializes
variable {φ : R →+* S} {ψ : A →+* B}
  {x : CoefficientHeightBank R A m} {y : CoefficientHeightBank S B m}
  (H : Specializes φ ψ x y)
include H

theorem commonDenominator : φ x.commonDenominator = y.commonDenominator := by
  classical
  simp only [CoefficientHeightBank.commonDenominator, map_prod, H.denominator]

theorem cofactor (i : Fin m) : φ (x.cofactor i) = y.cofactor i := by
  classical
  simp only [CoefficientHeightBank.cofactor, map_prod, H.denominator]

theorem cleared (i : Fin m) : ψ (x.cleared i) = y.cleared i := by
  simp only [CoefficientHeightBank.cleared, map_mul, H.numerator, H.coefficients, H.cofactor]

theorem expression (a : IntegralMixedHistory.AffineExpr) : ψ (x.expression a) = y.expression a := by
  induction a with
  | constant c =>
    simp only [CoefficientHeightBank.expression, map_mul, H.coefficients,
      H.commonDenominator, map_intCast]
  | reference j =>
    simp only [CoefficientHeightBank.expression]
    split_ifs with hj
    · exact H.cleared ⟨j, hj⟩
    · exact map_zero ψ
  | add a b ha hb => simp only [CoefficientHeightBank.expression, map_add, ha, hb]
  | scale c a ha => simp only [CoefficientHeightBank.expression, map_mul, map_intCast, ha]

end Specializes

noncomputable def ofState {n cap width : ℕ} {P : IntegralMixedHistory.SpatialSource n} {ι : Type}
    (x : IntegralMixedHistory.State P cap width m ι) :
    CoefficientHeightBank ℤ x.sampler.scalarPrefix.carrier m where
  numerator := x.bank.numerator
  denominator := x.bank.denominator

theorem commonDenominator_ofState {n cap width : ℕ} {P : IntegralMixedHistory.SpatialSource n} {ι : Type}
    (x : IntegralMixedHistory.State P cap width m ι) :
    (ofState x).commonDenominator = IntegralMixedHistory.commonDenominator x := rfl

theorem cleared_ofState {n cap width : ℕ} {P : IntegralMixedHistory.SpatialSource n} {ι : Type}
    (x : IntegralMixedHistory.State P cap width m ι) (i : Fin m) :
    (ofState x).cleared i = IntegralMixedHistory.cleared x i := rfl

theorem expression_ofState {n cap width : ℕ} {P : IntegralMixedHistory.SpatialSource n} {ι : Type}
    (x : IntegralMixedHistory.State P cap width m ι) (a : IntegralMixedHistory.AffineExpr) :
    (ofState x).expression a = IntegralMixedHistory.expression x a := by
  induction a with
  | constant c => rfl
  | reference j => rfl
  | add a b ha hb => simp only [expression, IntegralMixedHistory.expression, ha, hb]
  | scale c a ha => simp only [expression, IntegralMixedHistory.expression, ha]

end CoefficientHeightBank
end LeanCanny.Algebra
