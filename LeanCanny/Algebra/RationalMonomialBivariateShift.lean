/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RationalMonomialParameterShiftNative
/-! # One eta shift acts coefficientwise on the entire coordinate head

The same clearing allowance is used for every outer coefficient. This is an
additive coefficient map, not a claimed ring hom on chosen representatives.
-/
@[expose] public section
namespace LeanCanny.Algebra.RationalMonomialBivariateShift
open Polynomial RationalMonomialWindowQuery
open scoped Classical

noncomputable def coefficientMap (F : Family) (negative : Bool) (W : List Bool→ℕ) (c : List Bool) :
    MvPolynomial (Fin (F.arity c+1)) ℤ→+MvPolynomial (Fin (F.arity c+1)) ℤ :=
  CommonDenominatorSpecialization.clear (2*RationalMonomialParameterShift.sourceDegree F W c)
    (F.scalars.denominator c) (RationalMonomialParameterShift.numerator F negative c)

noncomputable def head (F : Family) (negative : Bool) (W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ)) (c : List Bool) :
    Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ) :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (Finsupp.mapRange (coefficientMap F negative W c) (map_zero _)
    (AddMonoidAlgebra.coeff (p c).toFinsupp)))

theorem coefficient (F : Family) (negative : Bool) (W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ)) (c : List Bool) (y : ℕ) :
    (head F negative W p c).coeff y=coefficientMap F negative W c ((p c).coeff y) :=rfl

theorem coefficient_native (F : Family) (negative : Bool) (W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ))
    (hfit : ∀ c y i,((p c).coeff y).degreeOf i<2^W c) (y : List Bool→ℕ) (c : List Bool) :
    (head F negative W p c).coeff (y c)=
      (RationalMonomialParameterShift.nativeFamily F negative W (fun c=>(p c).coeff (y c))
        (fun c=>hfit c (y c))).polynomial c :=by
  unfold RationalMonomialParameterShift.nativeFamily
  rw [coefficient,RationalMonomialParameterShift.sourceFamily_polynomial]
  rfl

theorem outer_degree (F : Family) (negative : Bool) (W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ)) (c : List Bool) :
    (head F negative W p c).natDegree≤(p c).natDegree :=by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro y hy
  rw [coefficient,Polynomial.coeff_eq_zero_of_natDegree_lt hy,map_zero]

theorem coefficient_degree (F : Family) (negative : Bool) (W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ))
    (hfit : ∀ c y i,((p c).coeff y).degreeOf i<2^W c) (c : List Bool) (y : ℕ) :
    ((head F negative W p c).coeff y).totalDegree≤
      RationalMonomialParameterShift.sourceDegree F W c*(F.weight c+1) :=by
  rw [coefficient]
  exact (RationalMonomialParameterShift.degree F negative c _ _).trans
    (Nat.mul_le_mul_right _ (RationalMonomialParameterShift.source_degree F W
      (fun c=>(p c).coeff y) (fun c=>hfit c y) c))

theorem coefficient_mass (F : Family) (negative : Bool) (W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ))
    (hfit : ∀ c y i,((p c).coeff y).degreeOf i<2^W c)
    (H : ℕ) (c : List Bool) (y : ℕ) (hm : MvMass.mass ((p c).coeff y)≤2^H) :
    MvMass.mass ((head F negative W p c).coeff y)≤
      2^(H+2*RationalMonomialParameterShift.sourceDegree F W c*(F.scalars.mass c+1)) :=by
  rw [coefficient_native F negative W p hfit (fun _=>y)]
  exact RationalMonomialParameterShift.source_mass F negative W _ (fun c=>(p c).coeff y)
    (fun c=>hfit c y) H c hm


theorem selected_head (F : Family) (negative : Bool) (W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (F.arity c+1)) ℤ))
    (hfit : ∀ c y i,((p c).coeff y).degreeOf i<2^W c) (c : List Bool)
    (z : Fin (F.arity c)→ℝ) (hi : F.index c<F.arity c) (hb : F.scalars.denominator c≠0) (δ : ℝ) :
    (head F negative W p c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons δ z))=
      Polynomial.C ((F.scalars.denominator c:ℝ)^(2*RationalMonomialParameterShift.sourceDegree F W c))*
        (p c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ)
          (Fin.cons ((F.scalars.numerator c:ℝ)*z ⟨F.index c,hi⟩^F.weight c/(F.scalars.denominator c:ℝ)+
            if negative then -δ else δ) z)) :=by
  ext y
  rw [Polynomial.coeff_map,Polynomial.coeff_C_mul,Polynomial.coeff_map,coefficient]
  exact RationalMonomialParameterShift.eval F negative c (RationalMonomialParameterShift.sourceDegree F W c)
    ((p c).coeff y) ((RationalMonomialParameterShift.source_degree F W (fun c=>(p c).coeff y)
      (fun c=>hfit c y) c).trans (by omega)) z hi hb δ

end LeanCanny.Algebra.RationalMonomialBivariateShift
