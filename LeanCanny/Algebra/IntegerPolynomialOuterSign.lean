/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegerRootBound
public import LeanCanny.Algebra.Sturm.RealSigns
public import LeanCanny.Algebra.Sturm.EvalInfinity

/-! # A uniform coefficient-mass cutoff for signs at a large parameter

This applies to an actual integer parameter polynomial. It does not assert
that an arbitrary recursive computation has such a polynomial presentation.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegerPolynomialOuterSign
open Polynomial
open scoped Classical

theorem nonzero_after_mass (p : Polynomial ℤ) (hp : p≠0) (x : ℝ)
    (hx : (coefficientMass p : ℝ)+1≤x) : p.eval₂ (Int.castRingHom ℝ) x≠0 := by
  intro H
  have HB:=abs_root_lt_coefficientMass_add_one p hp x H
  have HX : 0≤x:=le_trans (by positivity : 0≤(coefficientMass p : ℝ)+1) hx
  rw [abs_of_nonneg HX] at HB
  exact (not_lt_of_ge hx) HB

theorem sign_after_mass (p : Polynomial ℤ) (x : ℝ) (hx : (coefficientMass p : ℝ)+1≤x) :
    SignType.sign (p.eval₂ (Int.castRingHom ℝ) x)=SignType.sign (p.leadingCoeff : ℝ) := by
  by_cases hp : p=0
  · subst p
    simp
  let q:=p.map (Int.castRingHom ℝ)
  obtain ⟨B,hB⟩:=Sturm.exists_sign_atTop q
  let y:=max x B+1
  have HXY : x≤y:=by dsimp only [y]; linarith [le_max_left x B]
  have HBY : B<y:=by dsimp only [y]; linarith [le_max_right x B]
  have HS:=Sturm.sign_eval_const q HXY (fun z hz=>by
    change (p.map (Int.castRingHom ℝ)).eval z≠0
    rw [Polynomial.eval_map]
    exact nonzero_after_mass p hp z (hx.trans hz.1))
  rw [hB y HBY] at HS
  have HL : q.leadingCoeff=(p.leadingCoeff : ℝ):=
    Polynomial.leadingCoeff_map_of_injective Int.cast_injective p
  rw [HL] at HS
  simpa only [q,Polynomial.eval_map] using HS

theorem sign_after_binary_mass (p : Polynomial ℤ) (b : ℕ) (hb : coefficientMass p≤2^b) (x : ℝ)
    (hx : (2 : ℝ)^(b+1)≤x) :
    SignType.sign (p.eval₂ (Int.castRingHom ℝ) x)=SignType.sign (p.leadingCoeff : ℝ) := by
  apply sign_after_mass
  apply le_trans _ hx
  have H : coefficientMass p+1≤2^(b+1):=by
    rw [pow_succ]
    have HP:=Nat.one_le_two_pow (n:=b)
    omega
  exact_mod_cast H

theorem family_stable {ι : Type*} (p : ι→Polynomial ℤ) (b : ℕ) (hb : ∀ i,coefficientMass (p i)≤2^b)
    (x y : ℝ) (hx : (2 : ℝ)^(b+1)≤x) (hy : (2 : ℝ)^(b+1)≤y) :
    ∀ i,SignType.sign ((p i).eval₂ (Int.castRingHom ℝ) x)=SignType.sign ((p i).eval₂ (Int.castRingHom ℝ) y) :=
  fun i=>(sign_after_binary_mass (p i) b (hb i) x hx).trans (sign_after_binary_mass (p i) b (hb i) y hy).symm

end LeanCanny.Algebra.IntegerPolynomialOuterSign
