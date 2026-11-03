/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.MvCoefficientMass
public import Mathlib.Algebra.MvPolynomial.Equiv
/-! # Extracting two independent parameter coefficients preserves the raw tuple

Delta is the first variable and epsilon the second. Extraction leaves
exactly the original raw variables; evaluation is one ring hom.
-/
@[expose] public section
namespace LeanCanny.Algebra.MvTwoParameterCoefficient
open Polynomial
open scoped BigOperators Classical
variable {R : Type*} [CommSemiring R] {m : ℕ}

noncomputable def one (p : MvPolynomial (Fin (m+1)) R) (k : ℕ) : MvPolynomial (Fin m) R :=
  (MvPolynomial.finSuccEquiv R m p).coeff k

noncomputable def slice (p : MvPolynomial (Fin (m+2)) R) (δ ε : ℕ) : MvPolynomial (Fin m) R :=
  one (one p δ) ε

theorem coefficient (p : MvPolynomial (Fin (m+2)) R) (δ ε : ℕ) (v : Fin m→₀ℕ) :
    (slice p δ ε).coeff v=p.coeff ((v.cons ε).cons δ) :=by
  unfold slice one
  rw [MvPolynomial.finSuccEquiv_coeff_coeff,MvPolynomial.finSuccEquiv_coeff_coeff]

theorem one_degree (p : MvPolynomial (Fin (m+1)) R) (k : ℕ) : (one p k).totalDegree≤p.totalDegree :=by
  by_cases h : one p k=0
  · simp only [h,MvPolynomial.totalDegree_zero,Nat.zero_le]
  · exact (Nat.le_add_right _ _).trans (MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le p k h)

theorem degree (p : MvPolynomial (Fin (m+2)) R) (δ ε : ℕ) : (slice p δ ε).totalDegree≤p.totalDegree :=
  (one_degree (one p δ) ε).trans (one_degree p δ)

theorem one_eq_zero (p : MvPolynomial (Fin (m+1)) R) (k : ℕ) (hk : p.totalDegree<k) : one p k=0 :=by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [MvPolynomial.natDegree_finSuccEquiv]
  exact (MvPolynomial.degreeOf_le_totalDegree _ 0).trans_lt hk

theorem eq_zero (p : MvPolynomial (Fin (m+2)) R) (δ ε : ℕ) (h : p.totalDegree<δ ∨ p.totalDegree<ε) :
    slice p δ ε=0 :=by
  rcases h with h|h
  · rw [slice,one_eq_zero p δ h]
    simp [one]
  · exact one_eq_zero (one p δ) ε ((one_degree p δ).trans_lt h)

theorem one_mass (p : MvPolynomial (Fin (m+1)) ℤ) (k : ℕ) : MvMass.mass (one p k)≤MvMass.mass p :=by
  let s:=(one p k).support
  have HI : Function.Injective (fun e : Fin m→₀ℕ=>e.cons k) :=by
    intro e f h
    simpa only [Finsupp.tail_cons] using congrArg Finsupp.tail h
  have HS : s.image (fun e=>e.cons k)⊆p.support :=by
    intro e he
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp he
    exact MvPolynomial.mem_support_coeff_finSuccEquiv.mp hv
  change (∑ e∈s,((one p k).coeff e).natAbs)≤∑ e∈p.support,(p.coeff e).natAbs
  calc
    _=∑ e∈s,(p.coeff (e.cons k)).natAbs :=by
      apply Finset.sum_congr rfl
      intro e _
      rw [one,MvPolynomial.finSuccEquiv_coeff_coeff]
    _=∑ e∈s.image (fun e=>e.cons k),(p.coeff e).natAbs :=(Finset.sum_image (s:=s) (g:=fun e : Fin m→₀ℕ=>e.cons k)
      (f:=fun e : Fin (m+1)→₀ℕ=>(p.coeff e).natAbs) (fun _ _ _ _ h=>HI h)).symm
    _≤_:=Finset.sum_le_sum_of_subset_of_nonneg HS (fun _ _ _=>Nat.zero_le _)

theorem mass (p : MvPolynomial (Fin (m+2)) ℤ) (δ ε : ℕ) : MvMass.mass (slice p δ ε)≤MvMass.mass p :=
  (one_mass (one p δ) ε).trans (one_mass p δ)

noncomputable def separate : MvPolynomial (Fin (m+2)) R→+*Polynomial (Polynomial (MvPolynomial (Fin m) R)) :=
  (Polynomial.mapRingHom (MvPolynomial.finSuccEquiv R m).toRingHom).comp
    (MvPolynomial.finSuccEquiv R (m+1)).toRingHom

noncomputable def evaluate {K : Type*} [CommSemiring K] (f : R→+*K) (z : Fin m→K) :
    MvPolynomial (Fin (m+2)) R→+*Polynomial (Polynomial K) :=
  (Polynomial.mapRingHom (Polynomial.mapRingHom (MvPolynomial.eval₂Hom f z))).comp separate

theorem selected_coefficient {K : Type*} [CommSemiring K] (f : R→+*K) (z : Fin m→K)
    (p : MvPolynomial (Fin (m+2)) R) (δ ε : ℕ) :
    ((evaluate f z p).coeff δ).coeff ε=(slice p δ ε).eval₂ f z :=by
  simp only [evaluate,separate,RingHom.comp_apply,Polynomial.coe_mapRingHom,Polynomial.coeff_map,slice,one,
    MvPolynomial.coe_eval₂Hom]
  rfl

end LeanCanny.Algebra.MvTwoParameterCoefficient
