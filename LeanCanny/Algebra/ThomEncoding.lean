/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Algebra.Polynomial.Roots

/-! # Derivative signs identify real polynomial roots

Each common sign condition on a polynomial and all its derivatives is an
interval. For a nonzero polynomial, such a condition containing a root therefore
contains only that point. The bounded signature
can be queried by derivative index; no numerical approximation is involved.
-/

@[expose] public section
namespace LeanCanny.Algebra.ThomEncoding
open Polynomial
open scoped Classical

noncomputable def sign (p : ℝ[X]) (x : ℝ) (k : ℕ) : SignType :=
  SignType.sign ((Polynomial.derivative^[k] p).eval x)

private theorem sign_interval_of_derivative (p : ℝ[X]) (a b : ℝ) (hab : a ≤ b)
    (hs : SignType.sign (p.eval a) = SignType.sign (p.eval b))
    (hd : ∀ z ∈ Set.Icc a b, SignType.sign (p.derivative.eval z) = SignType.sign (p.derivative.eval a)) :
    ∀ z ∈ Set.Icc a b, SignType.sign (p.eval z) = SignType.sign (p.eval a) := by
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  by_cases hp : 0 ≤ p.derivative.eval a
  · have hm : MonotoneOn (fun x => p.eval x) (Set.Icc a b) :=
      monotoneOn_of_deriv_nonneg (convex_Icc a b) p.differentiable.continuous.continuousOn p.differentiableOn (by
        intro z hz
        rw [(p.hasDerivAt z).deriv]
        apply sign_nonneg_iff.mp
        rw [hd z (interior_subset hz)]
        exact sign_nonneg_iff.mpr hp)
    intro z hz
    have hL := SignType.sign.monotone (hm ha hz hz.1)
    have hU := SignType.sign.monotone (hm hz hb hz.2)
    rw [← hs] at hU
    exact le_antisymm hU hL
  · have hm : AntitoneOn (fun x => p.eval x) (Set.Icc a b) :=
      antitoneOn_of_deriv_nonpos (convex_Icc a b) p.differentiable.continuous.continuousOn p.differentiableOn (by
        intro z hz
        rw [(p.hasDerivAt z).deriv]
        apply sign_nonpos_iff.mp
        rw [hd z (interior_subset hz)]
        exact sign_nonpos_iff.mpr (le_of_lt (lt_of_not_ge hp)))
    intro z hz
    have hU := SignType.sign.monotone (hm ha hz hz.1)
    have hL := SignType.sign.monotone (hm hz hb hz.2)
    rw [← hs] at hL
    exact le_antisymm hU hL

theorem interval (D : ℕ) : ∀ (p : ℝ[X]) (a b : ℝ), p.natDegree ≤ D → a ≤ b →
    (∀ k ≤ D, sign p a k = sign p b k) →
    ∀ z ∈ Set.Icc a b, ∀ k ≤ D, sign p z k = sign p a k := by
  induction D with
  | zero =>
    intro p a b hD _ _ z _ k hk
    have hk' : k = 0 := by omega
    have hp : p = C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (by omega)
    simp only [hk', sign, Function.iterate_zero_apply]
    apply congrArg SignType.sign
    rw [hp]
    simp only [Polynomial.eval_C]
  | succ D ih =>
    intro p a b hD hab hs
    have hd : p.derivative.natDegree ≤ D := (Polynomial.natDegree_derivative_le p).trans (by omega)
    have hds : ∀ k ≤ D, sign p.derivative a k = sign p.derivative b k := by
      intro k hk
      simpa only [sign, Function.iterate_succ_apply] using hs (k + 1) (by omega)
    have hdi := ih p.derivative a b hd hab hds
    have hzero := sign_interval_of_derivative p a b hab
      (by simpa only [sign, Function.iterate_zero_apply] using hs 0 (by omega))
      (fun z hz => by simpa only [sign, Function.iterate_zero_apply] using hdi z hz 0 (by omega))
    intro z hz k hk
    cases k with
    | zero => exact hzero z hz
    | succ k =>
      simpa only [sign, Function.iterate_succ_apply] using hdi z hz k (by omega)

private theorem root_eq_of_le (p : ℝ[X]) (hp : p ≠ 0) (D : ℕ) (hD : p.natDegree ≤ D)
    (a b : ℝ) (hab : a ≤ b) (ha : p.eval a = 0) (hs : ∀ k ≤ D, sign p a k = sign p b k) : a = b := by
  by_contra he
  have hab' : a < b := lt_of_le_of_ne hab he
  have hz : ∀ z ∈ Set.Icc a b, p.eval z = 0 := by
    intro z hzi
    apply sign_eq_zero_iff.mp
    have h := interval D p a b hD hab hs z hzi 0 (by omega)
    simpa only [sign, Function.iterate_zero_apply, ha, sign_zero] using h
  apply hp
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (Set.Ioo_infinite hab').mono
  intro z hzi
  exact hz z ⟨hzi.1.le, hzi.2.le⟩

theorem root_eq (p : ℝ[X]) (hp : p ≠ 0) (D : ℕ) (hD : p.natDegree ≤ D)
    (a b : ℝ) (ha : p.eval a = 0) (hb : p.eval b = 0)
    (hs : ∀ k ≤ D, sign p a k = sign p b k) : a = b := by
  rcases le_total a b with hab | hba
  · exact root_eq_of_le p hp D hD a b hab ha hs
  · exact (root_eq_of_le p hp D hD b a hba hb (fun k hk => (hs k hk).symm)).symm

noncomputable def signature (p : ℝ[X]) (D : ℕ) (x : ℝ) : Fin (D + 1) → SignType := fun k => sign p x k.val

theorem signature_injective (p : ℝ[X]) (hp : p ≠ 0) (D : ℕ) (hD : p.natDegree ≤ D) :
    Function.Injective (fun x : {x : ℝ // p.IsRoot x} => signature p D x.val) := by
  intro a b he
  apply Subtype.ext
  apply root_eq p hp D hD a.val b.val a.property b.property
  intro k hk
  exact congrFun he ⟨k, by omega⟩

end LeanCanny.Algebra.ThomEncoding
