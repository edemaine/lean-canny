/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralParameterInverse
public import LeanCanny.Algebra.TrailingCoefficientMap
/-! # Exact guarded specialization of constant-denominator parameter inverses

A specialization can kill an original trailing coefficient. A fixed index
therefore selects its own symbolic coefficient shift; the ordinary inverse
commutes with specialization when the original trailing coefficient survives.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralParameterInverse
open Polynomial
variable {R S :Type*} [CommRing R] [CommRing S]

private theorem coeff_iterate_divX (p :R[X]) (τ k :ℕ) :
    ((Polynomial.divX^[τ]) p).coeff k=p.coeff (k+τ):=by
  induction τ generalizing p k with
  | zero=>rfl
  | succ τ IH=>
    simp only [Function.iterate_succ_apply',coeff_divX,IH]
    congr 1
    omega

/-- The symbolic branch for a fixed specialized trailing index. -/
noncomputable def inverseAt (p :R[X]) (τ :ℕ) :R[X]:=-((Polynomial.divX^[τ+1]) p)

theorem coeff_inverseAt (p :R[X]) (τ k :ℕ) :
    (inverseAt p τ).coeff k=-p.coeff (k+1+τ):=by
  rw [inverseAt,coeff_neg,coeff_iterate_divX]
  congr 2
  omega

theorem inverseAt_map (φ :R→+*S) (p :R[X]) (τ :ℕ) :
    (inverseAt p τ).map φ=inverseAt (p.map φ) τ:=by
  ext k
  simp only [coeff_map,coeff_inverseAt,map_neg]

theorem inverseAt_natTrailingDegree (p :R[X]) :inverseAt p p.natTrailingDegree=inverse p:=by
  ext k
  rw [coeff_inverseAt,coeff_inverse]

/-- The guards concern the actual mapped coefficients, and permit a map with
kernel as well as a specialized trailing index larger than the original one. -/
theorem natTrailingDegree_map_at (φ :R→+*S) (p :R[X]) (τ :ℕ)
    (Hbelow :∀k<τ,φ (p.coeff k)=0) (Hτ :φ (p.coeff τ)≠0) :
    (p.map φ).natTrailingDegree=τ:=by
  have HC :(p.map φ).coeff τ≠0:=by simpa only [coeff_map] using Hτ
  have HP :p.map φ≠0:=by
    intro HZ
    exact HC (by rw [HZ,coeff_zero])
  exact le_antisymm (natTrailingDegree_le_of_ne_zero HC)
    (le_natTrailingDegree HP (fun k hk=>by rw [coeff_map];exact Hbelow k hk))

theorem denominator_map_at (φ :R→+*S) (p :R[X]) (τ :ℕ)
    (Hbelow :∀k<τ,φ (p.coeff k)=0) (Hτ :φ (p.coeff τ)≠0) :
    denominator (p.map φ)=φ (p.coeff τ):=by
  simp only [denominator,trailingCoeff,natTrailingDegree_map_at φ p τ Hbelow Hτ,coeff_map]

theorem inverse_map_at (φ :R→+*S) (p :R[X]) (τ :ℕ)
    (Hbelow :∀k<τ,φ (p.coeff k)=0) (Hτ :φ (p.coeff τ)≠0) :
    inverse (p.map φ)=(inverseAt p τ).map φ:=by
  ext k
  simp only [coeff_inverse,natTrailingDegree_map_at φ p τ Hbelow Hτ,
    coeff_map,coeff_inverseAt,map_neg]

theorem denominator_map_of_survives (φ :R→+*S) (p :R[X]) (H :φ p.trailingCoeff≠0) :
    denominator (p.map φ)=φ (denominator p):=
  trailingCoeff_map_of_survives φ p H

theorem inverse_map_of_survives (φ :R→+*S) (p :R[X]) (H :φ p.trailingCoeff≠0) :
    inverse (p.map φ)=(inverse p).map φ:=by
  have HT :φ (p.coeff p.natTrailingDegree)≠0:=H
  have HB :∀k<p.natTrailingDegree,φ (p.coeff k)=0:=by
    intro k hk
    rw [coeff_eq_zero_of_lt_natTrailingDegree hk,map_zero]
  rw [inverse_map_at φ p p.natTrailingDegree HB HT,inverseAt_natTrailingDegree]

end LeanCanny.Algebra.IntegralParameterInverse
