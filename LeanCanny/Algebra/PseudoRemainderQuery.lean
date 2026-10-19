/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PseudoRemainderSpace
public import LeanCanny.Algebra.PseudoRemainderBounds

/-! # Tarski queries from integer pseudo-remainder seeds

The new seed is integral for integral inputs and has smaller degree than the
nonconstant head. Its positive scaling preserves the query. Thus the principal
determinants used for the answer have integer coefficients throughout.
-/

@[expose] public section

namespace LeanCanny.Algebra.PseudoRemainder
open Polynomial PrincipalSubresultant

variable {R S : Type*} [CommRing R] [LinearOrder R] [CommRing S] [LinearOrder S]

noncomputable def principalQuery (p f : R[X]) (d D : ℕ) : ℤ :=
  let s := seed p f d D
  permanencesMinusVariations ((List.range (d + 1)).reverse.map (signedPsc p s d s.natDegree))

theorem principalQuery_map (φ : R →+* S) (hi : Function.Injective φ)
    (hs : ∀ x, SignType.sign (φ x) = SignType.sign x) (p f : R[X]) (d D : ℕ) :
    principalQuery (p.map φ) (f.map φ) d D = principalQuery p f d D := by
  simp only [principalQuery, seed_map, natDegree_map_eq_of_injective hi]
  apply permanencesMinusVariations_congr
  simp only [List.map_map]
  apply List.map_congr_left
  intro j _
  change SignType.sign (signedPsc (p.map φ) ((seed p f d D).map φ) d
      (seed p f d D).natDegree j) =
    SignType.sign (signedPsc p (seed p f d D) d (seed p f d D).natDegree j)
  rw [signedPsc_map_map]
  exact hs _

end LeanCanny.Algebra.PseudoRemainder

namespace LeanCanny.Algebra.RootSignQueries
open Polynomial PrincipalSubresultant

/-- The positively scaled integer-style seed computes the same real-root query. -/
theorem tarskiQuery_eq_pseudoPrincipalQuery (p f : ℝ[X]) (d D : ℕ)
    (hp : p.natDegree = d) (hd : 0 < d) (hD : (f * p.derivative).natDegree ≤ D) :
    tarskiQuery p f = PseudoRemainder.principalQuery p f d D := by
  have hn : p ≠ 0 := by intro hz; rw [hz, natDegree_zero] at hp; omega
  have hs := PseudoRemainder.isTarskiSeed p f d D hp hn
  have hl : (PseudoRemainder.seed p f d D).natDegree < p.natDegree := by
    rw [hp]
    exact PseudoRemainder.seed_natDegree_lt p f d D hd hD
  have ht := remainderIndex_eq_permanences_signedPsc hl
  exact (Sturm.remainderIndex_tarskiSeed hs).symm.trans
    (by simpa only [hp, PseudoRemainder.principalQuery] using ht)

/-- Integral input queries reduce to signs of integral principal determinants.
The exponent and every coefficient bound remain finite binary control data. -/
theorem tarskiQuery_pseudo_int (p f : ℤ[X]) (d D : ℕ)
    (hp : p.natDegree = d) (hd : 0 < d) (hD : (f * p.derivative).natDegree ≤ D) :
    tarskiQuery (p.map (algebraMap ℤ ℝ)) (f.map (algebraMap ℤ ℝ)) =
      PseudoRemainder.principalQuery p f d D := by
  let φ := algebraMap ℤ ℝ
  have hi : Function.Injective φ := by
    intro a b h
    exact Int.cast_injective h
  have hp' : (p.map φ).natDegree = d := by rw [natDegree_map_eq_of_injective hi]; exact hp
  have hD' : (f.map φ * (p.map φ).derivative).natDegree ≤ D := by
    rw [derivative_map, ← Polynomial.map_mul, natDegree_map_eq_of_injective hi]
    exact hD
  rw [tarskiQuery_eq_pseudoPrincipalQuery (p.map φ) (f.map φ) d D hp' hd hD']
  apply PseudoRemainder.principalQuery_map φ hi
  intro z
  change SignType.sign (z : ℝ) = SignType.sign z
  exact sign_intCast z

end LeanCanny.Algebra.RootSignQueries
