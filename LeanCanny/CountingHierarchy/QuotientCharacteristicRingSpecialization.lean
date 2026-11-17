/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PowerTraceCharacteristic
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Characteristic specialization to characteristic-zero integral domains -/

public section

namespace LeanCanny.CountingHierarchy.PurePowerResidue

open Polynomial MvPolynomial

/-- Comparison in the target fraction field proves the integral identity
 before passing to real or finite-field coefficients. -/
theorem multiplicationMatrix_charpoly_map_charZero {S T : Type*}
    [CommRing S] [CommRing T] [IsDomain T] [CharZero T] {n : ℕ}
    (φ : S →+* T) (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) S) :
    ((multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly).map φ =
      (multiplicationMatrix (by omega : 1 ≤ d + 1) (fun i => (r i).map φ)
        (fun i => (map_degree_le φ _).trans_lt ((hr i).trans_lt (Nat.lt_succ_self d)))
        (v.map φ)).charpoly := by
  let K := FractionRing T
  let η : T →+* K := algebraMap T K
  have hη : Function.Injective η := IsFractionRing.injective T K
  apply Polynomial.map_injective η hη
  rw [Polynomial.map_map]
  have hK (j : ℕ) (hj : 1 ≤ j) (_hle : j ≤ (d + 1) ^ n) : (j : K) ≠ 0 := by
    exact_mod_cast (by omega : j ≠ 0)
  have h₁ := multiplicationMatrix_charpoly_map (η.comp φ) d hd r hr v hK
  have h₂ := multiplicationMatrix_charpoly_map η d hd (fun i => (r i).map φ)
    (fun i => (map_degree_le φ _).trans (hr i)) (v.map φ) hK
  refine h₁.trans ((multiplicationMatrix_charpoly_congr (by omega : 1 ≤ d + 1)
    _ _ _ _ _ _ ?_ ?_).trans h₂.symm)
  · funext i
    exact (MvPolynomial.map_map φ η (r i)).symm
  · exact (MvPolynomial.map_map φ η v).symm

end LeanCanny.CountingHierarchy.PurePowerResidue
