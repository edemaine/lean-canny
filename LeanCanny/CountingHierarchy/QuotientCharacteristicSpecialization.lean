/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.QuotientCharacteristicEvaluation
public import LeanCanny.CountingHierarchy.QuotientTraceSpecialization

/-! # Characteristic residues after arbitrary coefficient specialization -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial PurePowerResidue
open scoped Classical

/-- The modular algorithm computes the reduction of the source quotient's
 characteristic coefficient. The source may itself be a polynomial ring,
 allowing parameter evaluation before the finite-field computation. -/
theorem quotientCharacteristicValue_eq_specialization
    {S : Type*} [CommRing S] {p n B m : ℕ} [Fact p.Prime] (φ : S →+* ZMod p)
    (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) S)
    (hdeg : ∀ k ≤ (d + 1) ^ n, (v ^ k * jacobian (d + 1) r).totalDegree ≤ B)
    (hcut : (d + 1) * (B + 1) + 1 < p)
    (hD : (d + 1) ^ n < p - 1) (hdegree : (d + 1) ^ n * (d + 1) ^ n < p - 1)
    (value Jvalue : List ℕ → ℕ) (rvalue : ℕ → List ℕ → ℕ)
    (hvalue : ∀ s < p ^ n, (value (gridPoint p n s) : ZMod p) =
      eval (fun i : Fin n => (((gridPoint p n s)[i.val]?.getD 0 : ℕ) : ZMod p)) (v.map φ))
    (hJvalue : ∀ s < p ^ n, (Jvalue (gridPoint p n s) : ZMod p) =
      eval (fun i : Fin n => (((gridPoint p n s)[i.val]?.getD 0 : ℕ) : ZMod p))
        ((jacobian (d + 1) r).map φ))
    (hrvalue : ∀ i : Fin n, ∀ s < p ^ n, (rvalue i.val (gridPoint p n s) : ZMod p) =
      eval (fun j : Fin n => (((gridPoint p n s)[j.val]?.getD 0 : ℕ) : ZMod p)) ((r i).map φ)) :
    quotientCharacteristicValue p n (d + 1) B m value Jvalue rvalue =
      (φ ((multiplicationMatrix (by omega : 1 ≤ d + 1) r
        (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly.coeff m)).val := by
  let M := multiplicationMatrix (by omega : 1 ≤ d + 1) r
    (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v
  have hdim : Fintype.card (NormalIndex n (d + 1)) = (d + 1) ^ n := card_normalIndex _ _
  have htr (k : ℕ) (hk : k ≤ Fintype.card (NormalIndex n (d + 1))) :
      (quotientTraceValue p n (d + 1) B k value Jvalue rvalue : ZMod p) =
        ((M.map φ) ^ k).trace := by
    rw [multiplicationMatrix_map_trace_pow φ d hd r hr v k]
    unfold quotientTraceValue
    have hnum : ((v.map φ) ^ k * jacobian (d + 1) (fun i => (r i).map φ)).totalDegree ≤ B := by
      rw [← jacobian_map, ← map_pow, ← map_mul]
      exact (map_degree_le φ _).trans (hdeg k (by simpa only [hdim] using hk))
    apply residueValue_cast (by omega) (fun i => (r i).map φ)
      (fun i => (map_degree_le φ _).trans_lt ((hr i).trans_lt (Nat.lt_succ_self d)))
      _ hnum hcut _ rvalue _ hrvalue
    intro s hs
    rw [ZMod.natCast_mod, Nat.cast_mul,
      Turing.MultiTapeTM.powMod_of_ne_zero (Fact.out : p.Prime).ne_zero,
      ZMod.natCast_mod, Nat.cast_pow, hvalue s hs, hJvalue s hs, jacobian_map,
      map_mul, map_pow]
  have hc := traceExponentialCoefficient_eq_charpoly (M.map φ)
    (by simpa only [hdim] using hD) (by simpa only [hdim] using hdegree) m
    (fun k => quotientTraceValue p n (d + 1) B k value Jvalue rvalue) htr
  simpa only [quotientCharacteristicValue, hdim, Matrix.charpoly_map,
    Polynomial.coeff_map] using hc

end LeanCanny.CountingHierarchy
