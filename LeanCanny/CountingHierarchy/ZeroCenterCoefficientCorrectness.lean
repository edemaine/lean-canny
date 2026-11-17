/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ZeroCenterAccess
public import LeanCanny.CountingHierarchy.SeparatedPotentialDegree

/-! # Actual zero-center characteristic coefficients from source evaluation -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial PurePowerResidue
open scoped Classical

theorem zeroCoefficientValue_eq {p n : ℕ} [Fact p.Prime] (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) (ZMod p)) (hF : F.totalDegree ≤ d + 1) (u k : ℕ)
    (hsmall : F.totalDegree < p - 1) (hp : 3 < p)
    (hcut : (d + 1) * ((d + 1) ^ n * (d + 2) + n * d + 1) + 1 < p)
    (hD : (d + 1) ^ n < p - 1) (hD₂ : (d + 1) ^ n * (d + 1) ^ n < p - 1)
    (value : List ℕ → ℕ)
    (hv : ∀ y, (value y : ZMod p) = eval (fun i : Fin n => (y[i.val]?.getD 0 : ZMod p)) F) :
    zeroCoefficientValue p n d u k value =
      ((multiplicationMatrix (by omega : 1 ≤ d + 1) (criticalLower (d + 1) (fun _ => 0) (u : ZMod p) F)
        (criticalLower_degree (d + 1) (by omega) _ _ _ hF)
        (deformedPolynomial (d + 1) (fun _ => 0) (u : ZMod p) F)).charpoly.coeff k).val := by
  let r := criticalLower (d + 1) (fun _ : Fin n => (0 : ZMod p)) (u : ZMod p) F
  let v := deformedPolynomial (d + 1) (fun _ : Fin n => (0 : ZMod p)) (u : ZMod p) F
  have hr (i : Fin n) : (r i).totalDegree ≤ d := by
    have h := criticalLower_degree (d + 1) (by omega) (fun _ => (0 : ZMod p)) (u : ZMod p) F hF i
    dsimp only [r]
    omega
  have hvdeg : v.totalDegree ≤ d + 2 := by
    dsimp only [v, deformedPolynomial]
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le (potentialPolynomial_totalDegree_le _ _) _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simpa only [MvPolynomial.totalDegree_C, Nat.zero_add] using hF.trans (by omega))
  have hnum (j : ℕ) (hj : j ≤ (d + 1) ^ n) :
      (v ^ j * jacobian (d + 1) r).totalDegree ≤ (d + 1) ^ n * (d + 2) + n * d :=
    quotient_trace_numerator_degree d r hr v (d + 2) ((d + 1) ^ n) j hvdeg hj
  exact quotientCharacteristicValue_eq d hd r hr v hnum hcut hD hD₂
    (fun z => zeroObjectiveValue p n (d + 1) u z value)
    (fun z => criticalJacobianValue p n (d + 1) u z value)
    (fun i z => zeroLowerValue p n u i z value)
    (fun s _ => zeroObjectiveValue_cast F (d + 1) u (by omega) _ value hv)
    (fun s _ => zeroJacobianValue_cast F (d + 1) u _ value hsmall hp hv)
    (fun i s _ => zeroLowerValue_cast F (d + 1) u (by omega) i _ value hsmall hp hv)

end LeanCanny.CountingHierarchy
