/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ZeroCoordinateAccess
public import LeanCanny.CountingHierarchy.ParametricCoordinatePolynomial
public import LeanCanny.CountingHierarchy.SourceCriticalEvaluation

/-! # Source-derived residues of actual coordinate characteristic coefficients -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial PurePowerResidue

variable {p n : ℕ} [Fact p.Prime]

theorem sourceCoordinateCoefficient_cast (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (u k : ℕ) (i : Fin n)
    (hcut : criticalCoefficientPrimeCutoff n d < p) (value : List ℕ → ℕ)
    (hv : ∀ y, (value y : ZMod p) = MvPolynomial.eval₂ (Int.castRingHom (ZMod p))
      (fun j : Fin n => (y[j.val]?.getD 0 : ZMod p)) F) :
    (zeroCoordinateCoefficientValue p n d u i.val k value : ZMod p) =
      parameterEvaluation (u : ZMod p) ((parametricCoordinatePolynomial d F hF i).coeff k) := by
  have hp : 3 < p := by unfold criticalCoefficientPrimeCutoff at hcut; omega
  have hsmall : (F.map (Int.castRingHom (ZMod p))).totalDegree < p - 1 := by
    have := (map_degree_le (Int.castRingHom (ZMod p)) F).trans hF
    unfold criticalCoefficientPrimeCutoff at hcut
    omega
  have hgrid : (d + 1) * ((d + 1) ^ n * (d + 2) + n * d + 1) + 1 < p := by
    unfold criticalCoefficientPrimeCutoff criticalTraceDegreeBound at hcut
    omega
  have hdim : (d + 1) ^ n < p - 1 := by unfold criticalCoefficientPrimeCutoff at hcut; omega
  have hdim₂ : (d + 1) ^ n * (d + 1) ^ n < p - 1 := by
    unfold criticalCoefficientPrimeCutoff at hcut
    omega
  have hcoeff := zeroCoordinateCoefficientValue_eq d hd (F.map (Int.castRingHom (ZMod p)))
    ((map_degree_le (Int.castRingHom (ZMod p)) F).trans hF) u k i hsmall hp hgrid hdim hdim₂ value
    (fun y => by simpa only [MvPolynomial.eval_map] using hv y)
  have hK : ∀ j : ℕ, 1 ≤ j → j ≤ (d + 1) ^ n → (j : ZMod p) ≠ 0 := by
    intro j hj hle
    exact (ZMod.natCast_eq_zero_iff j p).not.mpr (by
      intro hdiv
      have := Nat.le_of_dvd (by omega : 0 < j) hdiv
      omega)
  have hmap := congrArg (fun Q : Polynomial (ZMod p) => Q.coeff k)
    (parametricCoordinatePolynomial_map d hd F hF i (u : ZMod p) hK)
  rw [Polynomial.coeff_map] at hmap
  rw [hcoeff, ZMod.natCast_zmod_val]
  exact hmap.symm

end LeanCanny.CountingHierarchy
