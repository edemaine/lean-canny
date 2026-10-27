/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.InfinitesimalSignSpace
public import LeanCanny.Algebra.PolynomialSignedReflection
public import Mathlib.Algebra.Polynomial.Taylor

/-! # One-sided signs from streamed derivative signs

Taylor coefficients have the same signs as the corresponding derivatives.
Scanning these signs in increasing order recovers the sign on either side
of the center. No Taylor coefficients or neighborhood radius are computed.
-/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialLocalSign
open Polynomial
open scoped Classical

theorem tag_cast (s : SignType) : InfinitesimalSign.tag (s : ℤ) = InfinitesimalSign.encode s := by
  cases s <;> decide

theorem cast_eq_zero (s : SignType) : (s : ℤ) = 0 ↔ s = 0 := by
  cases s <;> decide

theorem scan_real (p : ℝ[X]) (n : ℕ) (hn : p.natDegree < n) :
    InfinitesimalSign.scan (fun k => (SignType.sign (p.coeff k) : ℤ)) n =
      InfinitesimalSign.encode (SignType.sign p.trailingCoeff) := by
  by_cases hp : p = 0
  · rw [InfinitesimalSign.scan_zero_prefix _ n (by
      intro k _
      simp only [hp, coeff_zero, sign_zero, SignType.coe_zero])]
    simp only [hp, trailingCoeff_zero, sign_zero, InfinitesimalSign.encode]
  · rw [InfinitesimalSign.scan_of_first_nonzero _ p.natTrailingDegree n
      (p.natTrailingDegree_le_natDegree.trans_lt hn)
      (by rw [ne_eq, cast_eq_zero, sign_eq_zero_iff]; exact coeff_natTrailingDegree_ne_zero.mpr hp)
      (by
        intro k hk
        simp only [coeff_eq_zero_of_lt_natTrailingDegree hk, sign_zero, SignType.coe_zero]), tag_cast]
    rfl

theorem derivative_sign (p : ℝ[X]) (x : ℝ) (k : ℕ) :
    SignType.sign (((Polynomial.derivative^[k]) p).eval x) = SignType.sign ((p.taylor x).coeff k) := by
  have he : ((Polynomial.derivative^[k]) p).eval x =
      (k.factorial : ℝ) * (p.taylor x).coeff k := by
    have H := (congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℝ) k) p).symm
    change (Polynomial.derivative^[k]) p = k.factorial • Polynomial.hasseDeriv k p at H
    rw [H, Polynomial.eval_smul, nsmul_eq_mul, Polynomial.taylor_coeff]
  rw [he, sign_mul, sign_pos (Nat.cast_pos.mpr (Nat.factorial_pos k)), one_mul]

noncomputable def right (p : ℝ[X]) (x : ℝ) : SignType := SignType.sign (p.taylor x).trailingCoeff
noncomputable def left (p : ℝ[X]) (x : ℝ) : SignType :=
  SignType.sign (((p.taylor x).comp (-X)).trailingCoeff)

theorem scan_right (p : ℝ[X]) (x : ℝ) (n : ℕ) (hn : p.natDegree < n) :
    InfinitesimalSign.scan (fun k => (SignType.sign (((Polynomial.derivative^[k]) p).eval x) : ℤ)) n =
      InfinitesimalSign.encode (right p x) := by
  simp only [derivative_sign]
  exact scan_real (p.taylor x) n (by simpa only [Polynomial.natDegree_taylor] using hn)

theorem scan_left (p : ℝ[X]) (x : ℝ) (n : ℕ) (hn : p.natDegree < n) :
    InfinitesimalSign.scan (fun k =>
      (SignType.sign ((-1 : ℝ) ^ k * ((Polynomial.derivative^[k]) p).eval x) : ℤ)) n =
      InfinitesimalSign.encode (left p x) := by
  have hd : ((p.taylor x).comp (-X)).natDegree < n :=
    (Polynomial.natDegree_comp_le.trans (by simp only [Polynomial.natDegree_neg, Polynomial.natDegree_X,
      Nat.mul_one, Polynomial.natDegree_taylor]; exact le_rfl)).trans_lt hn
  have H := scan_real ((p.taylor x).comp (-X)) n hd
  simp only [PolynomialSignedReflection.coefficient, sign_mul, ← derivative_sign] at H
  simpa only [sign_mul, left] using H

theorem right_eventually (p : ℝ[X]) (x : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → SignType.sign (p.eval (x + t)) = right p x := by
  obtain ⟨δ, hδ, H⟩ := InfinitesimalSign.sign_eval_eq_trailingCoeff (p.taylor x)
  refine ⟨δ, hδ, fun t ht htd => ?_⟩
  simpa only [Polynomial.taylor_eval, add_comm, right] using H t ht htd

theorem left_eventually (p : ℝ[X]) (x : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → SignType.sign (p.eval (x - t)) = left p x := by
  obtain ⟨δ, hδ, H⟩ := InfinitesimalSign.sign_eval_eq_trailingCoeff ((p.taylor x).comp (-X))
  refine ⟨δ, hδ, fun t ht htd => ?_⟩
  have he : (((p.taylor x).comp (-X)).eval t) = p.eval (x - t) := by
    rw [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, Polynomial.taylor_eval]
    congr 1
    ring
  simpa only [he, left] using H t ht htd

end LeanCanny.Algebra.PolynomialLocalSign
