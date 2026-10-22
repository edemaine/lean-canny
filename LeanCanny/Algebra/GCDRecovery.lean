/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitiveCoordinates

/-!
# Linear-GCD coordinate recovery in Canny's Lemma 2.1

For a separating value `θ = a + c*b`, the polynomials `p₁(θ-c*x)` and `p₂(x)`
have exactly one common root, namely `b`. Separability makes their GCD linear.
Its first two coefficients recover `b` and then `a`, with a nonzero denominator.
This verifies the GCD specification. `SubresultantRecovery` connects it to a
symbolic first subresultant for nonzero directions and input degrees greater
than one. `CoordinateRecovery` includes the linear and zero-direction cases;
the full coordinate computation's space bound remains open.
-/

@[expose] public section

namespace LeanCanny.Algebra
open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

noncomputable def shiftedPolynomial (p : Polynomial K) (c : ℕ) (θ : L) : Polynomial L :=
  (p.map (algebraMap K L)).comp (C θ - C (c : L) * X)

@[simp] theorem eval_shiftedPolynomial (p : Polynomial K) (c : ℕ) (θ x : L) :
    (shiftedPolynomial p c θ).eval x = Polynomial.aeval (θ - (c : L) * x) p := by
  simp [shiftedPolynomial, Polynomial.eval_comp]

noncomputable def recoveryGCD (p₁ p₂ : Polynomial K) (c : ℕ) (θ : L) : Polynomial L := by
  classical
  exact EuclideanDomain.gcd (shiftedPolynomial p₁ c θ) (p₂.map (algebraMap K L))

theorem recoveryGCD_separable (p₁ p₂ : Polynomial K) (c : ℕ) (θ : L) (h₂ : p₂.Separable) :
    (recoveryGCD p₁ p₂ c θ).Separable := by
  classical
  exact Polynomial.separable_gcd_right _ h₂.map

theorem recoveryGCD_eq_linear (p₁ p₂ : Polynomial K) (c : ℕ) (a b : L)
    (h₁ : p₁ ≠ 0) (h₂ : p₂.Separable) (hs₂ : (p₂.map (algebraMap K L)).Splits)
    (hinj : Set.InjOn (shear c) (rootPairs (L := L) p₁ p₂ : Set (L × L)))
    (ha : Polynomial.aeval a p₁ = 0) (hb : Polynomial.aeval b p₂ = 0) :
    recoveryGCD p₁ p₂ c (shear c (a, b)) =
      C (recoveryGCD p₁ p₂ c (shear c (a, b))).leadingCoeff * (X - C b) := by
  classical
  let g := recoveryGCD p₁ p₂ c (shear c (a, b))
  have hsep : g.Separable := recoveryGCD_separable p₁ p₂ c _ h₂
  have hroot : g.eval b = 0 := by
    apply Polynomial.eval_gcd_eq_zero
    · rw [eval_shiftedPolynomial]
      simpa only [shear, add_sub_cancel_right] using ha
    · simpa only [Polynomial.eval_map_algebraMap] using hb
  have hs : g.Splits := hs₂.of_dvd (Polynomial.map_ne_zero h₂.ne_zero)
    (EuclideanDomain.gcd_dvd_right _ _)
  have hunique : ∀ x ∈ g.roots, x = b := by
    intro x hx
    have hxg := (Polynomial.mem_roots hsep.ne_zero).mp hx
    have hxpair := (Polynomial.isRoot_gcd_iff_isRoot_left_right).mp hxg
    have hx₁ : Polynomial.aeval (shear c (a, b) - (c : L) * x) p₁ = 0 := by
      simpa only [Polynomial.IsRoot, eval_shiftedPolynomial] using hxpair.1
    have hx₂ : Polynomial.aeval x p₂ = 0 := by
      simpa only [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using hxpair.2
    have hp := (mem_rootPairs p₁ p₂ h₁ h₂.ne_zero
      (shear c (a, b) - (c : L) * x, x)).mpr ⟨hx₁, hx₂⟩
    have hab := (mem_rootPairs p₁ p₂ h₁ h₂.ne_zero (a, b)).mpr ⟨ha, hb⟩
    have he : shear c (shear c (a, b) - (c : L) * x, x) = shear c (a, b) := by
      simp only [shear]
      ring
    exact congrArg Prod.snd (hinj hp hab he)
  apply Polynomial.eq_X_sub_C_of_separable_of_root_eq (i := RingHom.id L) hsep hroot
  · simpa only [Polynomial.map_id] using hs
  · simpa only [Polynomial.map_id, RingHom.id_apply] using hunique

/-- The coefficient formulas (6) and (7), including their denominator condition. -/
theorem recoveryGCD_spec (p₁ p₂ : Polynomial K) (c : ℕ) (a b : L)
    (h₁ : p₁ ≠ 0) (h₂ : p₂.Separable) (hs₂ : (p₂.map (algebraMap K L)).Splits)
    (hinj : Set.InjOn (shear c) (rootPairs (L := L) p₁ p₂ : Set (L × L)))
    (ha : Polynomial.aeval a p₁ = 0) (hb : Polynomial.aeval b p₂ = 0) :
    let g := recoveryGCD p₁ p₂ c (shear c (a, b))
    g.natDegree = 1 ∧ g.coeff 1 ≠ 0 ∧
      b = -g.coeff 0 / g.coeff 1 ∧ a = shear c (a, b) + (c : L) * (g.coeff 0 / g.coeff 1) := by
  let g := recoveryGCD p₁ p₂ c (shear c (a, b))
  have hlinear : g = C g.leadingCoeff * (X - C b) := recoveryGCD_eq_linear p₁ p₂ c a b h₁ h₂ hs₂ hinj ha hb
  have hlc : g.leadingCoeff ≠ 0 :=
    mt Polynomial.leadingCoeff_eq_zero.mp (recoveryGCD_separable p₁ p₂ c _ h₂).ne_zero
  have hzero : g.coeff 0 = -g.leadingCoeff * b := by
    simpa using congrArg (fun p : Polynomial L => p.coeff 0) hlinear
  have hone : g.coeff 1 = g.leadingCoeff := by
    simpa using congrArg (fun p : Polynomial L => p.coeff 1) hlinear
  have hratio : g.coeff 0 / g.coeff 1 = -b := by
    rw [hzero, hone]
    field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      g.natDegree = (C g.leadingCoeff * (X - C b)).natDegree := congrArg Polynomial.natDegree hlinear
      _ = 1 := by rw [Polynomial.natDegree_C_mul hlc, Polynomial.natDegree_X_sub_C]
  · rw [hone]
    exact hlc
  · rw [neg_div, hratio, neg_neg]
  · rw [hratio]
    simp only [shear]
    ring

end LeanCanny.Algebra
