/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Nullstellensatz
/-! # Heights of affine point ideals

An affine point ideal in `n` variables has height `n`. Splitting off one
variable and applying the polynomial height formula proves the result
without a Jacobian or smoothness hypothesis. The weak Nullstellensatz gives
the same height for every maximal ideal over an algebraically closed field.
-/

@[expose] public section

open MvPolynomial
open scoped Classical
namespace LeanCanny.Algebra.MvPolynomialPointHeight

variable {K : Type*} [Field K]
theorem height_point (n : ℕ) (x : Fin n → K) :
    (vanishingIdeal K {x} : Ideal (MvPolynomial (Fin n) K)).height = n := by
  induction n with
  | zero =>
    have h := Ideal.height_le_ringKrullDim_of_ne_top
      ((inferInstance : (vanishingIdeal K {x} : Ideal (MvPolynomial (Fin 0) K)).IsPrime).ne_top)
    have hd : ringKrullDim (MvPolynomial (Fin 0) K) = 0 := by simp
    rw [hd] at h
    exact le_antisymm (WithBot.coe_le_coe.mp h) bot_le
  | succ n ih =>
    let e := MvPolynomial.finSuccEquiv K n
    let t : Fin n → K := fun j => x j.succ
    let P : Ideal (MvPolynomial (Fin n) K) := vanishingIdeal K {t}
    let Q : Ideal (Polynomial (MvPolynomial (Fin n) K)) :=
      RingHom.ker (Polynomial.eval₂RingHom (MvPolynomial.eval t) (x 0))
    have : Q.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun a =>
      ⟨Polynomial.C (MvPolynomial.C a), by simp⟩)
    have : Q.LiesOver P := by
      constructor
      ext f
      change f ∈ vanishingIdeal K {t} ↔ Polynomial.C f ∈ Q
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      change MvPolynomial.aeval t f = 0 ↔ (Polynomial.eval₂RingHom (MvPolynomial.eval t) (x 0)) (Polynomial.C f) = 0
      simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, MvPolynomial.aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id]
    have he : Q.comap e.toRingHom = (vanishingIdeal K {x} : Ideal (MvPolynomial (Fin (n + 1)) K)) := by
      ext f
      rw [Ideal.mem_comap, MvPolynomial.mem_vanishingIdeal_singleton_iff]
      change (Polynomial.eval₂RingHom (MvPolynomial.eval t) (x 0)) (e f) = 0 ↔ MvPolynomial.aeval x f = 0
      have hx : Fin.cons (x 0) t = x := by
        funext j
        exact Fin.cases rfl (fun _ => rfl) j
      have hv := MvPolynomial.eval_eq_eval_mv_eval' t (x 0) f
      rw [hx, Polynomial.eval_map] at hv
      change (MvPolynomial.eval₂ (RingHom.id K) x f) = _ at hv
      simp only [MvPolynomial.aeval_def, Algebra.algebraMap_self]
      exact ⟨fun h => hv.trans h, fun h => hv.symm.trans h⟩
    calc
      (vanishingIdeal K {x} : Ideal (MvPolynomial (Fin (n + 1)) K)).height = Q.height := by
        rw [← he]
        exact e.toRingEquiv.height_comap Q
      _ = P.height + 1 := Polynomial.height_eq_height_add_one P Q
      _ = (n + 1 : ℕ) := by rw [ih t]; simp

theorem height_maximal [IsAlgClosed K] (n : ℕ) (P : Ideal (MvPolynomial (Fin n) K)) [P.IsMaximal] :
    P.height = n := by
  obtain ⟨x, rfl⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K (inferInstance : P.IsMaximal)
  exact height_point n x

end LeanCanny.Algebra.MvPolynomialPointHeight
