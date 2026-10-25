/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCriticalKernelPSPACE
public import Mathlib.Algebra.BigOperators.Fin

/-! # Finite-coordinate semantics of affine critical-kernel queries

A coefficient-map and variable-renaming identity identifies the actual source
polynomial. It transports its value, gradient, and Hessian together, including
both directions of the normalized root correspondence.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.CriticalKernel
open MvPolynomial
open scoped Classical BigOperators

variable {n : ℕ}

noncomputable def finiteSelected (p : MvPolynomial (Fin (n + 1)) ℂ) (j : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) ℂ := if j.val = 0 then p else pderiv j p
noncomputable def finiteEntry (p : MvPolynomial (Fin (n + 1)) ℂ) (j k : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) ℂ := if j.val = 0 then pderiv k p else pderiv k (pderiv j p)
noncomputable def finiteCriticalValue (p : MvPolynomial (Fin (n + 1)) ℂ) (v : ℕ → ℤ)
    (x : Fin (n + 1) → ℂ) (j : Fin (n + 1)) : ℂ :=
  (finiteSelected p j).eval x + (coefficient v j.val : ℂ) * (pderiv ⟨0, by omega⟩ p).eval x
noncomputable def finiteKernelValue (p : MvPolynomial (Fin (n + 1)) ℂ) (v : ℕ → ℤ)
    (x u : Fin (n + 1) → ℂ) (j : Fin (n + 1)) : ℂ :=
  ∑ k : Fin (n + 1), ((finiteEntry p j k).eval x +
    (coefficient v j.val : ℂ) * (pderiv k (pderiv ⟨0, by omega⟩ p)).eval x) * u k

def FiniteBad (p : MvPolynomial (Fin (n + 1)) ℂ) (v : ℕ → ℤ) (chart : Fin (n + 1)) : Prop :=
  ∃ x u : Fin (n + 1) → ℂ, u chart = 1 ∧
    ∀ j, finiteCriticalValue p v x j = 0 ∧ finiteKernelValue p v x u j = 0

theorem mapped_eval (P : MvPolynomial ℕ ℤ) (p : MvPolynomial (Fin (n + 1)) ℂ)
    (hP : P.map (Int.castRingHom ℂ) = rename Fin.val p) (x : ℕ → ℂ) :
    P.eval₂ (Int.castRingHom ℂ) x = p.eval (fun i => x i.val) := by
  rw [← eval_map, hP, eval_rename]
  rfl

theorem mapped_partial (P : MvPolynomial ℕ ℤ) (p : MvPolynomial (Fin (n + 1)) ℂ)
    (hP : P.map (Int.castRingHom ℂ) = rename Fin.val p) (j : Fin (n + 1)) :
    (pderiv j.val P).map (Int.castRingHom ℂ) = rename Fin.val (pderiv j p) := by
  rw [← pderiv_map, hP, pderiv_rename Fin.val_injective]

theorem criticalValue_fin (P : MvPolynomial ℕ ℤ) (p : MvPolynomial (Fin (n + 1)) ℂ)
    (hP : P.map (Int.castRingHom ℂ) = rename Fin.val p) (v : ℕ → ℤ) (x : ℕ → ℂ) (j : Fin (n + 1)) :
    criticalValue P v x j.val = finiteCriticalValue p v (fun i => x i.val) j := by
  have hs : (selectedPolynomial P j.val).eval₂ (Int.castRingHom ℂ) x =
      (finiteSelected p j).eval (fun i => x i.val) := by
    unfold selectedPolynomial finiteSelected
    split_ifs
    · exact mapped_eval P p hP x
    · exact mapped_eval _ _ (mapped_partial P p hP j) x
  exact congrArg₂ (· + ·) hs (congrArg ((coefficient v j.val : ℂ) * ·)
    (mapped_eval _ _ (mapped_partial P p hP ⟨0, by omega⟩) x))

theorem kernelValue_fin (P : MvPolynomial ℕ ℤ) (p : MvPolynomial (Fin (n + 1)) ℂ)
    (hP : P.map (Int.castRingHom ℂ) = rename Fin.val p) (v : ℕ → ℤ) (x u : ℕ → ℂ) (j : Fin (n + 1)) :
    kernelValue P (n + 1) v x u j.val = finiteKernelValue p v (fun i => x i.val) (fun i => u i.val) j := by
  unfold kernelValue finiteKernelValue
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  have he : (entryPolynomial P j.val k.val).eval₂ (Int.castRingHom ℂ) x =
      (finiteEntry p j k).eval (fun i => x i.val) := by
    unfold entryPolynomial finiteEntry
    split_ifs
    · exact mapped_eval _ _ (mapped_partial P p hP k) x
    · exact mapped_eval _ _ (mapped_partial _ _ (mapped_partial P p hP j) k) x
  have hb := mapped_eval _ _ (mapped_partial _ _ (mapped_partial P p hP ⟨0, by omega⟩) k) x
  rw [he, hb]

theorem bad_iff_finite (P : MvPolynomial ℕ ℤ) (p : MvPolynomial (Fin (n + 1)) ℂ)
    (hP : P.map (Int.castRingHom ℂ) = rename Fin.val p) (v : ℕ → ℤ) (chart : Fin (n + 1)) :
    Bad P (n + 1) v chart.val ↔ FiniteBad p v chart := by
  constructor
  · rintro ⟨x, u, hn, hr⟩
    refine ⟨fun i => x i.val, fun i => u i.val, hn, fun j => ?_⟩
    exact ⟨(criticalValue_fin P p hP v x j).symm.trans (hr j.val j.isLt).1,
      (kernelValue_fin P p hP v x u j).symm.trans (hr j.val j.isLt).2⟩
  · rintro ⟨x, u, hn, hr⟩
    let e : (Fin (n + 1) → ℂ) → ℕ → ℂ := fun f i => if h : i < n + 1 then f ⟨i, h⟩ else 0
    have he (f : Fin (n + 1) → ℂ) : (fun i : Fin (n + 1) => e f i.val) = f := by
      funext i
      simp only [e, i.isLt, dite_true, Fin.eta]
    refine ⟨e x, e u, ?_, fun j hj => ?_⟩
    · simpa only [e, chart.isLt, dite_true, Fin.eta] using hn
    · have hc := criticalValue_fin P p hP v (e x) ⟨j, hj⟩
      have hk := kernelValue_fin P p hP v (e x) (e u) ⟨j, hj⟩
      rw [he x] at hc
      rw [he x, he u] at hk
      exact ⟨hc.trans (hr ⟨j, hj⟩).1, hk.trans (hr ⟨j, hj⟩).2⟩

theorem finite_bad_map_iff {R : Type*} [CommRing R] (φ : R →+* ℂ) (p : MvPolynomial (Fin (n + 1)) R)
    (v : ℕ → ℤ) (w : Fin n → ℂ) (hv : ∀ j : Fin n, (v j.val : ℂ) = w j) (chart : Fin (n + 1)) :
    FiniteBad (p.map φ) v chart ↔ ∃ x u : Fin (n + 1) → ℂ, u chart = 1 ∧
      (p.eval₂ φ x = 0 ∧ ∀ j : Fin n,
        (pderiv j.succ p).eval₂ φ x - w j * (pderiv 0 p).eval₂ φ x = 0) ∧
      ((∑ k : Fin (n + 1), (pderiv k p).eval₂ φ x * u k) = 0 ∧ ∀ j : Fin n,
        (∑ k : Fin (n + 1), ((pderiv k (pderiv j.succ p)).eval₂ φ x -
          w j * (pderiv k (pderiv 0 p)).eval₂ φ x) * u k) = 0) := by
  have hzero : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
  simp only [FiniteBad, finiteCriticalValue, finiteKernelValue, finiteSelected, finiteEntry,
    Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ, Nat.add_one_ne_zero, ite_true, ite_false,
    coefficient, Nat.add_sub_cancel_right, Int.cast_zero, zero_mul, add_zero,
    Int.cast_neg, hv, neg_mul, ← sub_eq_add_neg, pderiv_map, eval_map, hzero, forall_and]

end LeanCanny.ETR.ComplexCircuit.CriticalKernel
