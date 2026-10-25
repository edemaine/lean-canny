/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PartialDerivativeDegree
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.MvPolynomial.CommRing
public import LeanCanny.Algebra.MvCoefficientMass
public import Mathlib.Data.Nat.Size

/-! # A square affine system for critical values

The extra coordinate records the value of the polynomial at a gradient zero.
Finite gradient zero sets give finite augmented zero sets, even when the
critical points are singular.
-/

@[expose] public section
namespace LeanCanny.Algebra.CriticalValueSystem
open MvPolynomial
open scoped Classical

variable {n : ℕ} {R K : Type*} [CommRing R] [Field K]

noncomputable def equations (p : MvPolynomial (Fin n) R) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) R :=
  Fin.cons (X 0 - rename Fin.succ p) (fun i => rename Fin.succ (pderiv i p))

def degrees (n D : ℕ) : Fin (n + 1) → ℕ := Fin.cons D (fun _ => D - 1)

theorem degrees_pos (D : ℕ) (hD : 1 < D) (j : Fin (n + 1)) : 0 < degrees n D j := by
  refine Fin.cases (by simpa [degrees] using (show 0 < D by omega))
    (fun _ => by simp only [degrees, Fin.cons_succ]; omega) j

theorem degree_le [Nontrivial R] (p : MvPolynomial (Fin n) R) (D : ℕ)
    (hp : p.totalDegree ≤ D) (hD : 0 < D) (j : Fin (n + 1)) :
    (equations p j).totalDegree ≤ degrees n D j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · apply (totalDegree_sub _ _).trans
    apply max_le
    · simpa [degrees] using (show 1 ≤ D by omega)
    · exact (totalDegree_rename_le _ _).trans hp
  · exact (totalDegree_rename_le _ _).trans
      ((PartialDerivativeDegree.degree_le p i).trans (Nat.sub_le_sub_right hp 1))

theorem eval_equations (φ : R →+* K) (p : MvPolynomial (Fin n) R)
    (z : Fin (n + 1) → K) (j : Fin (n + 1)) :
    (equations p j).eval₂ φ z =
      (Fin.cons (z 0 - p.eval₂ φ (fun i => z i.succ))
        (fun i => (pderiv i p).eval₂ φ (fun i => z i.succ)) : Fin (n + 1) → K) j := by
  refine Fin.cases ?_ (fun i => ?_) j <;>
    simp [equations, eval₂_rename, Function.comp_def]

theorem finite_zero_set (φ : R →+* K) (p : MvPolynomial (Fin n) R)
    (hf : {x : Fin n → K | ∀ i, (pderiv i p).eval₂ φ x = 0}.Finite) :
    {z : Fin (n + 1) → K | ∀ j, (equations p j).eval₂ φ z = 0}.Finite := by
  apply (hf.image (fun x => (Fin.cons (p.eval₂ φ x) x : Fin (n + 1) → K))).subset
  intro z hz
  have hhead := hz 0
  rw [eval_equations] at hhead
  have he : z 0 = p.eval₂ φ (fun i => z i.succ) := sub_eq_zero.mp hhead
  refine ⟨fun i => z i.succ, ?_, ?_⟩
  · intro i
    simpa only [eval_equations, Fin.cons_succ] using hz i.succ
  · change Fin.cons (p.eval₂ φ (fun i => z i.succ)) (fun i => z i.succ) = z
    rw [← he]
    exact Fin.cons_self_tail z

theorem critical_root (φ : R →+* K) (p : MvPolynomial (Fin n) R)
    (x : Fin n → K) (hx : ∀ i, (pderiv i p).eval₂ φ x = 0) (j : Fin (n + 1)) :
    (equations p j).eval₂ φ (Fin.cons (p.eval₂ φ x) x) = 0 := by
  rw [eval_equations]
  refine Fin.cases (by simp) (fun i => ?_) j
  simpa only [Fin.cons_succ] using hx i

omit [CommRing R] [Field K] in
theorem mass_bound (p : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : p.totalDegree ≤ D) (hp : MvMass.mass p ≤ 2 ^ b)
    (j : Fin (n + 1)) : MvMass.mass (equations p j) ≤ 2 ^ (b + D.size + 1) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · apply (MvMass.sub_le _ _).trans
    have hm := (MvMass.rename_le Fin.succ p).trans hp
    have hb : 2 ^ b ≤ 2 ^ (b + D.size) := Nat.pow_le_pow_right (by decide) (by omega)
    have hpos : 1 ≤ 2 ^ (b + D.size) := Nat.one_le_two_pow
    simp only [MvMass.X]
    rw [pow_succ]
    omega
  · apply (MvMass.rename_le _ _).trans
    apply (MvMass.pderiv_le p i).trans
    calc
      p.totalDegree * MvMass.mass p ≤ 2 ^ D.size * 2 ^ b :=
        Nat.mul_le_mul (hD.trans (Nat.lt_size_self D).le) hp
      _ = 2 ^ (b + D.size) := by rw [← pow_add, Nat.add_comm]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

omit [CommRing R] [Field K] in
theorem coefficient_bound (p : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : p.totalDegree ≤ D) (hp : MvMass.mass p ≤ 2 ^ b)
    (j : Fin (n + 1)) (e : Fin (n + 1) →₀ ℕ) :
    ((equations p j).coeff e).natAbs ≤ 2 ^ (b + D.size + 1) :=
  (MvMass.coeff_le _ _).trans (mass_bound p D b hD hp j)

end LeanCanny.Algebra.CriticalValueSystem
