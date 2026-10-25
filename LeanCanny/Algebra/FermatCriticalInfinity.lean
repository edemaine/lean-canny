/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RowSpanSpecialization
public import LeanCanny.Algebra.MacaulayProjectiveCriterion

/-! # Critical equations at infinity for a pure-power leading form

For the coordinate direction, the non-base critical equations force all
non-base coordinates to vanish. The leading hypersurface equation then forces
the base coordinate to vanish. Surjectivity of the full Macaulay row map
transfers this root-free specialization to every injective coefficient map.
-/

@[expose] public section
namespace LeanCanny.Algebra.FermatCriticalInfinity
open MvPolynomial
open scoped Classical BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

noncomputable def native (a : R) (N : ℕ) (v : Fin n → R) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) R :=
  Fin.cons (C a * ∑ j : Fin (n + 1), X j ^ N)
    (fun i => C (a * (N : R)) * (X i.succ ^ (N - 1) - C (v i) * X 0 ^ (N - 1)))

def degrees (n N : ℕ) : Fin (n + 1) → ℕ := Fin.cons N (fun _ => N - 1)

theorem degrees_pos (N : ℕ) (hN : 1 < N) (j : Fin (n + 1)) : 0 < degrees n N j := by
  refine Fin.cases ?_ (fun _ => ?_) j <;> simp only [degrees, Fin.cons_zero, Fin.cons_succ] <;> omega

theorem homogeneous (a : R) (N : ℕ) (v : Fin n → R) (j : Fin (n + 1)) :
    (native a N v j).IsHomogeneous (degrees n N j) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [native, degrees, Fin.cons_zero]
    apply IsHomogeneous.C_mul
    apply IsHomogeneous.sum
    intro i _
    simpa only [one_mul] using (isHomogeneous_X (R := R) i).pow N
  · simp only [native, degrees, Fin.cons_succ]
    apply IsHomogeneous.C_mul
    apply IsHomogeneous.sub
    · simpa only [one_mul] using (isHomogeneous_X (R := R) i.succ).pow (N - 1)
    · apply IsHomogeneous.C_mul
      simpa only [one_mul] using (isHomogeneous_X (R := R) (0 : Fin (n + 1))).pow (N - 1)

theorem map_native (φ : R →+* S) (a : R) (N : ℕ) (v : Fin n → R) (j : Fin (n + 1)) :
    (native a N v j).map φ = native (φ a) N (fun i => φ (v i)) j := by
  refine Fin.cases ?_ (fun _ => ?_) j <;>
    simp [native, map_sum]

theorem zero_direction_root {K : Type*} [Field K] [CharZero K]
    (a : K) (ha : a ≠ 0) (N : ℕ) (hN : 1 < N) (x : Fin (n + 1) → K)
    (hx : ∀ j, eval x (native a N (fun _ : Fin n => 0) j) = 0) : x = 0 := by
  have hcoef : a * (N : K) ≠ 0 := mul_ne_zero ha (Nat.cast_ne_zero.mpr (by omega))
  have htail (i : Fin n) : x i.succ = 0 := by
    have h := hx i.succ
    simp only [native, Fin.cons_succ, eval_mul, eval_C, eval_sub, eval_pow, eval_X,
      zero_mul, sub_zero] at h
    exact (pow_eq_zero_iff (by omega : N - 1 ≠ 0)).mp ((mul_eq_zero.mp h).resolve_left hcoef)
  have hbase : x 0 = 0 := by
    have h := hx 0
    simp only [native, Fin.cons_zero, map_mul, eval_C, map_sum, map_pow, eval_X, map_add,
      Fin.sum_univ_succ, htail, zero_pow (by omega : N ≠ 0), Finset.sum_const_zero, add_zero] at h
    exact (pow_eq_zero_iff (by omega : N ≠ 0)).mp ((mul_eq_zero.mp h).resolve_left ha)
  funext j
  exact Fin.cases hbase htail j

variable {K L : Type*} [Field K] [CharZero K] [Field L]

noncomputable def system (a : K) (N : ℕ) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) (MvPolynomial (Fin n) K) :=
  native (C a) N (fun i => X i)

/-- A generic direction has no critical point at infinity. The target map
only needs to be injective; its target field need not be algebraically closed. -/
theorem no_root_injective (a : K) (ha : a ≠ 0) (N : ℕ) (hN : 1 < N)
    (F : Type*) [Field F] [IsAlgClosed F] [Algebra K F]
    (ψ : MvPolynomial (Fin n) K →+* L) (hψ : Function.Injective ψ)
    (x : Fin (n + 1) → L) (hx : ∀ j, (system a N j).eval₂ ψ x = 0) : x = 0 := by
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let φ : MvPolynomial (Fin n) K →+* F := eval₂Hom (algebraMap K F) (fun _ => 0)
  let d := degrees n N
  let W := (Macaulay.level d).size
  have hW : Macaulay.level d < 2 ^ W := Nat.lt_size_self _
  have hp (j : Fin (n + 1)) : (system a N j).IsHomogeneous (d j) := homogeneous _ _ _ _
  have hroot (y : Fin (n + 1) → F) (hy : ∀ j, eval y ((system a N j).map φ) = 0) : y = 0 := by
    apply zero_direction_root (algebraMap K F a) (by
      intro h
      apply ha
      apply (algebraMap K F).injective
      simpa only [map_zero] using h) N hN y
    intro j
    simpa only [system, map_native, φ, eval₂Hom_C, eval₂Hom_X'] using hy j
  have hs : Function.Surjective (fun v => Matrix.vecMul v ((Macaulay.fullMatrix (system a N) d W).map φ)) := by
    rw [Macaulay.fullMatrix_map]
    exact Macaulay.fullMatrix_surjective_of_no_nonzero_root _ d W (fun j => (hp j).map φ)
      (degrees_pos N hN) hW hroot
  have hsψ := RowSpanSpecialization.generic_surjective φ ψ hψ (Macaulay.fullMatrix (system a N) d W) hs
  rw [Macaulay.fullMatrix_map] at hsψ
  apply Macaulay.no_nonzero_root_of_fullMatrix_surjective _ d W (fun j => (hp j).map ψ) hW hsψ x
  intro j
  simpa only [eval_map] using hx j

end LeanCanny.Algebra.FermatCriticalInfinity
