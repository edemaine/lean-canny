/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexFrozenEncoding
public import LeanCanny.ETR.ComplexDifferentialSymbolic
public import LeanCanny.Algebra.CoordinateSlicePolynomial

/-! # Exact polynomial slice computed by the frozen source

The input identity describes the original finite-coordinate polynomial. The
compiled frozen circuit computes its actual coordinate slice, including the
coefficient specialization at the supplied integer sample.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.FrozenSource
open MvPolynomial LeanCanny.Algebra
open scoped Classical

theorem polynomial_map_slice {n : ℕ} (t : Term) (low : MvPolynomial (Fin (n + 2)) ℤ)
    (ht : t.toPolynomial = rename Fin.val low) (sample : ℤ) :
    (polynomial sample t).map (Int.castRingHom ℂ) = rename Fin.val
      ((CoordinateSlicePolynomial.family low).map (Polynomial.eval₂RingHom (Int.castRingHom ℂ) (sample : ℂ))) := by
  apply MvPolynomial.funext
  intro x
  simp only [eval_map, eval_rename, Function.comp_def]
  rw [polynomial_eval, ← Term.eval₂_toPolynomial (inputs sample x) t, ht,
    eval₂_rename, CoordinateSlicePolynomial.eval_family]
  apply congrArg (fun y : Fin (n + 2) → ℂ => low.eval₂ (Int.castRingHom ℂ) y)
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [inputs]
  · simp [inputs]

theorem symbolic_output_map_slice {n : ℕ} (oldStart start : ℕ) (sample : ℤ) (t : Term)
    (low : MvPolynomial (Fin (n + 2)) ℤ) (hlow : t.toPolynomial = rename Fin.val low)
    (ht : t.arity ≤ oldStart) (hs : oldStart ≤ start) :
    (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start (program oldStart start sample t)
      (output oldStart start t)).map (Int.castRingHom ℂ) = rename Fin.val
        ((CoordinateSlicePolynomial.family low).map (Polynomial.eval₂RingHom (Int.castRingHom ℂ) (sample : ℂ))) := by
  rw [symbolic_output oldStart start sample t ht hs]
  exact polynomial_map_slice t low hlow sample

end LeanCanny.ETR.ComplexCircuit.FrozenSource
