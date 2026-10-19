/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.LayeredMatrix
public import LeanCanny.Algebra.MatrixPowerControllerCorrect

/-!
# Streaming an ordered product with the matrix-power machine

The layered reduction lets the existing power continuation machine evaluate a
product interval. Its correctness, exact work clock, encoded controller
simulation, and modular state-size bound apply directly. Matrix-entry access
still has the original power-machine contract: the layered matrix must be
supplied by a suitable callback, whose computation is not free.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixProduct
open Matrix

variable {R : Type*} [Semiring R] {n : ℕ}

def intervalQuery (s e : ℕ) (i j : Fin n) : MatrixPower.Query ((s + e + 1) * n) where
  height := e.size
  exponent := e
  row := finProdFinEquiv (⟨s, by omega⟩, i)
  col := finProdFinEquiv (⟨s + e, by omega⟩, j)

theorem run_product (A : ℕ → Matrix (Fin n) (Fin n) R) (s e : ℕ) (i j : Fin n) :
    (MatrixPower.step (layeredFin A (s + e + 1)))^[
      MatrixPower.work ((s + e + 1) * n) e.size e + 1]
        (.eval (intervalQuery s e i j) []) = .done (product A s e i j) := by
  rw [show intervalQuery s e i j = ⟨e.size, e,
      finProdFinEquiv (⟨s, by omega⟩, i), finProdFinEquiv (⟨s + e, by omega⟩, j)⟩ from rfl,
    MatrixPower.run_pow, layeredFin_pow_product]

theorem run_controller_product (ops : MatrixPower.Controller.Callbacks) (c : List Bool)
    (A : ℕ → Matrix (Fin n) (Fin n) R) (s e : ℕ) (i j : Fin n)
    (enc : R → List Bool)
    (hc : MatrixPower.Controller.CorrectAt ops c (layeredFin A (s + e + 1)) enc) :
    (MatrixPower.Controller.step ops)^[MatrixPower.work ((s + e + 1) * n) e.size e + 1]
      (Complexity.pair c (MatrixPower.stateBits enc (.eval (intervalQuery s e i j) []))) =
        Complexity.pair c (MatrixPower.stateBits (n := (s + e + 1) * n) enc
          (.done (product A s e i j))) := by
  rw [MatrixPower.Controller.iterate_packet ops c _ enc hc, run_product]

theorem run_product_residue_length (m : ℕ) [NeZero m]
    (A : ℕ → Matrix (Fin n) (Fin n) (ZMod m)) (s e t : ℕ) (i j : Fin n) :
    (MatrixPower.stateBits MatrixPower.residueBits
      ((MatrixPower.step (layeredFin A (s + e + 1)))^[t]
        (.eval (intervalQuery s e i j) []))).length ≤
      64 * (((s + e + 1) * n).size + e.size + m.size + 1) ^ 2 :=
  MatrixPower.run_residueBits_quadratic m (layeredFin A (s + e + 1)) e t _ _

end LeanCanny.Algebra.MatrixProduct
