/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralScalarGeneratorController

/-! # A carrier-free view of scalar companion control values -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralScalarGeneratorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def viewValue (modulus N D row col oldRow oldCol : ℕ) (leading : ZMod modulus) (reply : List Bool) : List Bool :=
  if ¬(col + 1 < N) ∧ D ≤ N ∧ N - D ≤ row then
    residueBits (-((Nat.fromBitsLE reply : ZMod modulus) * leading ^ (D - 1 - (row - (N - D)))))
  else residueBits (if col + 1 < N ∧ row = col + 1 ∧ oldRow = oldCol then (1 : ZMod modulus) else 0)

theorem program_view (F : Family) (task answer : List Bool → List Bool) (q : List Bool) :
    (program F task).value answer q = viewValue (F.modulus q) (F.scalarDegree q) (F.selectedDegree q)
      (F.row q).val (F.col q).val (F.oldRow q).val (F.oldCol q).val (F.leading q)
      (answer (task (coefficientQuery F q))) := by
  unfold SingleCall.Program.value program
  dsimp only
  unfold finish
  rw [pairFst_pair, pairSnd_pair]
  simp only [request, finishValue, power, index, immediate, decide_eq_true_eq, viewValue]

end LeanCanny.Algebra.IntegralScalarGeneratorBits
