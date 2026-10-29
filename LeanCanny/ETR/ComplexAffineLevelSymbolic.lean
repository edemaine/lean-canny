/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexAffineLevelCorrect

/-! # Symbolic ancestral levels in an existing shared program

The fresh circuit preserves all earlier wires. Its selected output is exactly
the level polynomial in those wires, allowing successive stages to share the
same original ambient variables.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.AffineLevel
open MvPolynomial
open scoped Classical BigOperators

noncomputable def polynomial (D : Inputs) (wire : ℕ → MvPolynomial ℕ ℤ) : MvPolynomial ℕ ℤ :=
  if D.mode = 1 then ∑ i ∈ Finset.range D.count, MvPolynomial.C (D.normal i) * wire (D.left + i)
  else if D.mode = 2 then
    (∑ i ∈ Finset.range D.count, MvPolynomial.C (D.normal i) * wire (D.left + i)) +
      ∑ i ∈ Finset.range D.count, MvPolynomial.C (D.normal i) * wire (D.right + i)
  else MvPolynomial.C D.constant

theorem polynomial_eval (D : Inputs) (wire : ℕ → MvPolynomial ℕ ℤ) (x : ℕ → ℂ) :
    (polynomial D wire).eval₂ (Int.castRingHom ℂ) x = value D (fun i => (wire i).eval₂ (Int.castRingHom ℂ) x) := by
  unfold polynomial value
  split_ifs <;> simp only [eval₂_sum, eval₂_mul, eval₂_C, eval₂_add, Int.coe_castRingHom]

theorem symbolic (D : Inputs) (h : D.Valid) (wire : ℕ → MvPolynomial ℕ ℤ) :
    Differential.symbolicRun wire D.base (program D) (output D) = polynomial D wire := by
  apply Differential.eq_of_eval_complex
  intro x
  let W := Differential.symbolicRun wire D.base (program D)
  let env : ℕ → ℂ := fun i => (W i).eval₂ (Int.castRingHom ℂ) x
  have hR : Differential.Realizes W D.base (program D) :=
    Differential.symbolicRun_realizes wire D.base (program D) (wellFormed D h)
  have hg : ∀ g ∈ gates D, g.Holds env := Differential.realizes_gates_eval W D.base (program D) hR x
  have hp (i : ℕ) (hi : i < D.base) : env i = (wire i).eval₂ (Int.castRingHom ℂ) x := by
    dsimp only [env, W]
    rw [Differential.symbolicRun_preserves_before wire D.base (program D) i hi]
  exact (output_sound D env hg).trans ((value_congr D h env _ hp).trans (polynomial_eval D wire x).symm)

end LeanCanny.ETR.ComplexCircuit.AffineLevel
