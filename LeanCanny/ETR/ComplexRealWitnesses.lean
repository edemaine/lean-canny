/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexRealConstraints

/-! # Fresh existential witnesses beside a shared real circuit

Logical coordinates below `inputs` retain their addresses. All further
coordinates are relocated beyond the auxiliary wire interval. Completing the
circuit preserves those witnesses, so Boolean constraints may contain any
number of additional existential real coordinates.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit
open MvPolynomial
open scoped Classical

theorem StraightLine.run_preserves_after (env : ℕ → ℂ) (start : ℕ) (ops : List Operation)
    (i : ℕ) (hi : start + ops.length ≤ i) : StraightLine.run env start ops i = env i := by
  induction ops generalizing env start with
  | nil => rfl
  | cons op ops ih =>
    rw [run, ih _ _ (by simp only [List.length_cons] at hi; omega)]
    exact Function.update_of_ne (show i ≠ start by simp only [List.length_cons] at hi; omega) _ _

namespace RealQuery.Witnesses

def index (inputs fresh i : ℕ) : ℕ := if i < inputs then i else fresh + (i - inputs)

theorem index_unary {inputs fresh i : List Bool → ℕ}
    (hn : UnaryFn inputs) (hf : UnaryFn fresh) (hi : UnaryFn i) :
    UnaryFn (fun c => index (inputs c) (fresh c) (i c)) :=
  (UnaryFn.ite (FPPred.lt hi hn) hi (hf.add (hi.sub hn))).of_eq (fun _ => rfl)

theorem index_initial {inputs fresh i : ℕ} (hi : i < inputs) : index inputs fresh i = i := by
  exact ite_eq_left hi

theorem index_witness {inputs fresh i : ℕ} (hi : inputs ≤ i) :
    index inputs fresh i = fresh + (i - inputs) := by
  exact ite_eq_right (Nat.not_lt.mpr hi)

theorem index_injective (inputs fresh : ℕ) (hf : inputs ≤ fresh) : Function.Injective (index inputs fresh) := by
  intro i j he
  unfold index at he
  split_ifs at he <;> omega

theorem index_avoids_aux (inputs start : ℕ) (ops : List Operation) (hn : inputs ≤ start) (i : ℕ) :
    index inputs (start + ops.length) i < start ∨ start + ops.length ≤ index inputs (start + ops.length) i := by
  by_cases hi : i < inputs
  · left
    rw [index_initial hi]
    exact hi.trans_le hn
  · rw [index_witness (Nat.le_of_not_lt hi)]
    exact Or.inr (Nat.le_add_right ..)

theorem zero_constraints_with_iff (start : ℕ) (ops : List Operation) (outputs : List ℕ)
    (p : Formula) (f : ℕ → ℕ) (hw : StraightLine.WellFormed start ops)
    (ho : ∀ out ∈ outputs, out < start + ops.length)
    (hf : ∀ i < p.arity, f i < start ∨ start + ops.length ≤ f i) :
    WithConstraints start (StraightLine.gates start ops ++ outputs.map Gate.zero) (p.rename f) ↔
      ∃ x : ℕ → ℝ, (∀ out ∈ outputs,
        (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start ops out).eval₂ (Int.castRingHom ℝ) x = 0) ∧
        p.Holds (x ∘ f) := by
  constructor
  · rintro ⟨env, hg, hr, hpred⟩
    let x : ℕ → ℝ := fun i => (env i).re
    have hprogram : ∀ g ∈ StraightLine.gates start ops, g.Holds env :=
      fun g h => hg g (List.mem_append_left _ h)
    have hin : ∀ i < start, env i = (x i : ℂ) := by
      intro i hi
      apply Complex.ext
      · rfl
      · exact hr i hi
    refine ⟨x, ?_, (Formula.holds_rename _ _ p).mp hpred⟩
    intro out hout
    have hv := StraightLine.symbolic_value env start ops hw hprogram (fun i => (x i : ℂ)) hin out (ho out hout)
    have hz : env out = 0 := hg (.zero out) (List.mem_append_right _ (List.mem_map.mpr ⟨out, hout, rfl⟩))
    rw [polynomial_eval_ofReal] at hv
    have he : Complex.ofReal ((Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start ops out).eval₂
        (Int.castRingHom ℝ) x) = 0 := hv.symm.trans hz
    exact_mod_cast he
  · rintro ⟨x, hx, hpred⟩
    let env : ℕ → ℂ := StraightLine.run (fun i => (x i : ℂ)) start ops
    have hprogram : ∀ g ∈ StraightLine.gates start ops, g.Holds env := StraightLine.run_satisfies _ _ _ hw
    have hin : ∀ i < start, env i = (x i : ℂ) :=
      fun i hi => StraightLine.run_preserves_before _ _ _ i hi
    refine ⟨env, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hprogram g hg
      · obtain ⟨out, hout, rfl⟩ := List.mem_map.mp hg
        change env out = 0
        rw [StraightLine.symbolic_value env start ops hw hprogram (fun i => (x i : ℂ)) hin out (ho out hout),
          polynomial_eval_ofReal, hx out hout, Complex.ofReal_zero]
    · intro i hi
      rw [hin i hi]
      exact Complex.ofReal_im _
    · apply (Formula.holds_rename _ _ p).mpr
      apply (p.holds_congr (x ∘ f) ((fun i => (env i).re) ∘ f) ?_).mp hpred
      intro i hi
      have he : env (f i) = (x (f i) : ℂ) := by
        rcases hf i hi with hi | hi
        · exact hin (f i) hi
        · exact StraightLine.run_preserves_after _ start ops (f i) hi
      simp only [Function.comp_apply, he, Complex.ofReal_re]

theorem relocated_zero_constraints_iff (inputs start : ℕ) (ops : List Operation) (outputs : List ℕ)
    (p : Formula) (hn : inputs ≤ start) (hw : StraightLine.WellFormed start ops)
    (ho : ∀ out ∈ outputs, out < start + ops.length) :
    WithConstraints start (StraightLine.gates start ops ++ outputs.map Gate.zero)
        (p.rename (index inputs (start + ops.length))) ↔
      ∃ x : ℕ → ℝ, (∀ out ∈ outputs,
        (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start ops out).eval₂ (Int.castRingHom ℝ) x = 0) ∧
        p.Holds (x ∘ index inputs (start + ops.length)) :=
  zero_constraints_with_iff start ops outputs p _ hw ho (fun i _ => index_avoids_aux inputs start ops hn i)

end RealQuery.Witnesses
end LeanCanny.ETR.ComplexCircuit
