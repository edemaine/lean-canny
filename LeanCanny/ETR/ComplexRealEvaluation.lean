/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexRealQuery
public import LeanCanny.ETR.ComplexDifferentialSymbolic

/-! # Real polynomial semantics of acyclic shared-circuit queries

Assignments satisfying an acyclic circuit agree with its polynomial model.
With real initial wires, zero-output constraints are precisely real polynomial
equations. Auxiliary values cannot create additional complex solutions.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit
open MvPolynomial
open scoped Classical

theorem StraightLine.gates_unique (env env' : ℕ → ℂ) (start : ℕ) (ops : List Operation)
    (hw : WellFormed start ops)
    (hg : ∀ g ∈ gates start ops, g.Holds env) (hg' : ∀ g ∈ gates start ops, g.Holds env')
    (hin : ∀ i < start, env i = env' i) : ∀ i < start + ops.length, env i = env' i := by
  induction ops generalizing start with
  | nil => simpa only [List.length_nil, Nat.add_zero] using hin
  | cons op ops ih =>
    have h0 : env start = env' start :=
      ((Operation.gate_holds_iff op start env).mp (hg _ (List.mem_cons_self ..))).trans
        ((Operation.eval_congr op start env env' hw.1 hin).trans
          ((Operation.gate_holds_iff op start env').mp (hg' _ (List.mem_cons_self ..))).symm)
    have hb : ∀ i < start + 1, env i = env' i := by
      intro i hi
      by_cases h : i < start
      · exact hin i h
      · have he : i = start := by omega
        exact he ▸ h0
    intro i hi
    apply ih (start + 1) hw.2 (fun g h => hg g (List.mem_cons_of_mem _ h))
      (fun g h => hg' g (List.mem_cons_of_mem _ h)) hb i
    simp only [List.length_cons] at hi
    omega

theorem StraightLine.symbolic_value (env : ℕ → ℂ) (start : ℕ) (ops : List Operation)
    (hw : WellFormed start ops) (hg : ∀ g ∈ gates start ops, g.Holds env) (x : ℕ → ℂ)
    (hin : ∀ i < start, env i = x i) (out : ℕ) (ho : out < start + ops.length) :
    env out = (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start ops out).eval₂ (Int.castRingHom ℂ) x := by
  have hr := Differential.symbolicRun_realizes (fun i => (X i : MvPolynomial ℕ ℤ)) start ops hw
  apply gates_unique env (fun i => (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start ops i).eval₂
    (Int.castRingHom ℂ) x) start ops hw hg (Differential.realizes_gates_eval _ _ _ hr x) ?_ out ho
  intro i hi
  rw [Differential.symbolicRun_preserves_before _ _ _ i hi, eval₂_X]
  exact hin i hi

theorem polynomial_eval_ofReal (p : MvPolynomial ℕ ℤ) (x : ℕ → ℝ) :
    p.eval₂ (Int.castRingHom ℂ) (fun i => (x i : ℂ)) = Complex.ofReal (p.eval₂ (Int.castRingHom ℝ) x) := by
  induction p using MvPolynomial.induction_on with
  | C z =>
    rw [eval₂_C, eval₂_C]
    simp
  | add p q hp hq => simp only [eval₂_add, hp, hq, Complex.ofReal_add]
  | mul_X p i hp => simp only [eval₂_mul, eval₂_X, hp, Complex.ofReal_mul]

namespace RealQuery

theorem zero_constraints_iff (start : ℕ) (ops : List Operation) (outputs : List ℕ)
    (hw : StraightLine.WellFormed start ops) (ho : ∀ out ∈ outputs, out < start + ops.length) :
    Satisfiable start (StraightLine.gates start ops ++ outputs.map Gate.zero) ↔
      ∃ x : ℕ → ℝ, ∀ out ∈ outputs,
        (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start ops out).eval₂ (Int.castRingHom ℝ) x = 0 := by
  constructor
  · rintro ⟨env, hg, hr⟩
    let x : ℕ → ℝ := fun i => (env i).re
    have hprogram : ∀ g ∈ StraightLine.gates start ops, g.Holds env :=
      fun g h => hg g (List.mem_append_left _ h)
    have hin : ∀ i < start, env i = (x i : ℂ) := by
      intro i hi
      apply Complex.ext
      · rfl
      · exact hr i hi
    refine ⟨x, ?_⟩
    intro out hout
    have hv := StraightLine.symbolic_value env start ops hw hprogram (fun i => (x i : ℂ)) hin out (ho out hout)
    have hz : env out = 0 := hg (.zero out) (List.mem_append_right _ (List.mem_map.mpr ⟨out, hout, rfl⟩))
    rw [polynomial_eval_ofReal] at hv
    have he : Complex.ofReal ((Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start ops out).eval₂
        (Int.castRingHom ℝ) x) = 0 := hv.symm.trans hz
    exact_mod_cast he
  · rintro ⟨x, hx⟩
    let env : ℕ → ℂ := StraightLine.run (fun i => (x i : ℂ)) start ops
    have hprogram : ∀ g ∈ StraightLine.gates start ops, g.Holds env := StraightLine.run_satisfies _ _ _ hw
    have hin : ∀ i < start, env i = (x i : ℂ) :=
      fun i hi => StraightLine.run_preserves_before _ _ _ i hi
    refine ⟨env, ?_, ?_⟩
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

end RealQuery
end LeanCanny.ETR.ComplexCircuit
