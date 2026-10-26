/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexInterleavedQuery

/-! # Finite source polynomials with arbitrary formula witnesses

Only the designated finite coordinates affect the circuit output polynomials.
All remaining formula coordinates are independent existential real witnesses,
even if their logical names coincide with original auxiliary wire addresses.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.RealQuery.Interleaved
open MvPolynomial
open scoped Classical

def zeroGates {n : ℕ} (start : ℕ) (ops : List Operation)
    (models : List (ℕ × MvPolynomial (Fin n) ℤ)) : List Gate :=
  StraightLine.gates start ops ++ models.map (fun z => .zero z.1)

theorem zeroGates_arity {n : ℕ} (start : ℕ) (ops : List Operation)
    (models : List (ℕ × MvPolynomial (Fin n) ℤ)) (hw : StraightLine.WellFormed start ops)
    (ho : ∀ z ∈ models, z.1 < start + ops.length) :
    ∀ g ∈ zeroGates start ops models, g.arity ≤ start + ops.length := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact StraightLine.gates_arity start ops hw g hg
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hg
    exact Nat.succ_le_of_lt (ho z hz)

theorem finite_correct {n : ℕ} (start : ℕ) (ops : List Operation)
    (models : List (ℕ × MvPolynomial (Fin n) ℤ)) (p : Formula)
    (hn : n ≤ start) (hw : StraightLine.WellFormed start ops)
    (ho : ∀ z ∈ models, z.1 < start + ops.length)
    (hmodel : ∀ z ∈ models,
      Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start ops z.1 = rename Fin.val z.2) :
    InputSatisfiable n start (zeroGates start ops models) p ↔
      ∃ x : ℕ → ℝ, (∀ z ∈ models, z.2.eval₂ (Int.castRingHom ℝ) (fun i => x i.val) = 0) ∧ p.Holds x := by
  constructor
  · rintro ⟨x, env, hg, hr, hinput, hp⟩
    let y : ℕ → ℝ := fun i => (env i).re
    have hprogram : ∀ g ∈ StraightLine.gates start ops, g.Holds env :=
      fun g h => hg g (List.mem_append_left _ h)
    have hin : ∀ i < start, env i = (y i : ℂ) := by
      intro i hi
      apply Complex.ext
      · rfl
      · exact hr i hi
    have he : y ∘ Fin.val = fun i : Fin n => x i.val := by
      funext i
      exact congrArg Complex.re (hinput i.val i.isLt)
    refine ⟨x, ?_, hp⟩
    intro z hz
    have hv := StraightLine.symbolic_value env start ops hw hprogram (fun i => (y i : ℂ)) hin z.1 (ho z hz)
    have hzero : env z.1 = 0 := hg (.zero z.1) (List.mem_append_right _ (List.mem_map.mpr ⟨z, hz, rfl⟩))
    rw [hmodel z hz, polynomial_eval_ofReal, eval₂_rename, he] at hv
    have hvzero : Complex.ofReal (z.2.eval₂ (Int.castRingHom ℝ) (fun i => x i.val)) = 0 := hv.symm.trans hzero
    exact_mod_cast hvzero
  · rintro ⟨x, hx, hp⟩
    let env : ℕ → ℂ := StraightLine.run (fun i => (x i : ℂ)) start ops
    have hprogram : ∀ g ∈ StraightLine.gates start ops, g.Holds env := StraightLine.run_satisfies _ _ _ hw
    have hin : ∀ i < start, env i = (x i : ℂ) :=
      fun i hi => StraightLine.run_preserves_before _ _ _ i hi
    refine ⟨x, env, ?_, ?_, (fun i hi => hin i (hi.trans_le hn)), hp⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hprogram g hg
      · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hg
        change env z.1 = 0
        rw [StraightLine.symbolic_value env start ops hw hprogram (fun i => (x i : ℂ)) hin z.1 (ho z hz),
          hmodel z hz, polynomial_eval_ofReal, eval₂_rename]
        have he : (z.2.eval₂ (Int.castRingHom ℝ) (x ∘ Fin.val)) = 0 := hx z hz
        rw [he, Complex.ofReal_zero]
    · intro i hi
      rw [hin i hi]
      exact Complex.ofReal_im _

theorem port_finite_realizes {n : ℕ} (start : ℕ) (ops : List Operation)
    (models : List (ℕ × MvPolynomial (Fin n) ℤ)) (x : ℕ → ℝ) (port : ℕ → ℕ) (e : Fin n ≃ Fin n)
    (hn : n ≤ start) (he : ∀ i : Fin n, port i.val = (e i).val)
    (hw : StraightLine.WellFormed start ops) (ho : ∀ z ∈ models, z.1 < start + ops.length)
    (hmodel : ∀ z ∈ models,
      Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start ops z.1 =
        rename Fin.val (rename e z.2)) :
    PortRealizes n start port (zeroGates start ops models) x ↔
      ∀ z ∈ models, z.2.eval₂ (Int.castRingHom ℝ) (fun i => x i.val) = 0 := by
  constructor
  · rintro ⟨env, hg, hr, hinput⟩
    let y : ℕ → ℝ := fun i => (env i).re
    have hprogram : ∀ g ∈ StraightLine.gates start ops, g.Holds env :=
      fun g h => hg g (List.mem_append_left _ h)
    have hin : ∀ i < start, env i = (y i : ℂ) := by
      intro i hi
      apply Complex.ext
      · rfl
      · exact hr i hi
    have hev : (y ∘ Fin.val) ∘ e = fun i : Fin n => x i.val := by
      funext i
      have hv := congrArg Complex.re (hinput i.val i.isLt)
      rw [he i] at hv
      exact hv
    intro z hz
    have hv := StraightLine.symbolic_value env start ops hw hprogram (fun i => (y i : ℂ)) hin z.1 (ho z hz)
    have hzero : env z.1 = 0 := hg (.zero z.1) (List.mem_append_right _ (List.mem_map.mpr ⟨z, hz, rfl⟩))
    rw [hmodel z hz, polynomial_eval_ofReal, eval₂_rename, eval₂_rename, hev] at hv
    have hvzero : Complex.ofReal (z.2.eval₂ (Int.castRingHom ℝ) (fun i => x i.val)) = 0 := hv.symm.trans hzero
    exact_mod_cast hvzero
  · intro hx
    let y : ℕ → ℝ := fun i => if h : i < n then x (e.symm ⟨i, h⟩).val else 0
    have hy : ∀ i : Fin n, y (e i).val = x i.val := by
      intro i
      simp only [y, dite_eq_left (e i).isLt, e.symm_apply_apply]
    have hev : (y ∘ Fin.val) ∘ e = fun i : Fin n => x i.val := funext hy
    let env : ℕ → ℂ := StraightLine.run (fun i => (y i : ℂ)) start ops
    have hprogram : ∀ g ∈ StraightLine.gates start ops, g.Holds env := StraightLine.run_satisfies _ _ _ hw
    have hin : ∀ i < start, env i = (y i : ℂ) :=
      fun i hi => StraightLine.run_preserves_before _ _ _ i hi
    refine ⟨env, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hprogram g hg
      · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hg
        change env z.1 = 0
        rw [StraightLine.symbolic_value env start ops hw hprogram (fun i => (y i : ℂ)) hin z.1 (ho z hz),
          hmodel z hz, polynomial_eval_ofReal, eval₂_rename, eval₂_rename, hev, hx z hz, Complex.ofReal_zero]
    · intro i hi
      rw [hin i hi]
      exact Complex.ofReal_im _
    · intro i hi
      rw [he ⟨i, hi⟩, hin _ ((e ⟨i, hi⟩).isLt.trans_le hn), hy]

theorem port_finite_correct {n : ℕ} (start : ℕ) (ops : List Operation)
    (models : List (ℕ × MvPolynomial (Fin n) ℤ)) (p : Formula) (port : ℕ → ℕ) (e : Fin n ≃ Fin n)
    (hn : n ≤ start) (he : ∀ i : Fin n, port i.val = (e i).val)
    (hw : StraightLine.WellFormed start ops) (ho : ∀ z ∈ models, z.1 < start + ops.length)
    (hmodel : ∀ z ∈ models,
      Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start ops z.1 =
        rename Fin.val (rename e z.2)) :
    PortSatisfiable n start port (zeroGates start ops models) p ↔
      ∃ x : ℕ → ℝ, (∀ z ∈ models, z.2.eval₂ (Int.castRingHom ℝ) (fun i => x i.val) = 0) ∧ p.Holds x := by
  rw [portSatisfiable_iff]
  apply exists_congr
  intro x
  exact and_congr (port_finite_realizes start ops models x port e hn he hw ho hmodel) Iff.rfl

end LeanCanny.ETR.ComplexCircuit.RealQuery.Interleaved
