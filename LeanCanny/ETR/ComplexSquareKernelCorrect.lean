/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexSquareKernelCircuit
public import LeanCanny.ETR.ComplexRealConstraints

/-! # Exact all-root semantics of square-system kernel queries

The witness is an arbitrary complex point with a normalized nonzero kernel
vector. Additional source outputs can impose parent equations and inverse
matrix guards. These semantics do not assume that any roots are regular,
isolated, or finite.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.SquareKernel
open MvPolynomial
open scoped Classical BigOperators

def constraints (start m : ℕ) (ops : List Operation) (guardCount : ℕ)
    (guardOutputs : ℕ → ℕ) (chart : ℕ) : List Gate :=
  [.constant (start + chart) 1] ++ ((List.range m).flatMap (fun j =>
    [.zero (equationWire start m ops j), .zero (kernelWire start m ops j)]) ++
      (List.range guardCount).map (fun j => .zero (valueWire start m ops (guardOutputs j))))

def query (start m offset : ℕ) (ops : List Operation) (outputs : ℕ → ℕ)
    (guardCount : ℕ) (guardOutputs : ℕ → ℕ) (chart : ℕ) : List Gate :=
  StraightLine.gates (zeroWire start m) (program start m offset ops outputs) ++
    constraints start m ops guardCount guardOutputs chart

def At (wire : ℕ → MvPolynomial ℕ ℤ) (m offset : ℕ) (outputs : ℕ → ℕ)
    (guardCount : ℕ) (guardOutputs : ℕ → ℕ) (chart : ℕ) (x u : ℕ → ℂ) : Prop :=
  u chart = 1 ∧
    (∀ j < m, (wire (outputs j)).eval₂ (Int.castRingHom ℂ) x = 0 ∧
      (∑ k ∈ Finset.range m, (pderiv (offset + k) (wire (outputs j))).eval₂ (Int.castRingHom ℂ) x * u k) = 0) ∧
    ∀ j < guardCount, (wire (guardOutputs j)).eval₂ (Int.castRingHom ℂ) x = 0

theorem constraints_holds_iff (start m : ℕ) (ops : List Operation) (guardCount : ℕ)
    (guardOutputs : ℕ → ℕ) (chart : ℕ) (env : ℕ → ℂ) :
    (∀ g ∈ constraints start m ops guardCount guardOutputs chart, g.Holds env) ↔
      env (start + chart) = 1 ∧
      (∀ j < m, env (equationWire start m ops j) = 0 ∧ env (kernelWire start m ops j) = 0) ∧
      ∀ j < guardCount, env (valueWire start m ops (guardOutputs j)) = 0 := by
  constructor
  · intro hg
    refine ⟨?_, ?_, ?_⟩
    · have H := hg (.constant (start + chart) 1) (by simp [constraints])
      simpa only [Gate.Holds, Int.cast_one] using H
    · intro j hj
      have hm (g : Gate) (h : g ∈ [.zero (equationWire start m ops j), .zero (kernelWire start m ops j)]) :
          g ∈ constraints start m ops guardCount guardOutputs chart := by
        apply List.mem_append_right
        apply List.mem_append_left
        exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, h⟩
      exact ⟨hg (.zero (equationWire start m ops j)) (hm _ (by simp)),
        hg (.zero (kernelWire start m ops j)) (hm _ (by simp))⟩
    · intro j hj
      apply hg (.zero (valueWire start m ops (guardOutputs j)))
      apply List.mem_append_right
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  · rintro ⟨hn, hrows, hguards⟩ g hg
    rcases List.mem_append.mp hg with h | h
    · obtain rfl := List.mem_singleton.mp h
      simpa only [Gate.Holds, Int.cast_one] using hn
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨j, hj, h⟩ := List.mem_flatMap.mp h
        have H := hrows j (List.mem_range.mp hj)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · exact H.1
        · exact H.2
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
        exact hguards j (List.mem_range.mp hj)

theorem query_sound (wire : ℕ → MvPolynomial ℕ ℤ) (start m offset : ℕ) (ops : List Operation)
    (outputs : ℕ → ℕ) (guardCount : ℕ) (guardOutputs : ℕ → ℕ) (chart : ℕ) (hchart : chart < m)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (ho : ∀ j < m, outputs j < start + ops.length)
    (hguard : ∀ j < guardCount, guardOutputs j < start + ops.length) (env : ℕ → ℂ)
    (hg : ∀ g ∈ query start m offset ops outputs guardCount guardOutputs chart, g.Holds env) :
    At wire m offset outputs guardCount guardOutputs chart env (fun k => env (start + k)) := by
  have hp : ∀ g ∈ StraightLine.gates (zeroWire start m) (program start m offset ops outputs), g.Holds env :=
    fun g h => hg g (List.mem_append_left _ h)
  obtain ⟨hn, hc, ha⟩ := (constraints_holds_iff start m ops guardCount guardOutputs chart env).mp
    (fun g h => hg g (List.mem_append_right _ h))
  refine ⟨hn, fun j hj => ?_, fun j hj => ?_⟩
  · have H := rows_sound wire start m offset ops outputs hw hr hin ho env (fun k => env (start + k)) env
      (fun _ _ => rfl) (fun _ _ => rfl) hp j hj
    exact ⟨H.1.symm.trans (hc j hj).1, H.2.symm.trans (hc j hj).2⟩
  · have H := (jet_sound wire start m offset ops outputs hw hr hin env env (fun _ _ => rfl) hp
      0 (by omega) (guardOutputs j) (hguard j hj)).1
    exact H.symm.trans (ha j hj)

/-- Every bad point and normalized kernel vector has a circuit completion
preserving all source inputs. No root regularity is assumed. -/
theorem query_complete (wire : ℕ → MvPolynomial ℕ ℤ) (start m offset : ℕ) (ops : List Operation)
    (outputs : ℕ → ℕ) (guardCount : ℕ) (guardOutputs : ℕ → ℕ) (chart : ℕ) (hchart : chart < m)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (ho : ∀ j < m, outputs j < start + ops.length)
    (hguard : ∀ j < guardCount, guardOutputs j < start + ops.length) (x u : ℕ → ℂ)
    (hAt : At wire m offset outputs guardCount guardOutputs chart x u) :
    ∃ env : ℕ → ℂ, (∀ i < start, env i = x i) ∧ (∀ k < m, env (start + k) = u k) ∧
      ∀ g ∈ query start m offset ops outputs guardCount guardOutputs chart, g.Holds env := by
  obtain ⟨hn, hrows, hguards⟩ := hAt
  let initial : ℕ → ℂ := fun r => if r < start then x r else u (r - start)
  obtain ⟨env, hp, hg⟩ := StraightLine.exists_completion initial (zeroWire start m)
    (program start m offset ops outputs) (wellFormed start m offset ops outputs hw ho)
  have hx : ∀ i < start, env i = x i := by
    intro i hi
    rw [hp i (by unfold zeroWire; omega)]
    exact ite_eq_left hi
  have hu : ∀ k < m, env (start + k) = u k := by
    intro k hk
    rw [hp _ (by unfold zeroWire; omega)]
    simp only [initial, ite_eq_right (show ¬ start + k < start by omega), Nat.add_sub_cancel_left]
  refine ⟨env, hx, hu, fun g h => ?_⟩
  rcases List.mem_append.mp h with h | h
  · exact hg g h
  · apply (constraints_holds_iff start m ops guardCount guardOutputs chart env).mpr ?_ g h
    refine ⟨(hu chart hchart).trans hn, fun j hj => ?_, fun j hj => ?_⟩
    · have H := rows_sound wire start m offset ops outputs hw hr hin ho x u env hx hu hg j hj
      exact ⟨H.1.trans (hrows j hj).1, H.2.trans (hrows j hj).2⟩
    · have H := (jet_sound wire start m offset ops outputs hw hr hin x env hx hg
        0 (by omega) (guardOutputs j) (hguard j hj)).1
      exact H.trans (hguards j hj)

theorem query_satisfiable (wire : ℕ → MvPolynomial ℕ ℤ) (start m offset : ℕ) (ops : List Operation)
    (outputs : ℕ → ℕ) (guardCount : ℕ) (guardOutputs : ℕ → ℕ) (chart : ℕ) (hchart : chart < m)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (ho : ∀ j < m, outputs j < start + ops.length)
    (hguard : ∀ j < guardCount, guardOutputs j < start + ops.length) :
    Satisfiable (query start m offset ops outputs guardCount guardOutputs chart) ↔
      ∃ x u : ℕ → ℂ, At wire m offset outputs guardCount guardOutputs chart x u := by
  constructor
  · rintro ⟨env, hg⟩
    exact ⟨env, fun k => env (start + k), query_sound wire start m offset ops outputs guardCount guardOutputs
      chart hchart hw hr hin ho hguard env hg⟩
  · rintro ⟨x, u, hAt⟩
    obtain ⟨env, _, _, hg⟩ := query_complete wire start m offset ops outputs guardCount guardOutputs
      chart hchart hw hr hin ho hguard x u hAt
    exact ⟨env, hg⟩

/-- Only a prefix of inputs is constrained real; in particular parent
coordinates can be real while child points and kernel vectors are complex. -/
theorem query_withConstraints (wire : ℕ → MvPolynomial ℕ ℤ) (start m offset : ℕ) (ops : List Operation)
    (outputs : ℕ → ℕ) (guardCount : ℕ) (guardOutputs : ℕ → ℕ) (chart : ℕ) (hchart : chart < m)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (ho : ∀ j < m, outputs j < start + ops.length)
    (hguard : ∀ j < guardCount, guardOutputs j < start + ops.length)
    (realInputs : ℕ) (hreal : realInputs ≤ start) (p : Formula) (hp : p.arity ≤ start) :
    RealQuery.WithConstraints realInputs (query start m offset ops outputs guardCount guardOutputs chart) p ↔
      ∃ x u : ℕ → ℂ, At wire m offset outputs guardCount guardOutputs chart x u ∧
        (∀ i < realInputs, (x i).im = 0) ∧ p.Holds (fun i => (x i).re) := by
  constructor
  · rintro ⟨env, hg, hrPoint, hpred⟩
    exact ⟨env, fun k => env (start + k), query_sound wire start m offset ops outputs guardCount guardOutputs
      chart hchart hw hr hin ho hguard env hg, hrPoint, hpred⟩
  · rintro ⟨x, u, hAt, hrPoint, hpred⟩
    obtain ⟨env, hx, _, hg⟩ := query_complete wire start m offset ops outputs guardCount guardOutputs
      chart hchart hw hr hin ho hguard x u hAt
    refine ⟨env, hg, fun i hi => ?_, ?_⟩
    · rw [hx i (hi.trans_le hreal)]
      exact hrPoint i hi
    · apply (p.holds_congr (fun i => (x i).re) (fun i => (env i).re) ?_).mp hpred
      intro i hi
      rw [hx i (hi.trans_le hp)]

end LeanCanny.ETR.ComplexCircuit.SquareKernel
