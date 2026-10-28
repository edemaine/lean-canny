/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCriticalSampleCircuit

/-! # Critical kernels at real inputs with independent formula witnesses

The source inputs are linked to real logical coordinates. Kernel coordinates
and circuit auxiliaries remain separate. An arbitrary real formula can
therefore constrain the original point or introduce additional witnesses,
without accidentally constraining arithmetic wires of the kernel program.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.CriticalKernel
open LeanCanny.Computation LeanCanny.Encoding.Brackets MvPolynomial RealQuery.Interleaved
open scoped Classical

def At (p : MvPolynomial ℕ ℤ) (m : ℕ) (v : ℕ → ℤ) (chart : ℕ) (x : ℕ → ℂ) : Prop :=
  ∃ u : ℕ → ℂ, u chart = 1 ∧ ∀ j < m, criticalValue p v x j = 0 ∧ kernelValue p m v x u j = 0

theorem port_realizes (wire : ℕ → MvPolynomial ℕ ℤ) (start m : ℕ) (ops : List Operation)
    (out : ℕ) (v : ℕ → ℤ) (chart : ℕ) (hchart : chart < m)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (ho : out < start + ops.length) (x : ℕ → ℝ) :
    PortRealizes start start id (query start m ops out v chart) x ↔
      At (wire out) m v chart (fun i => (x i : ℂ)) := by
  constructor
  · rintro ⟨env, hg, _, hinput⟩
    have hp : ∀ g ∈ StraightLine.gates (zeroWire start m) (program start m ops out v), g.Holds env :=
      fun g h => hg g (List.mem_append_left _ h)
    have hc : ∀ g ∈ constraints start m ops chart, g.Holds env :=
      fun g h => hg g (List.mem_append_right _ h)
    obtain ⟨hn, hc⟩ := (constraints_holds_iff start m ops chart env).mp hc
    have hs := rows_sound wire start m ops out v hw hr hin ho (fun i => (x i : ℂ))
      (fun k => env (start + k)) env hinput (fun _ _ => rfl) hp
    exact ⟨_, hn, fun j hj => ⟨(hs j hj).1.symm.trans (hc j hj).2, (hs j hj).2.symm.trans (hc j hj).1⟩⟩
  · rintro ⟨u, hn, hroot⟩
    let initial : ℕ → ℂ := fun i => if i < start then (x i : ℂ) else u (i - start)
    obtain ⟨env, hp, hg⟩ := StraightLine.exists_completion initial (zeroWire start m)
      (program start m ops out v) (wellFormed start m ops out v hw ho)
    have hx : ∀ i < start, env i = (x i : ℂ) := by
      intro i hi
      rw [hp i (by unfold zeroWire; omega)]
      exact ite_eq_left hi
    have hu : ∀ k < m, env (start + k) = u k := by
      intro k hk
      rw [hp _ (by unfold zeroWire; omega)]
      simp only [initial, ite_eq_right (show ¬ start + k < start by omega), Nat.add_sub_cancel_left]
    have hs := rows_sound wire start m ops out v hw hr hin ho (fun i => (x i : ℂ)) u env hx hu hg
    refine ⟨env, ?_, ?_, hx⟩
    · intro g h
      rcases List.mem_append.mp h with h | h
      · exact hg g h
      · apply ((constraints_holds_iff start m ops chart env).mpr
          ⟨(hu chart hchart).trans hn, fun j hj =>
            ⟨(hs j hj).2.trans (hroot j hj).2, (hs j hj).1.trans (hroot j hj).1⟩⟩) g h
    · intro i hi
      rw [hx i hi]
      exact Complex.ofReal_im _

theorem input_correct (wire : ℕ → MvPolynomial ℕ ℤ) (start m : ℕ) (ops : List Operation)
    (out : ℕ) (v : ℕ → ℤ) (chart : ℕ) (hchart : chart < m)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (ho : out < start + ops.length) (p : Formula) :
    InputSatisfiable start start (query start m ops out v chart) p ↔
      ∃ x : ℕ → ℝ, At (wire out) m v chart (fun i => (x i : ℂ)) ∧ p.Holds x := by
  rw [InputSatisfiable, portSatisfiable_iff]
  apply exists_congr
  intro x
  exact and_congr (port_realizes wire start m ops out v chart hchart hw hr hin ho x) Iff.rfl

def fresh (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ) (chart : ℕ) : ℕ :=
  zeroWire start m + (program start m ops out v).length + chart + 1

theorem query_arity (start m : ℕ) (ops : List Operation) (out : ℕ) (v : ℕ → ℤ) (chart : ℕ)
    (hw : StraightLine.WellFormed start ops) (ho : out < start + ops.length) :
    ∀ g ∈ query start m ops out v chart, g.arity ≤ fresh start m ops out v chart := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact (StraightLine.gates_arity _ _ (wellFormed start m ops out v hw ho) g hg).trans (by unfold fresh; omega)
  · simp only [constraints, List.mem_append, List.mem_singleton] at hg
    rcases hg with rfl | hg
    · simp only [Gate.arity, fresh, zeroWire]
      omega
    · obtain ⟨j, hj, hg⟩ := List.mem_flatMap.mp hg
      have hj' := List.mem_range.mp hj
      have hc := CriticalSamples.output_lt start m ops out v j hj'
      change KernelRow.criticalWire (rowStart start m ops j) m < _ at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · have hm : m ≠ 0 := by omega
        simp only [Gate.arity, KernelRow.sumWire, hm, ite_false]
        unfold KernelRow.criticalWire at hc
        unfold fresh
        omega
      · simp only [Gate.arity]
        unfold fresh
        omega

theorem fresh_unary {start m out chart : List Bool → ℕ} {ops : List Bool → List Operation}
    {v : List Bool → ℕ → ℤ} (hs : UnaryFn start) (hm : UnaryFn m) (hi : UnaryFn chart)
    (hlen : UnaryFn (fun c => (ops c).length)) :
    UnaryFn (fun c => fresh (start c) (m c) (ops c) (out c) (v c) (chart c)) :=
  (((hs.add hm).add (CriticalSamples.length_unary hs hm hlen)).add hi).add (UnaryFn.const 1)

theorem constrained_evaluator {start m out chart : List Bool → ℕ} {ops : List Bool → List Operation}
    {v : List Bool → ℕ → ℤ} {p : List Bool → Formula}
    (hs : UnaryFn start) (hm : UnaryFn m) (ho : UnaryFn out) (hi : UnaryFn chart)
    (hlen : UnaryFn (fun c => (ops c).length))
    (hg : (fun c => encode (StraightLine.gates (start c) (ops c))) ∈ FP)
    (hv : (fun q => (Term.const (-v (pairFst q) (pairSnd q).length)).toData.toBits) ∈ FP)
    (hp : (fun c => (p c).encode) ∈ FP)
    (hw : ∀ c, StraightLine.WellFormed (start c) (ops c))
    (hOut : ∀ c, out c < start c + (ops c).length) :
    SpaceFunction (fun c => [decide (InputSatisfiable (start c) (start c)
      (query (start c) (m c) (ops c) (out c) (v c) (chart c)) (p c))]) :=
  RealQuery.Interleaved.evaluator hs hs (fresh_unary hs hm hi hlen)
    (query_encode_mem_FP hs hm ho hi hlen hg hv) hp (fun _ => le_rfl)
    (fun c => by unfold fresh zeroWire; omega) (fun c => query_arity _ _ _ _ _ _ (hw c) (hOut c))

end LeanCanny.ETR.ComplexCircuit.CriticalKernel
