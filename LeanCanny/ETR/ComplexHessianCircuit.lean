/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexTermHessian
public import LeanCanny.ETR.ComplexCircuitShift

/-! # Fresh Hessian copies with shared source inputs

Each copy initializes its own sixteen seed wires per source input, then runs
the relocated second-derivative circuit. Only the original coordinates and a
shared zero wire are read outside the copy's fresh consecutive interval.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Hessian
open MvPolynomial
open scoped Classical

def seedOp (zWire j k r : ℕ) : Operation :=
  if r % 4 = 0 then
    if r / 4 % 4 = 0 then .add (r / 16) zWire
    else if r / 4 % 4 = 3 then .constant (if r / 16 = j then 1 else 0)
    else .constant 0
  else if r % 4 = 3 ∧ r / 4 % 4 = 0 then .constant (if r / 16 = k then 1 else 0)
  else .constant 0

theorem input_polynomials (j q : ℕ) :
    Source.hessianInputPolynomials j q =
      if q % 4 = 0 then X (q / 4) else if q % 4 = 3 ∧ q / 4 = j then 1 else 0 := by
  unfold Source.hessianInputPolynomials Differential.polynomialInputs
  by_cases h0 : q % 4 = 0
  · simp only [h0, ite_true]
  · by_cases h3 : q % 4 = 3
    · by_cases hj : q / 4 = j
      · simp [h3, hj]
      · simp [h3, hj, pderiv_X_of_ne hj]
    · simp [h0, h3]

theorem input_polynomials_derivative (j k q : ℕ) :
    pderiv k (Source.hessianInputPolynomials j q) =
      if q % 4 = 0 ∧ q / 4 = k then 1 else 0 := by
  rw [input_polynomials]
  by_cases h0 : q % 4 = 0
  · by_cases hk : q / 4 = k
    · simp [h0, hk]
    · simp [h0, hk, pderiv_X_of_ne hk]
  · by_cases hj : q % 4 = 3 ∧ q / 4 = j <;> simp [h0, hj]

theorem seedOp_eval (zWire j k r : ℕ) (env : ℕ → ℂ) (hz : env zWire = 0) :
    (seedOp zWire j k r).eval env = Source.hessianInputs j k env r := by
  have hd : r / 4 / 4 = r / 16 := by omega
  unfold Source.hessianInputs
  rw [Differential.polynomialInputs, input_polynomials_derivative, input_polynomials, hd]
  by_cases h0 : r % 4 = 0
  · by_cases h00 : r / 4 % 4 = 0
    · simp [seedOp, h0, h00, Operation.eval, hz]
    · by_cases h03 : r / 4 % 4 = 3 <;> by_cases hj : r / 16 = j <;>
        simp [seedOp, h0, h00, h03, hj, Operation.eval]
  · by_cases h3 : r % 4 = 3 <;> by_cases h00 : r / 4 % 4 = 0 <;> by_cases hk : r / 16 = k <;>
      simp [seedOp, h0, h3, h00, hk, Operation.eval]

theorem inputs_congr (j k r : ℕ) (x y : ℕ → ℂ) (h : x (r / 16) = y (r / 16)) :
    Source.hessianInputs j k x r = Source.hessianInputs j k y r := by
  have hd : r / 4 / 4 = r / 16 := by omega
  unfold Source.hessianInputs
  rw [Differential.polynomialInputs, input_polynomials_derivative, input_polynomials, hd]
  split_ifs <;> simp_all

def seeds (zWire start j k : ℕ) : List Operation :=
  (List.range (16 * start)).map (seedOp zWire j k)

theorem seeds_length (zWire start j k : ℕ) : (seeds zWire start j k).length = 16 * start := by
  simp only [seeds, List.length_map, List.length_range]

theorem seedOp_inputsBelow (zWire base start j k r : ℕ)
    (hz : zWire < base) (hs : start ≤ base) (hr : r < 16 * start) :
    (seedOp zWire j k r).InputsBelow (base + r) := by
  have hi : r / 16 < start := by omega
  unfold seedOp
  split_ifs <;> simp only [Operation.InputsBelow]; omega

theorem seeds_wellFormed (zWire base start j k : ℕ) (hz : zWire < base) (hs : start ≤ base) :
    StraightLine.WellFormed base (seeds zWire start j k) := by
  have hgen (count : ℕ) (hc : count ≤ 16 * start) :
      StraightLine.WellFormed base ((List.range count).map (seedOp zWire j k)) := by
    induction count with
    | zero => trivial
    | succ count ih =>
      rw [List.range_succ, List.map_append, StraightLine.wellFormed_append]
      refine ⟨ih (by omega), ?_⟩
      simp only [List.length_map, List.length_range, List.map_cons, List.map_nil,
        StraightLine.WellFormed]
      exact ⟨seedOp_inputsBelow zWire base start j k count hz hs (by omega), trivial⟩
  exact hgen _ le_rfl

theorem seeds_gates (zWire base start j k : ℕ) :
    StraightLine.gates base (seeds zWire start j k) =
      (List.range (16 * start)).map (fun r => (seedOp zWire j k r).gate (base + r)) := by
  have hgen (count : ℕ) : StraightLine.gates base ((List.range count).map (seedOp zWire j k)) =
      (List.range count).map (fun r => (seedOp zWire j k r).gate (base + r)) := by
    induction count with
    | zero => rfl
    | succ count ih =>
      rw [List.range_succ, List.map_append, StraightLine.gates_append, ih]
      simp only [List.length_map, List.length_range, List.map_cons, List.map_nil,
        StraightLine.gates, List.map_append]
  exact hgen _

theorem seeds_sound (zWire base start j k : ℕ) (x env : ℕ → ℂ) (hz : env zWire = 0)
    (hx : ∀ i < start, env i = x i)
    (hg : ∀ g ∈ StraightLine.gates base (seeds zWire start j k), g.Holds env)
    (r : ℕ) (hr : r < 16 * start) : env (base + r) = Source.hessianInputs j k x r := by
  have hm : (seedOp zWire j k r).gate (base + r) ∈ StraightLine.gates base (seeds zWire start j k) := by
    rw [seeds_gates]
    exact List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩
  have hi : r / 16 < start := by omega
  exact ((Operation.gate_holds_iff _ _ _).mp (hg _ hm)).trans
    ((seedOp_eval zWire j k r env hz).trans (inputs_congr j k r env x (hx _ hi)))

def program (zWire base start j k : ℕ) (ops : List Operation) : List Operation :=
  seeds zWire start j k ++ (Differential.secondProgram start ops).map (Operation.shift base)

theorem program_length (zWire base start j k : ℕ) (ops : List Operation) :
    (program zWire base start j k ops).length = 16 * (start + ops.length) := by
  simp only [program, List.length_append, seeds_length, List.length_map, Differential.secondProgram_length]
  omega

theorem wellFormed (zWire base start j k : ℕ) (ops : List Operation)
    (hz : zWire < base) (hs : start ≤ base) (hw : StraightLine.WellFormed start ops) :
    StraightLine.WellFormed base (program zWire base start j k ops) := by
  rw [program, StraightLine.wellFormed_append, seeds_length]
  refine ⟨seeds_wellFormed zWire base start j k hz hs, ?_⟩
  simpa only [Differential.valueWire, ← Nat.mul_assoc] using
    StraightLine.shift_wellFormed base _ _ (Differential.second_wellFormed start ops hw)

theorem gates_eq (zWire base start j k : ℕ) (ops : List Operation) :
    StraightLine.gates base (program zWire base start j k ops) =
      StraightLine.gates base (seeds zWire start j k) ++
        (StraightLine.gates (Differential.valueWire (Differential.valueWire start))
          (Differential.secondProgram start ops)).map (Gate.shift base) := by
  rw [program, StraightLine.gates_append, seeds_length]
  simpa only [Differential.valueWire, ← Nat.mul_assoc] using congrArg
    (StraightLine.gates base (seeds zWire start j k) ++ ·)
    (StraightLine.shift_gates base (Differential.valueWire (Differential.valueWire start))
      (Differential.secondProgram start ops))

theorem sound (wire : ℕ → MvPolynomial ℕ ℤ) (zWire base start j k : ℕ) (ops : List Operation)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (x env : ℕ → ℂ) (hz : env zWire = 0)
    (hx : ∀ i < start, env i = x i)
    (hg : ∀ g ∈ StraightLine.gates base (program zWire base start j k ops), g.Holds env) :
    ∀ i < start + ops.length, Differential.SecondAgrees wire j k x (fun r => env (base + r)) i := by
  have hs : ∀ g ∈ StraightLine.gates base (seeds zWire start j k), g.Holds env := by
    intro g h
    exact hg g (by rw [gates_eq]; exact List.mem_append_left _ h)
  have hb : ∀ g ∈ StraightLine.gates (Differential.valueWire (Differential.valueWire start))
      (Differential.secondProgram start ops), g.Holds (fun r => env (base + r)) := by
    intro g h
    apply (Gate.shift_holds base g env).mp
    exact hg _ (by rw [gates_eq]; exact List.mem_append_right _ (List.mem_map.mpr ⟨g, h, rfl⟩))
  have hi : ∀ q < Differential.valueWire start, Differential.Agrees (Differential.polynomialInputs wire j)
      k x (fun r => env (base + r)) q := by
    intro q hq
    have hinput : Differential.polynomialInputs wire j q = Source.hessianInputPolynomials j q := by
      have hdiv : q / 4 < start := by unfold Differential.valueWire at hq; omega
      simp only [Differential.polynomialInputs, hin _ hdiv, Source.hessianInputPolynomials]
    have hv : Differential.valueWire q < 16 * start := by unfold Differential.valueWire at *; omega
    have hd : Differential.derivativeWire q < 16 * start := by
      unfold Differential.valueWire Differential.derivativeWire at *; omega
    simp only [Differential.Agrees, hinput]
    exact ⟨(seeds_sound zWire base start j k x env hz hx hs _ hv).trans (Source.hessianInputs_agrees j k x q).1,
      (seeds_sound zWire base start j k x env hz hx hs _ hd).trans (Source.hessianInputs_agrees j k x q).2⟩
  exact Differential.second_sound wire j k x start ops hw hr (fun r => env (base + r)) hi hb

theorem exists_completion (wire : ℕ → MvPolynomial ℕ ℤ) (zWire base start j k : ℕ) (ops : List Operation)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (hz : zWire < base) (hs : start ≤ base)
    (x : ℕ → ℂ) (hx : x zWire = 0) :
    ∃ env : ℕ → ℂ, (∀ i < base, env i = x i) ∧
      (∀ g ∈ StraightLine.gates base (program zWire base start j k ops), g.Holds env) ∧
      ∀ i < start + ops.length, Differential.SecondAgrees wire j k x (fun r => env (base + r)) i := by
  obtain ⟨env, hp, hg⟩ := StraightLine.exists_completion x base
    (program zWire base start j k ops) (wellFormed zWire base start j k ops hz hs hw)
  exact ⟨env, hp, hg, sound wire zWire base start j k ops hw hr hin x env ((hp _ hz).trans hx)
    (fun i hi => hp i (hi.trans_le hs)) hg⟩

theorem source_sound (zWire base start j k : ℕ) (t : Term) (ht : t.arity ≤ start)
    (x env : ℕ → ℂ) (hz : env zWire = 0) (hx : ∀ i < start, env i = x i)
    (hg : ∀ g ∈ StraightLine.gates base (program zWire base start j k (Source.program start t)), g.Holds env) :
    Differential.SecondAgrees (fun _ => t.toPolynomial) j k x
      (fun i => env (base + i)) (Source.output start t) := by
  have hs : ∀ g ∈ StraightLine.gates base (seeds zWire start j k), g.Holds env := by
    intro g h
    exact hg g (by rw [gates_eq]; exact List.mem_append_left _ h)
  have hb : ∀ g ∈ StraightLine.gates (Differential.valueWire (Differential.valueWire start))
      (Differential.secondProgram start (Source.program start t)), g.Holds (fun i => env (base + i)) := by
    intro g h
    apply (Gate.shift_holds base g env).mp
    exact hg _ (by rw [gates_eq]; exact List.mem_append_right _ (List.mem_map.mpr ⟨g, h, rfl⟩))
  have hi : ∀ q < Differential.valueWire start, Differential.Agrees (Source.hessianInputPolynomials j)
      k x (fun i => env (base + i)) q := by
    intro q hq
    have hv : Differential.valueWire q < 16 * start := by unfold Differential.valueWire at *; omega
    have hd : Differential.derivativeWire q < 16 * start := by
      unfold Differential.valueWire Differential.derivativeWire at *; omega
    exact ⟨(seeds_sound zWire base start j k x env hz hx hs _ hv).trans (Source.hessianInputs_agrees j k x q).1,
      (seeds_sound zWire base start j k x env hz hx hs _ hd).trans (Source.hessianInputs_agrees j k x q).2⟩
  simpa only [Differential.SecondAgrees, Term.eval₂_toPolynomial] using
    Source.hessian_sound start t ht j k x (fun i => env (base + i)) hi hb

theorem source_exists_completion (zWire base start j k : ℕ) (t : Term) (ht : t.arity ≤ start)
    (hz : zWire < base) (hs : start ≤ base) (x : ℕ → ℂ) (hx : x zWire = 0) :
    ∃ env : ℕ → ℂ, (∀ i < base, env i = x i) ∧
      (∀ g ∈ StraightLine.gates base (program zWire base start j k (Source.program start t)), g.Holds env) ∧
      Differential.SecondAgrees (fun _ => t.toPolynomial) j k x
        (fun i => env (base + i)) (Source.output start t) := by
  obtain ⟨env, hp, hg⟩ := StraightLine.exists_completion x base
    (program zWire base start j k (Source.program start t))
    (wellFormed zWire base start j k _ hz hs (Source.wellFormed start t ht))
  exact ⟨env, hp, hg, source_sound zWire base start j k t ht x env ((hp _ hz).trans hx)
    (fun i hi => hp i (hi.trans_le hs)) hg⟩

end LeanCanny.ETR.ComplexCircuit.Hessian
