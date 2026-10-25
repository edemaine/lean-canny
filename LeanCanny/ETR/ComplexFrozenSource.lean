/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCircuitReindex
public import LeanCanny.ETR.ComplexTermDifferential

/-! # Freezing the swept coordinate in the actual source circuit

Variable zero is replaced by a computed integer sample. Positive variables
become spatial coordinates one index earlier. Auxiliary wires occupy a fresh
consecutive interval, so the source compiler's original shared circuit is kept.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit
open MvPolynomial
open scoped Classical

theorem Differential.polynomial_reindex {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ)
    (f : ℕ → ℕ) (op : Operation) :
    polynomial wire (op.reindex f) = polynomial (fun i => wire (f i)) op := by cases op <;> rfl

theorem Differential.reindex_realizes {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ)
    (f : ℕ → ℕ) (start next : ℕ) (ops : List Operation) (hf : ∀ q, f (start + q) = next + q) :
    Realizes wire next (ops.map (Operation.reindex f)) ↔ Realizes (fun i => wire (f i)) start ops := by
  induction ops generalizing start next with
  | nil => rfl
  | cons op ops ih =>
    have h0 : f start = next := by simpa only [Nat.add_zero] using hf 0
    have ht (q : ℕ) : f (start + 1 + q) = next + 1 + q := by
      simpa only [Nat.add_assoc] using hf (1 + q)
    simp only [List.map_cons, Realizes, polynomial_reindex]
    rw [ih (start + 1) (next + 1) ht, h0]

namespace FrozenSource

def index (oldStart start i : ℕ) : ℕ :=
  if i < oldStart then (if i = 0 then start else i - 1) else start + 1 + (i - oldStart)

theorem index_aux (oldStart start q : ℕ) : index oldStart start (oldStart + q) = start + 1 + q := by
  simp only [index, ite_eq_right (show ¬ oldStart + q < oldStart by omega), Nat.add_sub_cancel_left]

theorem index_input_lt (oldStart start q i : ℕ) (hs : oldStart ≤ start) (hi : i < oldStart + q) :
    index oldStart start i < start + 1 + q := by
  unfold index
  split_ifs <;> omega

def program (oldStart start : ℕ) (sample : ℤ) (t : Term) : List Operation :=
  .constant sample :: (Source.program oldStart t).map (Operation.reindex (index oldStart start))
def output (oldStart start : ℕ) (t : Term) : ℕ := index oldStart start (Source.output oldStart t)

noncomputable def inputs (sample : ℤ) (x : ℕ → ℂ) (i : ℕ) : ℂ :=
  if i = 0 then sample else x (i - 1)
noncomputable def inputPolynomial (sample : ℤ) (i : ℕ) : MvPolynomial ℕ ℤ :=
  if i = 0 then C sample else X (i - 1)
noncomputable def polynomial (sample : ℤ) (t : Term) : MvPolynomial ℕ ℤ := t.eval (inputPolynomial sample)

theorem polynomial_eval (sample : ℤ) (t : Term) (x : ℕ → ℂ) :
    (polynomial sample t).eval₂ (Int.castRingHom ℂ) x = t.eval (inputs sample x) := by
  have hc (z : ℤ) : (z : MvPolynomial ℕ ℤ).eval₂ (Int.castRingHom ℂ) x = (z : ℂ) :=
    map_intCast (eval₂Hom (Int.castRingHom ℂ) x) z
  induction t with
  | const z => exact hc z
  | var i => by_cases hi : i = 0 <;> simp [polynomial, Term.eval, inputPolynomial, inputs, hi, hc]
  | add a b ha hb =>
    change (polynomial sample a + polynomial sample b).eval₂ (Int.castRingHom ℂ) x = _
    rw [eval₂_add, ha, hb]
    rfl
  | mul a b ha hb =>
    change (polynomial sample a * polynomial sample b).eval₂ (Int.castRingHom ℂ) x = _
    rw [eval₂_mul, ha, hb]
    rfl

theorem program_length (oldStart start : ℕ) (sample : ℤ) (t : Term) :
    (program oldStart start sample t).length = Source.count t + 1 := by
  simp only [program, List.length_cons, List.length_map, Source.program_length]

theorem wellFormed (oldStart start : ℕ) (sample : ℤ) (t : Term)
    (ht : t.arity ≤ oldStart) (hs : oldStart ≤ start) :
    StraightLine.WellFormed start (program oldStart start sample t) :=
  ⟨trivial, StraightLine.reindex_wellFormed (index oldStart start) oldStart (start + 1) _
    (Source.wellFormed oldStart t ht) (fun q i hi => index_input_lt oldStart start q i hs hi)⟩

theorem output_lt (oldStart start : ℕ) (sample : ℤ) (t : Term)
    (ht : t.arity ≤ oldStart) (hs : oldStart ≤ start) :
    output oldStart start t < start + (program oldStart start sample t).length := by
  have ho := Source.output_lt oldStart t ht
  have hi := index_input_lt oldStart start (Source.count t) (Source.output oldStart t) hs ho
  rw [program_length]
  unfold output
  omega

theorem gates_eq (oldStart start : ℕ) (sample : ℤ) (t : Term) :
    StraightLine.gates start (program oldStart start sample t) =
      .constant start sample :: (Source.gates oldStart t).map (Gate.reindex (index oldStart start)) := by
  simp only [program, StraightLine.gates, Operation.gate]
  rw [StraightLine.reindex_gates _ oldStart (start + 1) _ (index_aux oldStart start), Source.gates_eq]

theorem sound (oldStart start : ℕ) (sample : ℤ) (t : Term) (ht : t.arity ≤ oldStart) (env : ℕ → ℂ)
    (hg : ∀ g ∈ StraightLine.gates start (program oldStart start sample t), g.Holds env) :
    env (output oldStart start t) = t.eval (inputs sample env) := by
  rw [gates_eq] at hg
  have hz : env start = (sample : ℂ) := hg (.constant start sample) (List.mem_cons_self ..)
  have hb : ∀ g ∈ Source.gates oldStart t, g.Holds (fun i => env (index oldStart start i)) := by
    intro g h
    apply (Gate.reindex_holds _ g env).mp
    exact hg _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨g, h, rfl⟩))
  refine (Source.sound oldStart t _ hb).trans (t.eval_congr _ _ ?_)
  intro i hi
  have hlt : i < oldStart := hi.trans_le ht
  unfold index inputs
  rw [ite_eq_left hlt]
  split_ifs
  · exact hz
  · rfl

theorem exists_completion (oldStart start : ℕ) (sample : ℤ) (t : Term)
    (ht : t.arity ≤ oldStart) (hs : oldStart ≤ start) (x : ℕ → ℂ) :
    ∃ env : ℕ → ℂ, (∀ i < start, env i = x i) ∧
      (∀ g ∈ StraightLine.gates start (program oldStart start sample t), g.Holds env) ∧
      env (output oldStart start t) = t.eval (inputs sample x) := by
  obtain ⟨env, hp, hg⟩ := StraightLine.exists_completion x start (program oldStart start sample t)
    (wellFormed oldStart start sample t ht hs)
  refine ⟨env, hp, hg, (sound oldStart start sample t ht env hg).trans (t.eval_congr _ _ ?_)⟩
  intro i hi
  unfold inputs
  split_ifs with h0
  · rfl
  · have hlt : i - 1 < start := by have := hi.trans_le ht; omega
    exact hp _ hlt

theorem realized_output (wire : ℕ → MvPolynomial ℕ ℤ) (oldStart start : ℕ) (sample : ℤ) (t : Term)
    (ht : t.arity ≤ oldStart) (hs : oldStart ≤ start) (hin : ∀ i < start, wire i = X i)
    (hr : Differential.Realizes wire start (program oldStart start sample t)) :
    wire (output oldStart start t) = polynomial sample t := by
  have hz : wire start = C sample := hr.1
  have hb := (Differential.reindex_realizes wire (index oldStart start) oldStart (start + 1)
    (Source.program oldStart t) (index_aux oldStart start)).mp hr.2
  refine (Source.symbolic_sound (fun i => wire (index oldStart start i)) oldStart t hb).trans
    (t.eval_congr _ _ ?_)
  intro i hi
  have hlt : i < oldStart := hi.trans_le ht
  unfold index inputPolynomial
  rw [ite_eq_left hlt]
  split_ifs with h0
  · exact hz
  · exact hin (i - 1) (by omega)

theorem symbolic_output (oldStart start : ℕ) (sample : ℤ) (t : Term)
    (ht : t.arity ≤ oldStart) (hs : oldStart ≤ start) :
    Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start (program oldStart start sample t)
      (output oldStart start t) = polynomial sample t :=
  realized_output _ oldStart start sample t ht hs
    (fun i hi => Differential.symbolicRun_preserves_before _ _ _ i hi)
    (Differential.symbolicRun_realizes _ _ _ (wellFormed oldStart start sample t ht hs))

end FrozenSource
end LeanCanny.ETR.ComplexCircuit
