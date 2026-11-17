/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ExistsForallUpperBound
public import LeanCanny.CountingHierarchy.ExistentialUpperBound
public import LeanCanny.ETR.ComplexStraightLine
public import LeanCanny.ETR.SumSquaresFP

/-! # Shared real arithmetic circuits and universally quantified gate equations

A circuit writes consecutive fresh wires and reads earlier wires. Its equations
retain shared wires rather than expanding the computed polynomial. Universally
quantifying the wire values under these equations preserves the two real blocks.
-/

@[expose] public section

namespace LeanCanny.CountingHierarchy.RealCircuit

open LeanCanny LeanCanny.ETR
open LeanCanny.ETR.ComplexCircuit (Operation)
open scoped Classical

noncomputable def value (op : Operation) (env : ℕ → ℝ) : ℝ :=
  match op with
  | .constant z => z
  | .add i j => env i + env j
  | .mul i j => env i * env j

def rhs : Operation → Term
  | .constant z => .const z
  | .add i j => .add (.var i) (.var j)
  | .mul i j => .mul (.var i) (.var j)

def equation (out : ℕ) (op : Operation) : Term :=
  .add (.var out) (.mul (.const (-1)) (rhs op))

theorem eval_equation (out : ℕ) (op : Operation) (env : ℕ → ℝ) :
    (equation out op).eval env = 0 ↔ env out = value op env := by
  have ht : (rhs op).eval env = value op env := by cases op <;> rfl
  simp only [equation, Term.eval, ht, Int.cast_neg, Int.cast_one, neg_one_mul,
    ← sub_eq_add_neg, sub_eq_zero]

def equations : ℕ → List Operation → List Term
  | _, [] => []
  | start, op :: ops => equation start op :: equations (start + 1) ops

abbrev WellFormed := ComplexCircuit.StraightLine.WellFormed

noncomputable def run (env : ℕ → ℝ) : ℕ → List Operation → ℕ → ℝ
  | _, [] => env
  | start, op :: ops => run (Function.update env start (value op env)) (start + 1) ops

theorem value_congr (op : Operation) (out : ℕ) (env env' : ℕ → ℝ)
    (hop : op.InputsBelow out) (h : ∀ i < out, env i = env' i) : value op env = value op env' := by
  cases op with
  | constant z => rfl
  | add i j => simp only [value, h i hop.1, h j hop.2]
  | mul i j => simp only [value, h i hop.1, h j hop.2]

theorem run_preserves (env : ℕ → ℝ) (start : ℕ) (ops : List Operation)
    (i : ℕ) (hi : i < start) : run env start ops i = env i := by
  induction ops generalizing env start with
  | nil => rfl
  | cons op ops ih =>
    rw [run, ih _ _ (by omega)]
    exact Function.update_of_ne (show i ≠ start by omega) _ _

theorem run_satisfies (env : ℕ → ℝ) (start : ℕ) (ops : List Operation)
    (hw : WellFormed start ops) : ∀ t ∈ equations start ops, t.eval (run env start ops) = 0 := by
  induction ops generalizing env start with
  | nil => simp [equations]
  | cons op ops ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · apply (eval_equation start op _).mpr
      have ho : run env start (op :: ops) start = value op env := by
        rw [run, run_preserves _ (start + 1) ops start (by omega), Function.update_self]
      exact ho.trans (value_congr op start _ env hw.1
        (fun i hi => run_preserves env start (op :: ops) i hi)).symm
    · exact ih _ _ hw.2 t ht

/-- A satisfying wire assignment agrees with the actual straight-line run on
all input and output wires. Values beyond the circuit remain irrelevant. -/
theorem run_unique (env out : ℕ → ℝ) (start : ℕ) (ops : List Operation)
    (hw : WellFormed start ops) (hp : ∀ i < start, out i = env i)
    (he : ∀ t ∈ equations start ops, t.eval out = 0) :
    ∀ i < start + ops.length, out i = run env start ops i := by
  induction ops generalizing env start with
  | nil => simpa only [List.length_nil, Nat.add_zero, run] using hp
  | cons op ops ih =>
    have ho := (eval_equation start op out).mp (he _ (List.mem_cons_self ..))
    have hp' : ∀ i < start + 1, out i = Function.update env start (value op env) i := by
      intro i hi
      by_cases hi' : i = start
      · subst i
        rw [Function.update_self, ho, value_congr op start out env hw.1 hp]
      · rw [Function.update_of_ne hi']
        exact hp i (by omega)
    have ht := ih (Function.update env start (value op env)) (start + 1) hw.2 hp'
      (fun t ht => he t (List.mem_cons_of_mem _ ht))
    intro i hi
    exact ht i (by simp only [List.length_cons] at hi; omega)

/-- Boolean tests may refer directly to circuit output wires. -/
def guardedMatrix (start : ℕ) (ops : List Operation) (p : Formula) : Formula :=
  .or (.not (.eqZero (SumSquares.accumulate (equations start ops) (.const 0)))) p

theorem guardedMatrix_holds (start : ℕ) (ops : List Operation) (p : Formula) (env : ℕ → ℝ) :
    (guardedMatrix start ops p).Holds env ↔
      (∀ t ∈ equations start ops, t.eval env = 0) → p.Holds env := by
  simp only [guardedMatrix, Formula.Holds, SumSquares.accumulate_zero_iff]
  tauto

/-- Circuit semantics: the inputs follow the two-block quantifier order, and
the deterministic run computes all shared intermediate wires. -/
def SentenceHolds (r start : ℕ) (ops : List Operation) (p : Formula) : Prop :=
  ∃ x : Fin r → ℝ, ∀ env : ℕ → ℝ, (∀ i : Fin r, env i.val = x i) →
    p.Holds (run env start ops)

theorem sentence_iff (r start : ℕ) (ops : List Operation) (p : Formula)
    (hr : r ≤ start) (hw : WellFormed start ops) (hp : p.arity ≤ start + ops.length) :
    SentenceHolds r start ops p ↔ ExistsForall.SentenceHolds r (guardedMatrix start ops p) := by
  apply exists_congr
  intro x
  constructor
  · intro h env henv
    rw [guardedMatrix_holds]
    intro he
    exact (p.holds_congr env (run env start ops)
      (fun i hi => run_unique env env start ops hw (fun _ _ => rfl) he i (hi.trans_le hp))).mpr
        (h env henv)
  · intro h env henv
    have hprefix : ∀ i : Fin r, run env start ops i.val = x i := fun i =>
      (run_preserves env start ops i.val (i.isLt.trans_le hr)).trans (henv i)
    exact (guardedMatrix_holds start ops p _).mp (h _ hprefix) (run_satisfies env start ops hw)

/-- The existing total encoded CH decider accepts exactly the shared-circuit
sentence, without unfolding its arithmetic DAG into expression trees. -/
theorem encode_mem_language (r start : ℕ) (ops : List Operation) (p : Formula)
    (hr : r ≤ start) (hw : WellFormed start ops) (hp : p.arity ≤ start + ops.length) :
    ExistsForall.encSentence (r, (guardedMatrix start ops p).encode) ∈ ExistsForall.language ↔
      SentenceHolds r start ops p := by
  rw [ExistsForall.encode_mem_language, ← sentence_iff r start ops p hr hw hp]

/-- Native front ends may supply the shallow gate equations and Boolean output
tests. This writer retains every shared wire and preserves the fixed C₆₀ bound. -/
def guardedBits (equationsBits matrixBits : List Bool) : List Bool :=
  Codec.taggedTwo 5 (Codec.taggedOne 3 (Codec.taggedOne 1 (SumSquares.collapse equationsBits))) matrixBits

theorem guardedBits_mem_FP {e p : List Bool → List Bool} (he : e ∈ FP) (hp : p ∈ FP) :
    (fun w => guardedBits (e w) (p w)) ∈ FP :=
  Codec.taggedTwo_mem_FP 5
    (Codec.taggedOne_mem_FP 3 (Codec.taggedOne_mem_FP 1 (mem_FP_comp (f := e) (g := SumSquares.collapse) he SumSquares.collapse_mem_FP))) hp

theorem guardedBits_encode (start : ℕ) (ops : List Operation) (p : Formula) :
    guardedBits (SumSquares.listBits (equations start ops)) p.encode =
      (guardedMatrix start ops p).encode := by
  simp only [guardedBits, SumSquares.collapse_listBits, guardedMatrix, Formula.encode,
    Formula.toData, Codec.taggedTwo_toBits, Codec.taggedOne_toBits]

/-- A native family of shared circuits inherits the fixed decision level.
The only computational inputs are the unary outer-block reader and the writers
for the explicit shallow equations and Boolean output matrix. -/
theorem generated_mem_CountingLevel
    (r start : List Bool → ℕ) (ops : List Bool → List Operation) (p : List Bool → Formula)
    (hrTime : UnaryFn r)
    (heTime : (fun w => SumSquares.listBits (equations (start w) (ops w))) ∈ FP)
    (hpTime : (fun w => (p w).encode) ∈ FP)
    (hr : ∀ w, r w ≤ start w) (hw : ∀ w, WellFormed (start w) (ops w))
    (hp : ∀ w, (p w).arity ≤ start w + (ops w).length) :
    {w | SentenceHolds (r w) (start w) (ops w) (p w)} ∈
      Cslib.Complexity.CountingLevel 60 Turing.MultiTapeTM.encBits := by
  have hg := guardedBits_mem_FP heTime hpTime
  have hf := (hrTime.prod hg).encoded.computableInPolyTime
  let f := fun w => ExistsForall.encSentence
    (r w, guardedBits (SumSquares.listBits (equations (start w) (ops w))) (p w).encode)
  have hred : PolyTimeReduces {w | SentenceHolds (r w) (start w) (ops w) (p w)}
      ExistsForall.language := by
    refine ⟨f, hf, ?_⟩
    intro w
    dsimp only [f]
    rw [guardedBits_encode, encode_mem_language (r w) (start w) (ops w) (p w) (hr w) (hw w) (hp w)]
    rfl
  exact hred.mem_CountingLevel ExistsForall.mem_CountingLevel

/-- The existential fragment uses the same shared gate equations. -/
def existentialMatrix (start : ℕ) (ops : List Operation) (p : Formula) : Formula :=
  .and (.eqZero (SumSquares.accumulate (equations start ops) (.const 0))) p

theorem existential_iff (start : ℕ) (ops : List Operation) (p : Formula)
    (hw : WellFormed start ops) (hp : p.arity ≤ start + ops.length) :
    (∃ env : ℕ → ℝ, p.Holds (run env start ops)) ↔
      (existentialMatrix start ops p).Satisfiable := by
  constructor
  · rintro ⟨env, h⟩
    exact ⟨run env start ops, (SumSquares.accumulate_zero_iff _ _).mpr
      (run_satisfies env start ops hw), h⟩
  · rintro ⟨env, he, h⟩
    refine ⟨env, (p.holds_congr env (run env start ops) ?_).mp h⟩
    intro i hi
    exact run_unique env env start ops hw (fun _ _ => rfl)
      ((SumSquares.accumulate_zero_iff _ _).mp he) i (hi.trans_le hp)

def existentialBits (equationsBits matrixBits : List Bool) : List Bool :=
  Codec.taggedTwo 4 (Codec.taggedOne 1 (SumSquares.collapse equationsBits)) matrixBits

theorem existentialBits_mem_FP {e p : List Bool → List Bool} (he : e ∈ FP) (hp : p ∈ FP) :
    (fun w => existentialBits (e w) (p w)) ∈ FP :=
  Codec.taggedTwo_mem_FP 4
    (Codec.taggedOne_mem_FP 1
      (mem_FP_comp (f := e) (g := SumSquares.collapse) he SumSquares.collapse_mem_FP)) hp

theorem existentialBits_encode (start : ℕ) (ops : List Operation) (p : Formula) :
    existentialBits (SumSquares.listBits (equations start ops)) p.encode =
      (existentialMatrix start ops p).encode := by
  simp only [existentialBits, SumSquares.collapse_listBits, existentialMatrix, Formula.encode,
    Formula.toData, Codec.taggedTwo_toBits, Codec.taggedOne_toBits]

/-- Native shared-circuit families also inherit the sharper existential bound. -/
theorem generated_feasibility_mem_CountingLevel
    (start : List Bool → ℕ) (ops : List Bool → List Operation) (p : List Bool → Formula)
    (heTime : (fun w => SumSquares.listBits (equations (start w) (ops w))) ∈ FP)
    (hpTime : (fun w => (p w).encode) ∈ FP)
    (hw : ∀ w, WellFormed (start w) (ops w))
    (hp : ∀ w, (p w).arity ≤ start w + (ops w).length) :
    {w | ∃ env : ℕ → ℝ, (p w).Holds (run env (start w) (ops w))} ∈
      Cslib.Complexity.CountingLevel 26 Turing.MultiTapeTM.encBits := by
  have hf := existentialBits_mem_FP heTime hpTime
  have hred : PolyTimeReduces
      {w | ∃ env : ℕ → ℝ, (p w).Holds (run env (start w) (ops w))} ETR.language := by
    refine ⟨_, hf.computableInPolyTime, ?_⟩
    intro w
    rw [existentialBits_encode, ETR.encode_mem_language, ← existential_iff _ _ _ (hw w) (hp w)]
    rfl
  exact hred.mem_CountingLevel etr_mem_CountingLevel

end LeanCanny.CountingHierarchy.RealCircuit
