/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexGradientFamily
public import LeanCanny.ETR.ComplexRightInverseEncoding

/-! # Original parent Jacobian guards from shared source programs

The circuit differentiates the selected parent equations in the parent input
block, then checks a right inverse using auxiliary input variables. It keeps
the original parent equations as guard outputs at the same assignment.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.ParentRegularity
open MvPolynomial
open scoped Classical

def copyBase (base : ℕ) : ℕ := base + 2
def inverseBase (base start n : ℕ) (ops : List Operation) : ℕ :=
  copyBase base + n * GradientFamily.stride start ops

def entry (base start : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) (i k : ℕ) : ℕ :=
  GradientFamily.derivativeWire (copyBase base) start ops k (outputs i)

def rootOutput (base start : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) (i : ℕ) : ℕ :=
  GradientFamily.valueWire (copyBase base) start ops 0 (outputs i)

def program (base start inverse n : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) : List Operation :=
  .constant 0 :: .constant 1 ::
    (GradientFamily.program base (copyBase base) start 0 ops n ++
      RightInverse.program base (base + 1) (inverseBase base start n ops) inverse n (entry base start ops outputs) (n * n))

def gates (base start inverse n : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) : List Gate :=
  StraightLine.gates base (program base start inverse n ops outputs)

def guardOutput (base start n : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) (q : ℕ) : ℕ :=
  if q < n then rootOutput base start ops outputs q
  else RightInverse.output (inverseBase base start n ops) n (q - n)

theorem program_length (base start inverse n : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) :
    (program base start inverse n ops outputs).length =
      2 + n * GradientFamily.stride start ops + n * n * RightInverse.stride n := by
  simp only [program, List.length_cons, List.length_append, GradientFamily.program_length, RightInverse.program_length]
  omega

theorem gates_eq (base start inverse n : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) :
    gates base start inverse n ops outputs = .constant base 0 :: .constant (base + 1) 1 ::
      (GradientFamily.gates base (copyBase base) start 0 ops n ++
        RightInverse.gates base (base + 1) (inverseBase base start n ops) inverse n (entry base start ops outputs) (n * n)) := by
  rw [gates, program, StraightLine.gates, StraightLine.gates, StraightLine.gates_append, GradientFamily.program_length]
  rfl

theorem wellFormed (base start inverse n : ℕ) (ops : List Operation) (outputs : ℕ → ℕ)
    (hb : start ≤ base) (hw : StraightLine.WellFormed start ops)
    (he : ∀ i < n, outputs i < start + ops.length) (hu : inverse + n * n ≤ base) :
    StraightLine.WellFormed base (program base start inverse n ops outputs) := by
  refine ⟨trivial, trivial, ?_⟩
  rw [StraightLine.wellFormed_append, GradientFamily.program_length]
  have heq : base + 1 + 1 = copyBase base := by rfl
  rw [heq]
  refine ⟨GradientFamily.wellFormed base (copyBase base) start 0 ops n (by unfold copyBase; omega)
    (by unfold copyBase; omega) hw, ?_⟩
  have hbase : base + 2 ≤ inverseBase base start n ops := by unfold inverseBase copyBase; omega
  apply RightInverse.wellFormed _ _ _ _ _ _ (by omega) (by omega) ?_ (by omega) _ le_rfl
  intro i hi k hk
  exact GradientFamily.derivativeWire_lt_end (copyBase base) start ops n k (outputs i) hk (he i hi)

theorem guardOutput_lt (base start inverse n : ℕ) (ops : List Operation) (outputs : ℕ → ℕ)
    (he : ∀ i < n, outputs i < start + ops.length) (q : ℕ) (hq : q < n + n * n) :
    guardOutput base start n ops outputs q < base + (program base start inverse n ops outputs).length := by
  have hend : base + (program base start inverse n ops outputs).length =
      inverseBase base start n ops + n * n * RightInverse.stride n := by
    rw [program_length]
    unfold inverseBase copyBase
    omega
  rw [hend]
  unfold guardOutput
  split_ifs with hi
  · exact (GradientFamily.valueWire_lt_end (copyBase base) start ops n 0 (outputs q) (by omega) (he q hi)).trans_le
      (Nat.le_add_right _ _)
  · exact RightInverse.output_lt _ _ _ _ (by omega)

theorem zero_one (base start inverse n : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) (env : ℕ → ℂ)
    (hg : ∀ g ∈ gates base start inverse n ops outputs, g.Holds env) :
    env base = 0 ∧ env (base + 1) = 1 := by
  exact ⟨by simpa only [Gate.Holds, Int.cast_zero] using hg (.constant base 0) (by rw [gates_eq]; simp),
    by simpa only [Gate.Holds, Int.cast_one] using hg (.constant (base + 1) 1) (by rw [gates_eq]; simp)⟩

theorem gradient_gates (base start inverse n : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) (env : ℕ → ℂ)
    (hg : ∀ g ∈ gates base start inverse n ops outputs, g.Holds env) :
    ∀ g ∈ GradientFamily.gates base (copyBase base) start 0 ops n, g.Holds env := by
  intro g h
  apply hg g
  rw [gates_eq]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ h))

theorem inverse_gates (base start inverse n : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) (env : ℕ → ℂ)
    (hg : ∀ g ∈ gates base start inverse n ops outputs, g.Holds env) :
    ∀ g ∈ RightInverse.gates base (base + 1) (inverseBase base start n ops) inverse n
      (entry base start ops outputs) (n * n), g.Holds env := by
  intro g h
  apply hg g
  rw [gates_eq]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ h))

theorem jet_sound (wire : ℕ → MvPolynomial ℕ ℤ) (base start inverse n : ℕ) (ops : List Operation) (outputs : ℕ → ℕ)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (x env : ℕ → ℂ) (hx : ∀ i < start, env i = x i)
    (hg : ∀ g ∈ gates base start inverse n ops outputs, g.Holds env)
    (q out : ℕ) (hq : q < n) (ho : out < start + ops.length) :
    env (GradientFamily.valueWire (copyBase base) start ops q out) = (wire out).eval₂ (Int.castRingHom ℂ) x ∧
      env (GradientFamily.derivativeWire (copyBase base) start ops q out) =
        (pderiv q (wire out)).eval₂ (Int.castRingHom ℂ) x := by
  simpa only [Nat.zero_add] using GradientFamily.sound wire base (copyBase base) start 0 ops hw hr hin x env
    (zero_one base start inverse n ops outputs env hg).1 hx n (gradient_gates base start inverse n ops outputs env hg) q hq out ho

noncomputable def matrix (wire : ℕ → MvPolynomial ℕ ℤ) (n : ℕ) (outputs : ℕ → ℕ) (x : ℕ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun i k => (pderiv k.val (wire (outputs i.val))).eval₂ (Int.castRingHom ℂ) x

theorem matrix_sound (wire : ℕ → MvPolynomial ℕ ℤ) (base start inverse n : ℕ) (ops : List Operation) (outputs : ℕ → ℕ)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (he : ∀ i < n, outputs i < start + ops.length)
    (x env : ℕ → ℂ) (hx : ∀ i < start, env i = x i)
    (hg : ∀ g ∈ gates base start inverse n ops outputs, g.Holds env) :
    RightInverse.matrix n (entry base start ops outputs) env = matrix wire n outputs x := by
  apply Matrix.ext
  intro i k
  exact (jet_sound wire base start inverse n ops outputs hw hr hin x env hx hg k.val (outputs i.val) k.isLt (he _ i.isLt)).2

theorem guards_iff (wire : ℕ → MvPolynomial ℕ ℤ) (base start inverse n : ℕ) (ops : List Operation) (outputs : ℕ → ℕ)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (he : ∀ i < n, outputs i < start + ops.length)
    (x env : ℕ → ℂ) (hx : ∀ i < start, env i = x i)
    (hg : ∀ g ∈ gates base start inverse n ops outputs, g.Holds env) :
    (∀ q < n + n * n, env (guardOutput base start n ops outputs q) = 0) ↔
      (∀ i < n, (wire (outputs i)).eval₂ (Int.castRingHom ℂ) x = 0) ∧
        matrix wire n outputs x * RightInverse.inverseMatrix inverse n env = 1 := by
  obtain ⟨hz, ho⟩ := zero_one base start inverse n ops outputs env hg
  have hM := matrix_sound wire base start inverse n ops outputs hw hr hin he x env hx hg
  have hI := RightInverse.constraints_iff base (base + 1) (inverseBase base start n ops) inverse n
    (entry base start ops outputs) env hz ho (inverse_gates base start inverse n ops outputs env hg)
  rw [hM] at hI
  have hroot (i : ℕ) (hi : i < n) : env (rootOutput base start ops outputs i) = (wire (outputs i)).eval₂ (Int.castRingHom ℂ) x :=
    (jet_sound wire base start inverse n ops outputs hw hr hin x env hx hg 0 (outputs i) (by omega) (he i hi)).1
  constructor
  · intro hzero
    refine ⟨fun i hi => (hroot i hi).symm.trans ?_, hI.mp ?_⟩
    · simpa only [guardOutput, hi, ite_true] using hzero i (by omega)
    · intro q hq
      have H := hzero (n + q) (by omega)
      simpa only [guardOutput, show ¬ n + q < n by omega, ite_false, Nat.add_sub_cancel_left] using H
  · rintro ⟨hroots, hproduct⟩ q hq
    unfold guardOutput
    split_ifs with hi
    · exact (hroot q hi).trans (hroots q hi)
    · exact hI.mpr hproduct (q - n) (by omega)

theorem regular_of_guards (wire : ℕ → MvPolynomial ℕ ℤ) (base start inverse n : ℕ) (ops : List Operation) (outputs : ℕ → ℕ)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (he : ∀ i < n, outputs i < start + ops.length)
    (x env : ℕ → ℂ) (hx : ∀ i < start, env i = x i)
    (hg : ∀ g ∈ gates base start inverse n ops outputs, g.Holds env)
    (hzero : ∀ q < n + n * n, env (guardOutput base start n ops outputs q) = 0) :
    (∀ i < n, (wire (outputs i)).eval₂ (Int.castRingHom ℂ) x = 0) ∧ (matrix wire n outputs x).det ≠ 0 := by
  obtain ⟨hp, hI⟩ := (guards_iff wire base start inverse n ops outputs hw hr hin he x env hx hg).mp hzero
  exact ⟨hp, (RightInverse.exists_inverse_iff n _).mp ⟨_, hI⟩⟩

/-- Complete the fresh circuit while retaining all existing inputs and the
chosen auxiliary inverse matrix. -/
theorem exists_completion (wire : ℕ → MvPolynomial ℕ ℤ) (base start inverse n : ℕ) (ops : List Operation) (outputs : ℕ → ℕ)
    (hb : start ≤ base) (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (he : ∀ i < n, outputs i < start + ops.length)
    (hu : inverse + n * n ≤ base) (x : ℕ → ℂ)
    (hp : ∀ i < n, (wire (outputs i)).eval₂ (Int.castRingHom ℂ) x = 0)
    (hI : matrix wire n outputs x * RightInverse.inverseMatrix inverse n x = 1) :
    ∃ env : ℕ → ℂ, (∀ i < base, env i = x i) ∧
      (∀ g ∈ gates base start inverse n ops outputs, g.Holds env) ∧
      ∀ q < n + n * n, env (guardOutput base start n ops outputs q) = 0 := by
  obtain ⟨env, henv, hg⟩ := StraightLine.exists_completion x base (program base start inverse n ops outputs)
    (wellFormed base start inverse n ops outputs hb hw he hu)
  have hB : RightInverse.inverseMatrix inverse n env = RightInverse.inverseMatrix inverse n x := by
    apply Matrix.ext
    intro k j
    apply henv
    have hj := j.isLt
    have hk := k.isLt
    have H : j.val * n + k.val < n * n := by nlinarith
    omega
  refine ⟨env, henv, hg, ?_⟩
  apply (guards_iff wire base start inverse n ops outputs hw hr hin he x env (fun i hi => henv i (hi.trans_le hb)) hg).mpr
  exact ⟨hp, hB.symm ▸ hI⟩

end LeanCanny.ETR.ComplexCircuit.ParentRegularity
