/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexFrozenSource

/-! # Freezing a shared circuit coordinate at an existing parameter wire

The swept variable is redirected to an earlier input wire. Other variables
shift down by one, and all operation outputs are translated consecutively.
The original shared source is retained, with no term or polynomial expansion.
The parameter wire can later hold an irrational critical level or endpoint.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit
open MvPolynomial
open scoped Classical

theorem Differential.realizes_unique {σ : Type*} (wire wire' : ℕ → MvPolynomial σ ℤ)
    (start : ℕ) (ops : List Operation) (hw : StraightLine.WellFormed start ops)
    (hr : Realizes wire start ops) (hr' : Realizes wire' start ops)
    (hin : ∀ i < start, wire i = wire' i) : ∀ i < start + ops.length, wire i = wire' i := by
  induction ops generalizing start with
  | nil => simpa only [List.length_nil, Nat.add_zero] using hin
  | cons op ops ih =>
    have h0 : wire start = wire' start :=
      hr.1.trans ((polynomial_congr wire wire' start op hw.1 hin).trans hr'.1.symm)
    have hb : ∀ i < start + 1, wire i = wire' i := by
      intro i hi
      by_cases h : i < start
      · exact hin i h
      · have he : i = start := by omega
        exact he ▸ h0
    intro i hi
    apply ih (start + 1) hw.2 hr.2 hr'.2 hb i
    simp only [List.length_cons] at hi
    omega

theorem Differential.polynomial_hom {σ τ : Type*}
    (φ : MvPolynomial σ ℤ →+* MvPolynomial τ ℤ) (wire : ℕ → MvPolynomial σ ℤ) (op : Operation) :
    φ (polynomial wire op) = polynomial (fun i => φ (wire i)) op := by
  cases op with
  | constant z => exact map_intCast φ z
  | add a b => exact map_add φ _ _
  | mul a b => exact map_mul φ _ _

theorem Differential.Realizes.hom {σ τ : Type*}
    (φ : MvPolynomial σ ℤ →+* MvPolynomial τ ℤ) (wire : ℕ → MvPolynomial σ ℤ) (start : ℕ) (ops : List Operation)
    (hr : Realizes wire start ops) : Realizes (fun i => φ (wire i)) start ops := by
  induction ops generalizing start with
  | nil => trivial
  | cons op ops ih =>
    exact ⟨(congrArg φ hr.1).trans (polynomial_hom φ wire op), ih (start + 1) hr.2⟩

namespace CircuitFreeze

def index (inputs parameter start i : ℕ) : ℕ :=
  if i < inputs then (if i = 0 then parameter else i - 1) else start + (i - inputs)

def program (inputs parameter start : ℕ) (ops : List Operation) : List Operation :=
  ops.map (Operation.reindex (index inputs parameter start))
def output (inputs parameter start out : ℕ) : ℕ := index inputs parameter start out

noncomputable def substitution (parameter : ℕ) : MvPolynomial ℕ ℤ →+* MvPolynomial ℕ ℤ :=
  eval₂Hom C (fun i => if i = 0 then X parameter else X (i - 1))

theorem index_aux (inputs parameter start q : ℕ) : index inputs parameter start (inputs + q) = start + q := by
  simp only [index, ite_eq_right (show ¬ inputs + q < inputs by omega), Nat.add_sub_cancel_left]

theorem index_lt (inputs parameter start q i : ℕ) (hp : parameter < start) (hs : inputs ≤ start + 1)
    (hi : i < inputs + q) : index inputs parameter start i < start + q := by
  unfold index
  split_ifs <;> omega

theorem program_length (inputs parameter start : ℕ) (ops : List Operation) :
    (program inputs parameter start ops).length = ops.length := List.length_map ..

theorem wellFormed (inputs parameter start : ℕ) (ops : List Operation) (hw : StraightLine.WellFormed inputs ops)
    (hp : parameter < start) (hs : inputs ≤ start + 1) : StraightLine.WellFormed start (program inputs parameter start ops) :=
  StraightLine.reindex_wellFormed _ inputs start ops hw (fun q i hi => index_lt inputs parameter start q i hp hs hi)

theorem gates_eq (inputs parameter start : ℕ) (ops : List Operation) :
    StraightLine.gates start (program inputs parameter start ops) =
      (StraightLine.gates inputs ops).map (Gate.reindex (index inputs parameter start)) :=
  StraightLine.reindex_gates _ inputs start ops (index_aux inputs parameter start)

theorem output_lt (inputs parameter start out : ℕ) (ops : List Operation) (hp : parameter < start)
    (hs : inputs ≤ start + 1) (ho : out < inputs + ops.length) :
    output inputs parameter start out < start + (program inputs parameter start ops).length := by
  rw [program_length]
  exact index_lt inputs parameter start ops.length out hp hs ho

theorem realized_output (wire : ℕ → MvPolynomial ℕ ℤ) (inputs parameter start out : ℕ) (ops : List Operation)
    (hw : StraightLine.WellFormed inputs ops) (hp : parameter < start) (hs : inputs ≤ start + 1)
    (ho : out < inputs + ops.length) (hin : ∀ i < start, wire i = X i)
    (hr : Differential.Realizes wire start (program inputs parameter start ops)) :
    wire (output inputs parameter start out) = substitution parameter
      (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) inputs ops out) := by
  let original := Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) inputs ops
  have hOriginal := Differential.symbolicRun_realizes (fun i => (X i : MvPolynomial ℕ ℤ)) inputs ops hw
  have hMapped := Differential.Realizes.hom (substitution parameter) original inputs ops hOriginal
  have hReindexed := (Differential.reindex_realizes wire (index inputs parameter start) inputs start ops
    (index_aux inputs parameter start)).mp hr
  apply Differential.realizes_unique (fun i => wire (index inputs parameter start i))
    (fun i => substitution parameter (original i)) inputs ops hw hReindexed hMapped ?_ out ho
  intro i hi
  have hlt : index inputs parameter start i < start := by
    simpa only [Nat.add_zero] using index_lt inputs parameter start 0 i hp hs (by omega)
  rw [hin _ hlt, show original i = X i from Differential.symbolicRun_preserves_before _ _ _ i hi]
  simp only [substitution, eval₂Hom_X', index, ite_eq_left hi]
  split_ifs <;> rfl

theorem symbolic_output (inputs parameter start out : ℕ) (ops : List Operation)
    (hw : StraightLine.WellFormed inputs ops) (hp : parameter < start) (hs : inputs ≤ start + 1)
    (ho : out < inputs + ops.length) :
    Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start (program inputs parameter start ops)
      (output inputs parameter start out) = substitution parameter
        (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) inputs ops out) :=
  realized_output _ inputs parameter start out ops hw hp hs ho
    (fun i hi => Differential.symbolicRun_preserves_before _ _ _ i hi)
    (Differential.symbolicRun_realizes _ _ _ (wellFormed inputs parameter start ops hw hp hs))

end CircuitFreeze
end LeanCanny.ETR.ComplexCircuit
