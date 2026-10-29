/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCircuitShift
public import LeanCanny.ETR.ComplexDifferentialSymbolic

/-! # Relocating shared arithmetic sources

Fresh input-copy seeds place a source after a real parent prefix, preserving
sharing and exactly renaming its input polynomials.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit
open MvPolynomial
open scoped Classical

namespace Differential
variable {σ τ : Type*}

theorem symbolicRun_append (wire : ℕ → MvPolynomial σ ℤ) (start : ℕ) (a b : List Operation) :
    symbolicRun wire start (a ++ b) = symbolicRun (symbolicRun wire start a) (start + a.length) b := by
  induction a generalizing wire start with
  | nil => simp only [List.nil_append, symbolicRun, List.length_nil, Nat.add_zero]
  | cons op ops ih =>
    simpa only [List.cons_append, symbolicRun, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using ih
      (Function.update wire start (polynomial wire op)) (start + 1)

theorem symbolicRun_congr_before (wire wire' : ℕ → MvPolynomial σ ℤ) (start : ℕ) (ops : List Operation)
    (hw : StraightLine.WellFormed start ops) (h : ∀ i < start, wire i = wire' i) :
    ∀ i < start + ops.length, symbolicRun wire start ops i = symbolicRun wire' start ops i := by
  induction ops generalizing wire wire' start with
  | nil => simpa only [symbolicRun, List.length_nil, Nat.add_zero] using h
  | cons op ops ih =>
    have hop := polynomial_congr wire wire' start op hw.1 h
    have hu : ∀ i < start + 1,
        Function.update wire start (polynomial wire op) i = Function.update wire' start (polynomial wire' op) i := by
      intro i hi
      by_cases he : i = start
      · simp only [he, Function.update_self, hop]
      · rw [Function.update_of_ne he, Function.update_of_ne he]
        exact h i (by omega)
    intro i hi
    exact ih _ _ (start + 1) hw.2 hu i (by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hi)

theorem symbolicRun_shift (wire : ℕ → MvPolynomial σ ℤ) (base start : ℕ) (ops : List Operation) :
    (fun i => symbolicRun wire (base + start) (ops.map (Operation.shift base)) (base + i)) =
      symbolicRun (fun i => wire (base + i)) start ops := by
  induction ops generalizing wire start with
  | nil => rfl
  | cons op ops ih =>
    have hp : polynomial wire (Operation.shift base op) = polynomial (fun i => wire (base + i)) op := by
      cases op <;> rfl
    have hu : (fun i => Function.update wire (base + start) (polynomial wire (Operation.shift base op)) (base + i)) =
        Function.update (fun i => wire (base + i)) start (polynomial (fun i => wire (base + i)) op) := by
      funext i
      by_cases he : i = start
      · simp [he, hp]
      · simp [Function.update_of_ne he, Function.update_of_ne (show base + i ≠ base + start by omega)]
    simp only [List.map_cons, symbolicRun]
    rw [show base + start + 1 = base + (start + 1) by omega, ih, hu]

theorem symbolicRun_rename (wire : ℕ → MvPolynomial σ ℤ) (f : σ → τ) (start : ℕ) (ops : List Operation) :
    symbolicRun (fun i => rename f (wire i)) start ops = fun i => rename f (symbolicRun wire start ops i) := by
  induction ops generalizing wire start with
  | nil => rfl
  | cons op ops ih =>
    have hp : polynomial (fun i => rename f (wire i)) op = rename f (polynomial wire op) := by
      cases op <;> simp [polynomial]
    have hu : Function.update (fun i => rename f (wire i)) start (polynomial (fun i => rename f (wire i)) op) =
        fun i => rename f (Function.update wire start (polynomial wire op) i) := by
      funext i
      by_cases he : i = start <;> simp [he, hp]
    simp only [symbolicRun, hu, ih]

end Differential

namespace InputRelocation

def seeds (zWire offset count : ℕ) : List Operation :=
  (List.range count).map (fun i => .add (offset + i) zWire)

theorem seeds_length (zWire offset count : ℕ) : (seeds zWire offset count).length = count := by
  simp only [seeds, List.length_map, List.length_range]

theorem seeds_wellFormed (zWire offset base count : ℕ) (hz : zWire < base) (ho : offset + count ≤ base) :
    StraightLine.WellFormed base (seeds zWire offset count) := by
  induction count with
  | zero => trivial
  | succ count ih =>
    rw [seeds, List.range_succ, List.map_append, StraightLine.wellFormed_append]
    refine ⟨ih (by omega), ?_⟩
    simp only [List.length_map, List.length_range, List.map_cons, List.map_nil, StraightLine.WellFormed, Operation.InputsBelow]
    exact ⟨⟨by omega, by omega⟩, trivial⟩

theorem seeds_symbolic {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) (zWire offset base count : ℕ)
    (hz : zWire < base) (ho : offset + count ≤ base) (hzero : wire zWire = 0) :
    ∀ i < count, Differential.symbolicRun wire base (seeds zWire offset count) (base + i) = wire (offset + i) := by
  induction count with
  | zero => intro i hi; omega
  | succ count ih =>
    intro i hi
    rw [seeds, List.range_succ, List.map_append, Differential.symbolicRun_append]
    simp only [List.length_map, List.length_range, List.map_cons, List.map_nil, Differential.symbolicRun]
    by_cases he : i = count
    · subst i
      rw [Function.update_self]
      simp only [Differential.polynomial,
        Differential.symbolicRun_preserves_before wire base _ (offset + count) (by omega),
        Differential.symbolicRun_preserves_before wire base _ zWire hz, hzero, add_zero]
    · rw [Function.update_of_ne (show base + i ≠ base + count by omega)]
      exact ih (by omega) i (by omega)

def program (offset base start : ℕ) (ops : List Operation) : List Operation :=
  .constant 0 :: (seeds base offset start ++ ops.map (Operation.shift (base + 1)))

theorem program_length (offset base start : ℕ) (ops : List Operation) :
    (program offset base start ops).length = 1 + start + ops.length := by
  simp only [program, List.length_cons, List.length_append, seeds_length, List.length_map]
  omega

theorem wellFormed (offset base start : ℕ) (ops : List Operation)
    (ho : offset + start ≤ base) (hw : StraightLine.WellFormed start ops) :
    StraightLine.WellFormed base (program offset base start ops) := by
  refine ⟨trivial, ?_⟩
  rw [StraightLine.wellFormed_append, seeds_length]
  exact ⟨seeds_wellFormed base offset (base + 1) start (by omega) (by omega),
    StraightLine.shift_wellFormed (base + 1) start ops hw⟩

/-- Exact source-polynomial identity, with no expression expansion. -/
theorem symbolic (offset base start : ℕ) (ops : List Operation)
    (ho : offset + start ≤ base) (hw : StraightLine.WellFormed start ops)
    (out : ℕ) (hout : out < start + ops.length) :
    Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) base (program offset base start ops) (base + 1 + out) =
      rename (fun i => offset + i) (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start ops out) := by
  let w : ℕ → MvPolynomial ℕ ℤ := Function.update (fun i => X i) base 0
  have hz : w base = 0 := Function.update_self ..
  have hinput (i : ℕ) (hi : i < start) : w (offset + i) = X (offset + i) :=
    Function.update_of_ne (by omega) _ _
  have hs := seeds_symbolic w base offset (base + 1) start (by omega) (by omega) hz
  have hc := Differential.symbolicRun_congr_before
    (fun i => Differential.symbolicRun w (base + 1) (seeds base offset start) (base + 1 + i))
    (fun i => (rename (fun j => offset + j) (X i) : MvPolynomial ℕ ℤ)) start ops hw
    (fun i hi => (hs i hi).trans (by rw [hinput i hi, rename_X])) out hout
  have hr := congrFun (Differential.symbolicRun_rename (fun i => (X i : MvPolynomial ℕ ℤ))
    (fun i => offset + i) start ops) out
  rw [program, Differential.symbolicRun]
  simp only [Differential.polynomial, map_zero]
  change Differential.symbolicRun w (base + 1) (seeds base offset start ++ ops.map (Operation.shift (base + 1))) _ = _
  rw [Differential.symbolicRun_append, seeds_length]
  exact (congrFun (Differential.symbolicRun_shift _ (base + 1) start ops) out).trans (hc.trans hr)

theorem derivative (offset base start : ℕ) (ops : List Operation)
    (ho : offset + start ≤ base) (hw : StraightLine.WellFormed start ops)
    (out : ℕ) (hout : out < start + ops.length) (j : ℕ) :
    pderiv (offset + j) (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) base
      (program offset base start ops) (base + 1 + out)) =
      rename (fun i => offset + i) (pderiv j
        (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start ops out)) := by
  rw [symbolic offset base start ops ho hw out hout]
  exact pderiv_rename (fun _ _ h => Nat.add_left_cancel h) j _

end InputRelocation
end LeanCanny.ETR.ComplexCircuit
