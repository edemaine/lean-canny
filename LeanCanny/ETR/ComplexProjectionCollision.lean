/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ProjectionCollisionFP

/-! # Native collision formulas for complex projections

Both real and imaginary projection values must agree. Coordinate inequality
accepts a difference in either component. The original binary weights are
retained, and all logical indices lie in the two complex input tuples.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexProjectionCollision
open LeanCanny.Encoding LeanCanny.Computation ComplexCircuit ComplexCircuit.RealQuery.Interleaved
open scoped BigOperators

def agreement (p : Formula) : Formula := .and (p.rename (Interleave.index false)) (p.rename (Interleave.index true))
def formula (n : ℕ) (v : ℕ → ℕ) (i : ℕ) : Formula :=
  .and (agreement (.eqZero (ProjectionCollision.sum n v)))
    (.not (agreement (.eqZero (ProjectionCollision.difference i))))

def projection (n : ℕ) (v : ℕ → ℕ) (x : ℕ → ℂ) : ℂ := ∑ i ∈ Finset.range n, (v i : ℂ) * x i

theorem projection_re (n : ℕ) (v : ℕ → ℕ) (x : ℕ → ℂ) :
    (projection n v x).re = ProjectionCollision.projection n v (fun i => (x i).re) := by
  simp [projection, ProjectionCollision.projection]

theorem projection_im (n : ℕ) (v : ℕ → ℕ) (x : ℕ → ℂ) :
    (projection n v x).im = ProjectionCollision.projection n v (fun i => (x i).im) := by
  simp [projection, ProjectionCollision.projection]

theorem agreement_holds (p : Formula) (x : ℕ → ℂ) :
    (agreement p).Holds (realEnv x) ↔ p.Holds (fun i => (x i).re) ∧ p.Holds (fun i => (x i).im) := by
  simp only [agreement, Formula.Holds, Formula.holds_rename, Function.comp_def, Interleave.index,
    Bool.toNat_false, Bool.toNat_true, Nat.add_zero, realEnv_even, realEnv_odd]

theorem formula_holds (n : ℕ) (v : ℕ → ℕ) (i : ℕ) (x : ℕ → ℂ) :
    (formula n v i).Holds (realEnv x) ↔ projection n v (x ∘ even) = projection n v (x ∘ odd) ∧
      x (even i) ≠ x (odd i) := by
  have hs : (agreement (.eqZero (ProjectionCollision.sum n v))).Holds (realEnv x) ↔
      projection n v (x ∘ even) = projection n v (x ∘ odd) := by
    rw [agreement_holds]
    simp only [Formula.Holds, ProjectionCollision.sum_eval, sub_eq_zero]
    have H : projection n v (x ∘ even) = projection n v (x ∘ odd) ↔
        (projection n v (x ∘ even)).re = (projection n v (x ∘ odd)).re ∧
        (projection n v (x ∘ even)).im = (projection n v (x ∘ odd)).im := Complex.ext_iff
    simpa only [projection_re, projection_im, Function.comp_def] using H.symm
  have hd : (agreement (.eqZero (ProjectionCollision.difference i))).Holds (realEnv x) ↔ x (even i) = x (odd i) := by
    rw [agreement_holds]
    simp only [Formula.Holds, ProjectionCollision.difference_eval, sub_eq_zero]
    exact Complex.ext_iff.symm
  simp only [formula, Formula.Holds, hs, hd]

theorem agreement_FP {p : List Bool → Formula} (hp : (fun c => (p c).encode) ∈ FP) :
    (fun c => (agreement (p c)).encode) ∈ FP := by
  have H := Codec.taggedTwo_mem_FP 4 (mem_FP_comp hp (Interleave.renameBits_mem_FP false))
    (mem_FP_comp hp (Interleave.renameBits_mem_FP true))
  apply mem_FP_of_eq H
  intro c
  simp only [Function.comp_apply]
  rw [Interleave.renameBits_encode, Interleave.renameBits_encode]
  simp only [agreement, Formula.encode, Formula.toData, Codec.taggedTwo_toBits]

theorem formula_FP {n i : List Bool → ℕ} {v : List Bool → ℕ → ℕ}
    (hn : UnaryFn n) (hi : UnaryFn i) (hv : BinaryFn (fun z => v (pairFst z) (pairSnd z).length)) :
    (fun c => (formula (n c) (v c) (i c)).encode) ∈ FP := by
  have hs : (fun c => (Formula.eqZero (ProjectionCollision.sum (n c) (v c))).encode) ∈ FP :=
    by simpa only [Formula.eqZero_encode] using Codec.taggedOne_mem_FP 1 (ProjectionCollision.sum_mem_FP hn hv)
  have hd : (fun c => (Formula.eqZero (ProjectionCollision.difference (i c))).encode) ∈ FP :=
    by simpa only [Formula.eqZero_encode] using Codec.taggedOne_mem_FP 1 (ProjectionCollision.difference_mem_FP hi)
  have H := Codec.taggedTwo_mem_FP 4 (agreement_FP hs) (Codec.taggedOne_mem_FP 3 (agreement_FP hd))
  exact mem_FP_of_eq H (fun _ => by simp only [formula, Formula.encode, Formula.toData,
    Codec.taggedTwo_toBits, Codec.taggedOne_toBits])

theorem term_rename_scope (t : Term) (b : Bool) : (t.rename (Interleave.index b)).arity ≤ 2 * t.arity := by
  induction t with
  | const z => simp only [Term.rename, Term.arity, Nat.mul_zero, le_refl]
  | var i => cases b <;> simp +arith [Term.rename, Term.arity, Interleave.index]
  | add a b ha hb => simp only [Term.rename, Term.arity]; omega
  | mul a b ha hb => simp only [Term.rename, Term.arity]; omega

theorem rename_scope (p : Formula) (b : Bool) : (p.rename (Interleave.index b)).arity ≤ 2 * p.arity := by
  induction p with
  | falsum => simp only [Formula.rename, Formula.arity, Nat.mul_zero, le_refl]
  | eqZero t => exact term_rename_scope t b
  | ltZero t => exact term_rename_scope t b
  | not p h => exact h
  | and p q hp hq => simp only [Formula.rename, Formula.arity]; omega
  | or p q hp hq => simp only [Formula.rename, Formula.arity]; omega

theorem agreement_scope (p : Formula) : (agreement p).arity ≤ 2 * p.arity :=
  max_le (rename_scope p false) (rename_scope p true)

theorem accumulate_scope (ts : List Term) (acc : Term) (N : ℕ) (ha : acc.arity ≤ N)
    (hs : ∀ t ∈ ts, t.arity ≤ N) : (TermSum.accumulate ts acc).arity ≤ N := by
  induction ts generalizing acc with
  | nil => exact ha
  | cons t ts ih =>
    apply ih (Term.add t acc) (max_le (hs t (by simp)) ha)
    intro s h
    exact hs s (by simp only [List.mem_cons]; exact Or.inr h)

theorem sum_scope (n : ℕ) (v : ℕ → ℕ) : (ProjectionCollision.sum n v).arity ≤ 2 * n := by
  apply accumulate_scope _ _ _ (Nat.zero_le _)
  intro t ht
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
  have hin := List.mem_range.mp hi
  simp only [ProjectionCollision.term, ProjectionCollision.difference, Term.arity, even, odd]
  omega

theorem formula_scope (n : ℕ) (v : ℕ → ℕ) (i : ℕ) (hi : i < n) : (formula n v i).arity ≤ 4 * n := by
  have hs := agreement_scope (.eqZero (ProjectionCollision.sum n v))
  have hd := agreement_scope (.eqZero (ProjectionCollision.difference i))
  have hn := sum_scope n v
  have hi' : (ProjectionCollision.difference i).arity ≤ 2 * n := by
    simp only [ProjectionCollision.difference, Term.arity, even, odd]
    omega
  simp only [Formula.arity] at hs hd
  simp only [formula, Formula.arity]
  omega

end LeanCanny.ETR.ComplexProjectionCollision
