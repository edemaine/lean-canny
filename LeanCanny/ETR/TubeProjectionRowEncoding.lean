/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeProjectionGuard

/-! # Total row codes for projection systems

Code zero selects the level row. Positive codes below the point count select
nonbase partial rows in coordinate order, skipping the base index n. All other
codes select the level row. An always-valid partial selector supports uniform
space certificates on every binary input, including rejected row codes.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeProjectionRow
open Complexity
open Geometry TubeEncoding TubeProjectionEncoding
open LeanCanny.Encoding

def Valid (n k : ℕ) : Prop := 0 < k ∧ k < pointCount n
instance (n k : ℕ) : Decidable (Valid n k) := inferInstanceAs (Decidable (_ ∧ _))

def candidate (n k : ℕ) : ℕ := if k - 1 < n then k - 1 else k

def selected (n k : ℕ) : ℕ := if Valid n k then candidate n k else n + 1

theorem selected_lt (n k : ℕ) : selected n k < pointCount n := by
  have hp : n + 2 ≤ pointCount n := by unfold pointCount constraintCount; omega
  by_cases hv : Valid n k
  · rw [selected, ite_eq_left hv]
    have hk := hv.2
    unfold candidate
    split_ifs <;> omega
  · rw [selected, ite_eq_right hv]
    omega

theorem selected_ne_base (n k : ℕ) : selected n k ≠ n := by
  by_cases hv : Valid n k
  · rw [selected, ite_eq_left hv]
    have hk := hv.1
    unfold candidate
    split_ifs <;> omega
  · rw [selected, ite_eq_right hv]
    omega

theorem base_index (n : ℕ) : (pointEquiv n (TubePolynomial.base (Fin n))).val = n :=
  (tube_index_point n _).symm.trans (index_shift_source_false n)

def point (n k : ℕ) : {i : Point n // i ≠ TubePolynomial.base (Fin n)} :=
  ⟨(pointEquiv n).symm ⟨selected n k, selected_lt n k⟩, by
    intro h
    have he := congrArg (fun i => (pointEquiv n i).val) h
    simp only [Equiv.apply_symm_apply, base_index] at he
    exact selected_ne_base n k he⟩

@[simp] theorem point_index (n k : ℕ) : (pointEquiv n (point n k).val).val = selected n k := by
  change ((pointEquiv n) ((pointEquiv n).symm ⟨selected n k, selected_lt n k⟩)).val = _
  rw [Equiv.apply_symm_apply]

def decode (n k : ℕ) : TubePolynomial.ProjectionIndex (Fin n) := if Valid n k then some (point n k) else none

def code (n : ℕ) : TubePolynomial.ProjectionIndex (Fin n) → ℕ
  | none => 0
  | some i => if (pointEquiv n i.val).val < n then (pointEquiv n i.val).val + 1 else (pointEquiv n i.val).val

theorem point_index_ne_base (n : ℕ) (i : {i : Point n // i ≠ TubePolynomial.base (Fin n)}) :
    (pointEquiv n i.val).val ≠ n := by
  intro h
  apply i.property
  apply (pointEquiv n).injective
  apply Fin.ext
  exact h.trans (base_index n).symm

theorem code_lt (n : ℕ) (j : TubePolynomial.ProjectionIndex (Fin n)) : code n j < pointCount n := by
  have hp : n + 2 ≤ pointCount n := by unfold pointCount constraintCount; omega
  cases j with
  | none => simp only [code]; omega
  | some i =>
    have hi := (pointEquiv n i.val).isLt
    simp only [code]
    split_ifs <;> omega

theorem code_valid (n : ℕ) (i : {i : Point n // i ≠ TubePolynomial.base (Fin n)}) : Valid n (code n (some i)) := by
  have hb := point_index_ne_base n i
  have hl := code_lt n (some i)
  refine ⟨?_, hl⟩
  simp only [code]
  split_ifs <;> omega

theorem selected_code (n : ℕ) (i : {i : Point n // i ≠ TubePolynomial.base (Fin n)}) :
    selected n (code n (some i)) = (pointEquiv n i.val).val := by
  rw [selected, ite_eq_left (code_valid n i)]
  have hb := point_index_ne_base n i
  simp only [candidate, code]
  split_ifs <;> omega

@[simp] theorem decode_code (n : ℕ) (j : TubePolynomial.ProjectionIndex (Fin n)) : decode n (code n j) = j := by
  cases j with
  | none => simp [code, decode, Valid]
  | some i =>
    rw [decode, ite_eq_left (code_valid n i)]
    apply congrArg some
    apply Subtype.ext
    apply (pointEquiv n).injective
    apply Fin.ext
    rw [point_index, selected_code]

theorem valid_fppred {n k : List Bool → ℕ} (hn : UnaryFn n) (hk : UnaryFn k) :
    FPPred (fun c => Valid (n c) (k c)) :=
  (FPPred.lt (UnaryFn.const 0) hk).and (FPPred.lt hk (TubeProjectionQuery.pointCount_unary hn))

theorem selected_unary {n k : List Bool → ℕ} (hn : UnaryFn n) (hk : UnaryFn k) :
    UnaryFn (fun c => selected (n c) (k c)) :=
  UnaryFn.ite (valid_fppred hn hk)
    (UnaryFn.ite (FPPred.lt (hk.sub (UnaryFn.const 1)) hn) (hk.sub (UnaryFn.const 1)) hk)
    (hn.add (UnaryFn.const 1))

def index (n : List Bool → ℕ) (word : List Bool → List Bool) (c : List Bool) : ℕ :=
  min (Nat.fromBitsLE (word c)) (pointCount (n c))

theorem index_unary {n : List Bool → ℕ} {word : List Bool → List Bool} (hn : UnaryFn n) (hw : word ∈ FP) :
    UnaryFn (index n word) := UnaryFn.fromBitsLE_min hw (TubeProjectionQuery.pointCount_unary hn)

end LeanCanny.ETR.TubeProjectionRow
