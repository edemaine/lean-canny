/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubeExpanded
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Finite coordinate and active-set encodings for tube polynomials

Point coordinates precede root-shift coordinates, followed by alpha, epsilon,
and delta. Constraints are ordered as the two source constraints and then
lower/upper box constraints. The active set is one bit per constraint.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeEncoding
open Geometry

abbrev Constraint (n : ℕ) := PolynomialPerturbation.Constraint (Fin n)
abbrev Coordinate (n : ℕ) := TubePolynomial.IntegerCoordinate (Fin n)

def constraintCount (n : ℕ) : ℕ := 2 + n * 2

def dimension (n : ℕ) : ℕ := n + constraintCount n + 3

def constraintEquiv (n : ℕ) : Constraint n ≃ Fin (constraintCount n) :=
  (Equiv.sumCongr finTwoEquiv.symm
    ((Equiv.prodCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finProdFinEquiv)).trans finSumFinEquiv

def parameterEquiv : TubePolynomial.Parameter ≃ Fin 3 :=
  (Equiv.optionCongr finTwoEquiv.symm).trans (finSuccEquiv 2).symm

def coordinateEquiv (n : ℕ) : Coordinate n ≃ Fin (dimension n) :=
  (Equiv.sumCongr ((Equiv.sumCongr (Equiv.refl (Fin n)) (constraintEquiv n)).trans finSumFinEquiv)
    parameterEquiv).trans finSumFinEquiv

@[simp] theorem constraintIndex_source_false (n : ℕ) : (constraintEquiv n (.inl false)).val = 0 := rfl
@[simp] theorem constraintIndex_source_true (n : ℕ) : (constraintEquiv n (.inl true)).val = 1 := rfl
@[simp] theorem constraintIndex_box (n : ℕ) (i : Fin n) (b : Bool) :
    (constraintEquiv n (.inr (i, b))).val = 2 + 2 * i.val + (if b then 1 else 0) := by
  cases b
  · change 2 + (0 + 2 * i.val) = 2 + 2 * i.val + 0
    omega
  · change 2 + (1 + 2 * i.val) = 2 + 2 * i.val + 1
    omega

@[simp] theorem index_shift (n : ℕ) (i : Constraint n) :
    (coordinateEquiv n (.inl (.inr i))).val = n + (constraintEquiv n i).val := rfl

@[simp] theorem index_point (n : ℕ) (i : Fin n) :
    (coordinateEquiv n (.inl (.inl i))).val = i.val := rfl

@[simp] theorem index_shift_source_false (n : ℕ) :
    (coordinateEquiv n (.inl (.inr (.inl false)))).val = n := by
  change n + 0 = n
  omega

@[simp] theorem index_shift_source_true (n : ℕ) :
    (coordinateEquiv n (.inl (.inr (.inl true)))).val = n + 1 := by
  rfl

@[simp] theorem index_shift_box (n : ℕ) (i : Fin n) (b : Bool) :
    (coordinateEquiv n (.inl (.inr (.inr (i, b))))).val = n + 2 + 2 * i.val + (if b then 1 else 0) := by
  cases b
  · change n + (2 + (0 + 2 * i.val)) = n + 2 + 2 * i.val + 0
    omega
  · change n + (2 + (1 + 2 * i.val)) = n + 2 + 2 * i.val + 1
    omega

@[simp] theorem index_alpha (n : ℕ) :
    (coordinateEquiv n (.inr none)).val = n + constraintCount n := by
  change n + constraintCount n + 0 = n + constraintCount n
  omega

@[simp] theorem index_epsilon (n : ℕ) :
    (coordinateEquiv n (.inr (some false))).val = n + constraintCount n + 1 := by
  rfl

@[simp] theorem index_delta (n : ℕ) :
    (coordinateEquiv n (.inr (some true))).val = n + constraintCount n + 2 := by
  rfl

def activeSet (n : ℕ) (bits : List Bool) : Finset (Constraint n) :=
  Finset.univ.filter (fun i => bits[(constraintEquiv n i).val]?.getD false)

def activeCode (n : ℕ) (s : Finset (Constraint n)) : List Bool :=
  List.ofFn (fun i : Fin (constraintCount n) => decide ((constraintEquiv n).symm i ∈ s))

@[simp] theorem activeCode_length (n : ℕ) (s : Finset (Constraint n)) : (activeCode n s).length = constraintCount n :=
  List.length_ofFn

@[simp] theorem activeSet_activeCode (n : ℕ) (s : Finset (Constraint n)) : activeSet n (activeCode n s) = s := by
  ext i
  simp [activeSet, activeCode]

end LeanCanny.ETR.TubeEncoding
