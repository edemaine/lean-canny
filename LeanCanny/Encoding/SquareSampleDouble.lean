/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleComplete
public import LeanCanny.Algebra.BlockRenameCoefficient

/-! # Two independent copies of a complete finite square sampler

Disjoint blocks retain the original coordinate annihilators. Pairing finite
roots therefore needs no new elimination polynomial. This is a transient
pair sampler; recursive children can project its shared ancestry only once.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleDouble
open LeanCanny.Algebra MvPolynomial
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def offset (n : ℕ) (right : Bool) : ℕ := if right then n else 0

def slot (n : ℕ) (right : Bool) : Fin n → Fin (n + n) :=
  BlockRenameCoefficient.shift n (n + n) (offset n right) (by cases right <;> simp [offset])

def side (n : ℕ) (j : Fin (n + n)) : Bool := decide (n ≤ j.val)

def index (n : ℕ) (j : Fin (n + n)) : Fin n :=
  ⟨if j.val < n then j.val else j.val - n, by have := j.isLt; split_ifs <;> omega⟩

theorem slot_val (n : ℕ) (right : Bool) (i : Fin n) : (slot n right i).val = offset n right + i.val := rfl

theorem side_slot (n : ℕ) (right : Bool) (i : Fin n) : side n (slot n right i) = right := by
  unfold side
  rw [slot_val]
  cases right <;> simp only [offset, Bool.false_eq_true, ↓reduceIte] <;> simp [i.isLt]

theorem index_slot (n : ℕ) (right : Bool) (i : Fin n) : index n (slot n right i) = i := by
  apply Fin.ext
  change (if (slot n right i).val < n then (slot n right i).val else (slot n right i).val - n) = i.val
  rw [slot_val]
  cases right <;> simp only [offset, Bool.false_eq_true, ↓reduceIte] <;>
    split_ifs <;> have := i.isLt <;> omega

theorem slot_index (n : ℕ) (j : Fin (n + n)) : slot n (side n j) (index n j) = j := by
  apply Fin.ext
  rw [slot_val]
  by_cases h : n ≤ j.val
  · have hs : side n j = true := by simp only [side, h, decide_true]
    rw [hs]
    change n + (if j.val < n then j.val else j.val - n) = j.val
    rw [ite_eq_right (by omega)]
    omega
  · have hs : side n j = false := by simp only [side, h, decide_false]
    rw [hs]
    change 0 + (if j.val < n then j.val else j.val - n) = j.val
    rw [ite_eq_left (by omega), Nat.zero_add]

noncomputable def system (F : Inputs) (u : List Bool) (j : Fin (F.count u + F.count u)) :
    MvPolynomial (Fin (F.count u + F.count u)) ℤ :=
  rename (slot (F.count u) (side (F.count u) j)) (F.system u (index (F.count u) j))

theorem system_slot (F : Inputs) (u : List Bool) (right : Bool) (i : Fin (F.count u)) :
    system F u (slot (F.count u) right i) = rename (slot (F.count u) right) (F.system u i) := by
  rw [system, side_slot, index_slot]

theorem roots_iff (F : Inputs) (u : List Bool) (z : Fin (F.count u + F.count u) → ℝ) :
    (∀ j, (system F u j).eval₂ (Int.castRingHom ℝ) z = 0) ↔
      (∀ right : Bool, ∀ i, (F.system u i).eval₂ (Int.castRingHom ℝ) (z ∘ slot (F.count u) right) = 0) := by
  constructor
  · intro h right i
    have H := h (slot (F.count u) right i)
    simpa only [system_slot, eval₂_rename] using H
  · intro h j
    exact (eval₂_rename _ _ _ _).trans (h (side (F.count u) j) (index (F.count u) j))

theorem annihilate (F : Inputs) (hF : SquareSampleComplete.Complete F) (u : List Bool)
    (z : Fin (F.count u + F.count u) → ℝ)
    (hz : ∀ j, (system F u j).eval₂ (Int.castRingHom ℝ) z = 0) (i : Fin (F.count u + F.count u)) :
    (F.annihilator u (index (F.count u) i)).eval₂ (Int.castRingHom ℝ) (z i) = 0 := by
  have H := hF u (z ∘ slot (F.count u) (side (F.count u) i))
    ((roots_iff F u z).mp hz (side (F.count u) i)) (index (F.count u) i)
  simpa only [Function.comp_apply, slot_index] using H

noncomputable def input (F : Inputs) (hF : SquareSampleComplete.Complete F) : Inputs where
  count u := F.count u + F.count u
  degree := F.degree
  mass := F.mass
  system := system F
  count_pos u := by have := F.count_pos u; omega
  degree_pos := F.degree_pos
  system_degree u i := (totalDegree_rename_le _ _).trans (F.system_degree u (index (F.count u) i))
  system_mass u i := (MvMass.rename_le _ _).trans (F.system_mass u (index (F.count u) i))
  annihilator u i := F.annihilator u (index (F.count u) i)
  annDegree := F.annDegree
  annHeight := F.annHeight
  ann_nonzero u i := F.ann_nonzero u (index (F.count u) i)
  ann_degree u i := F.ann_degree u (index (F.count u) i)
  ann_height u i j := F.ann_height u (index (F.count u) i) j
  ann_root u z hz _ i := annihilate F hF u z hz i

theorem complete (F : Inputs) (hF : SquareSampleComplete.Complete F) : SquareSampleComplete.Complete (input F hF) :=
  annihilate F hF

noncomputable def point (F : Inputs) (u : List Bool) (x y : Fin (F.count u) → ℝ)
    (j : Fin (F.count u + F.count u)) : ℝ :=
  if side (F.count u) j then y (index (F.count u) j) else x (index (F.count u) j)

theorem point_slot (F : Inputs) (u : List Bool) (x y : Fin (F.count u) → ℝ) (right : Bool) (i : Fin (F.count u)) :
    point F u x y (slot (F.count u) right i) = if right then y i else x i := by
  simp only [point, side_slot, index_slot]

noncomputable def pair (F : Inputs) (hF : SquareSampleComplete.Complete F) (u : List Bool)
    (x y : SquareSampleComplete.Roots F u) : SquareSampleComplete.Roots (input F hF) u := by
  refine ⟨point F u x.val y.val, (roots_iff F u _).mpr ?_⟩
  intro right i
  have H : point F u x.val y.val ∘ slot (F.count u) right = if right then y.val else x.val := by
    funext j
    exact (point_slot F u x.val y.val right j).trans (by cases right <;> rfl)
  rw [H]
  cases right
  · exact x.property i
  · exact y.property i

noncomputable def project (F : Inputs) (hF : SquareSampleComplete.Complete F) (u : List Bool) (right : Bool)
    (z : SquareSampleComplete.Roots (input F hF) u) : SquareSampleComplete.Roots F u :=
  ⟨z.val ∘ slot (F.count u) right, (roots_iff F u z.val).mp z.property right⟩

theorem project_pair (F : Inputs) (hF : SquareSampleComplete.Complete F) (u : List Bool) (right : Bool)
    (x y : SquareSampleComplete.Roots F u) : project F hF u right (pair F hF u x y) = if right then y else x := by
  apply Subtype.ext
  funext i
  exact (point_slot F u x.val y.val right i).trans (by cases right <;> rfl)

theorem pair_project (F : Inputs) (hF : SquareSampleComplete.Complete F) (u : List Bool)
    (z : SquareSampleComplete.Roots (input F hF) u) :
    pair F hF u (project F hF u false z) (project F hF u true z) = z := by
  apply Subtype.ext
  funext j
  change (if side (F.count u) j then z.val (slot (F.count u) true (index (F.count u) j))
    else z.val (slot (F.count u) false (index (F.count u) j))) = z.val j
  have H := congrArg z.val (slot_index (F.count u) j)
  cases hs : side (F.count u) j <;> simpa only [hs, Bool.false_eq_true, ↓reduceIte] using H

end LeanCanny.Encoding.SquareSampleDouble
