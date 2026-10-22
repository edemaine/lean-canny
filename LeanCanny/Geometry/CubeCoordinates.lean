/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Canny's rational coordinates on the open unit cube

The map y / (1-y^2) covers the real line. An explicit inverse supplies a
coordinatewise preimage, and every finite cube point lies in a closed cube with
a positive margin from its boundary.
-/

@[expose] public section

namespace LeanCanny.Geometry.CubeCoordinates

noncomputable def toLine (y : ℝ) : ℝ := y / (1 - y ^ 2)

noncomputable def toCube (x : ℝ) : ℝ := 2 * x / (1 + Real.sqrt (1 + 4 * x ^ 2))

theorem one_sub_sq_pos (y : ℝ) (hy : -1 < y ∧ y < 1) : 0 < 1 - y ^ 2 := by
  have h := mul_pos (by linarith : 0 < 1 - y) (by linarith : 0 < 1 + y)
  nlinarith

theorem toCube_denominator (x : ℝ) :
    1 - toCube x ^ 2 = 2 / (1 + Real.sqrt (1 + 4 * x ^ 2)) := by
  have hs : Real.sqrt (1 + 4 * x ^ 2) ^ 2 = 1 + 4 * x ^ 2 := Real.sq_sqrt (by positivity)
  have hd : 0 < 1 + Real.sqrt (1 + 4 * x ^ 2) := by positivity
  unfold toCube
  generalize he : Real.sqrt (1 + 4 * x ^ 2) = s at *
  field_simp [ne_of_gt hd]
  nlinarith

theorem toCube_mem (x : ℝ) : -1 < toCube x ∧ toCube x < 1 := by
  have hd : 0 < 1 - toCube x ^ 2 := by rw [toCube_denominator]; positivity
  constructor <;> nlinarith [sq_nonneg (toCube x + 1), sq_nonneg (toCube x - 1)]

theorem toLine_toCube (x : ℝ) : toLine (toCube x) = x := by
  have hd : 1 + Real.sqrt (1 + 4 * x ^ 2) ≠ 0 := ne_of_gt (by positivity)
  rw [toLine, toCube_denominator, toCube]
  field_simp [hd]

def OpenCube {ι : Type*} (y : ι → ℝ) : Prop := ∀ i, -1 < y i ∧ y i < 1

def closedCube (ι : Type*) (epsilon : ℝ) : Set (ι → ℝ) :=
  Set.Icc (fun _ => -1 + epsilon) (fun _ => 1 - epsilon)

noncomputable def coordinates {ι : Type*} (y : ι → ℝ) : ι → ℝ := fun i => toLine (y i)

theorem exists_preimage {ι : Type*} (x : ι → ℝ) : ∃ y : ι → ℝ, OpenCube y ∧ coordinates y = x := by
  refine ⟨fun i => toCube (x i), fun i => toCube_mem (x i), ?_⟩
  funext i
  exact toLine_toCube (x i)

theorem exists_iff_openCube {ι : Type*} (P : (ι → ℝ) → Prop) :
    (∃ x, P x) ↔ ∃ y, OpenCube y ∧ P (coordinates y) := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, he⟩ := exists_preimage x
    exact ⟨y, hy, he.symm ▸ hx⟩
  · rintro ⟨y, _, hy⟩
    exact ⟨coordinates y, hy⟩

theorem finite_positive_margin {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 < f i) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ i ∈ s, epsilon ≤ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨epsilon, he, hs⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    refine ⟨min epsilon (f i), lt_min he (hf i (Finset.mem_insert_self _ _)), ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hs j hj)

theorem openCube_iff_exists_margin {ι : Type*} [Fintype ι] (y : ι → ℝ) :
    OpenCube y ↔ ∃ epsilon : ℝ, 0 < epsilon ∧ y ∈ closedCube ι epsilon := by
  constructor
  · intro hy
    obtain ⟨epsilon, he, hm⟩ := finite_positive_margin Finset.univ
      (fun i => min (y i + 1) (1 - y i)) (fun i _ => lt_min (by linarith [(hy i).1]) (by linarith [(hy i).2]))
    refine ⟨epsilon, he, ?_, ?_⟩ <;> intro i
    · have := (hm i (Finset.mem_univ i)).trans (min_le_left _ _)
      linarith
    · have := (hm i (Finset.mem_univ i)).trans (min_le_right _ _)
      linarith
  · rintro ⟨epsilon, he, hlo, hhi⟩ i
    exact ⟨by linarith [hlo i], by linarith [hhi i]⟩

theorem closedCube_mono {ι : Type*} {epsilon eta : ℝ} (h : eta ≤ epsilon) :
    closedCube ι epsilon ⊆ closedCube ι eta := by
  rintro y ⟨hlo, hhi⟩
  exact ⟨fun i => by linarith [hlo i], fun i => by linarith [hhi i]⟩

theorem isCompact_closedCube (ι : Type*) (epsilon : ℝ) : IsCompact (closedCube ι epsilon) := isCompact_Icc

end LeanCanny.Geometry.CubeCoordinates
