/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineRowPolynomials

/-! # Dispatch components are the actual positively completed affine rows -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineRowIdentity
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineRowLayout FlatAffineRowPolynomials
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullCriticalSamples.polynomial FlatAffineFullSourceTower.system

variable (F : Inputs) (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u))

noncomputable def mappedLevel (u : List Bool) {k : ℕ} : FlatAffineCriticalTower.Level (arity F u) k ℤ →
    MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ
  | .constant c => C c
  | .height m a => AffineHeightPolynomial.polynomial a (fun i => coordinate F u m.val i.val)
  | .midpoint l r a => AffineHeightPolynomial.polynomial a (fun i => coordinate F u l.val i.val) +
      AffineHeightPolynomial.polynomial a (fun i => coordinate F u r.val i.val)

theorem mappedLevel_eq (u : List Bool) (k : ℕ) (hk : k < F.depth u)
    (v : FlatAffineCriticalTower.Level (arity F u) k ℤ) :
    rename Fin.castSucc (rename (FlatAffineCriticalIndexedRows.embedding k hk) (rename Sum.inl v.polynomial)) =
      mappedLevel F u v := by
  rw [FlatAffineCriticalIndexedRows.rename_level]
  cases v with
  | constant c => exact rename_C _ _
  | height m a =>
    simp only [mappedLevel, AffineHeightPolynomial.polynomial, map_sum, map_mul, rename_C, rename_X]
    apply Finset.sum_congr rfl
    intro i _
    rw [coordinate_current F u m.val (m.isLt.trans hk) i]
    rfl
  | midpoint l r a =>
    simp only [mappedLevel, AffineHeightPolynomial.polynomial, map_add, map_sum, map_mul, rename_C, rename_X]
    congr 1 <;> apply Finset.sum_congr rfl
    · intro i _; rw [coordinate_current F u l.val (l.isLt.trans hk) i]; rfl
    · intro i _; rw [coordinate_current F u r.val (r.isLt.trans hk) i]; rfl

theorem actualLevel_eq (u : List Bool) :
    mappedLevel F u (FlatAffineFullSourceTower.level F u (stage F row u) (height F row u)) = oldLevel F row u := by
  unfold FlatAffineFullSourceTower.level oldLevel levelRecord
  dsimp only
  split_ifs <;> rfl

theorem tower_eq (u : List Bool) : FlatAffineFullSourceTower.system F u =
    FlatAffineCriticalTower.system (BoundedFullCriticalSamples.polynomial F.source u)
      (FlatAffineFullSourceTower.free F u) (FlatAffineFullSourceTower.direction F u)
      (FlatAffineFullSourceTower.level F u) (F.depth u) := by
  unfold FlatAffineFullSourceTower.system FlatAffineFullSourceTower.family
  rfl

theorem current_cast (u : List Bool) (h : index F row u < FlatAffineFullSourceTower.count F u) :
    Fin.castSucc ∘ FlatAffineCriticalIndexedRows.current (stage F row u) (stage_lt F row u h) = current F row u := by
  funext i
  exact (coordinate_current F u _ (stage_lt F row u h) i).symm

theorem multiplier_cast (u : List Bool) (h : index F row u < FlatAffineFullSourceTower.count F u) :
    Fin.castSucc ∘ FlatAffineCriticalIndexedRows.multiplier (stage F row u) (stage_lt F row u h) = multiplier F row u := by
  funext j
  exact (coordinate_multiplier F u _ (stage_lt F row u h) j).symm

theorem source_index (u : List Bool) (h : index F row u < FlatAffineFullSourceTower.count F u)
    (hs : slot F row u = arity F u) :
    (⟨index F row u, h⟩ : Fin (FlatAffineFullSourceTower.count F u)) =
      FlatAffineCriticalIndexedRows.multiplier (stage F row u) (stage_lt F row u h) 0 := by
  apply Fin.ext
  change index F row u = offset F row u + (arity F u + 0)
  simpa only [hs, Nat.add_zero] using (split_index F row u).symm

theorem gradient_index (u : List Bool) (h : index F row u < FlatAffineFullSourceTower.count F u)
    (hs : slot F row u < arity F u) :
    (⟨index F row u, h⟩ : Fin (FlatAffineFullSourceTower.count F u)) =
      FlatAffineCriticalIndexedRows.current (stage F row u) (stage_lt F row u h) (spatial F row u) := by
  apply Fin.ext
  change index F row u = offset F row u + min (slot F row u) (arity F u - 1)
  rw [Nat.min_eq_left (by omega)]
  exact (split_index F row u).symm

theorem height_index (u : List Bool) (h : index F row u < FlatAffineFullSourceTower.count F u)
    (hs : arity F u < slot F row u) :
    (⟨index F row u, h⟩ : Fin (FlatAffineFullSourceTower.count F u)) =
      FlatAffineCriticalIndexedRows.multiplier (stage F row u) (stage_lt F row u h) (height F row u).succ := by
  have hl : slot F row u < arity F u + (arity F u + 1) := Nat.mod_lt _ (width_pos F u)
  apply Fin.ext
  change index F row u = offset F row u + (arity F u + (min (slot F row u - arity F u - 1) (arity F u - 1) + 1))
  rw [Nat.min_eq_left (by omega)]
  have he := split_index F row u
  omega

theorem row_eq (u : List Bool) : FlatAffineFullSourcePositive.system F u (row u) = polynomial F row u := by
  by_cases h : index F row u < FlatAffineFullSourceTower.count F u
  · let i : Fin (FlatAffineFullSourceTower.count F u) := ⟨index F row u, h⟩
    have hi : row u = i.castSucc := Fin.ext rfl
    rw [hi, FlatAffineFullSourcePositive.system, PositivePolynomialSystem.old_row, tower_eq]
    unfold polynomial
    rw [ite_eq_left h]
    by_cases hs : slot F row u < arity F u
    · rw [ite_eq_left hs, show i = _ from gradient_index F row u h hs,
        FlatAffineCriticalIndexedRows.gradient_row]
      unfold gradient
      have hc := current_cast F row u h
      have hm := multiplier_cast F row u h
      dsimp +instances only [FlatAffineFullSourcePositive.count, FlatAffineFullSourceTower.count,
        FlatAffineFullSourceTower.stageWidth, FlatAffineFullSourceTower.arity] at hc hm ⊢
      simp only [map_sub, map_sum, map_mul, rename_C, rename_X, rename_rename, hc]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun z => C (FlatAffineFullSourceTower.direction F u (stage F row u) j (spatial F row u)) * X z)
        (congrFun hm j)
    · rw [ite_eq_right hs]
      by_cases he : slot F row u = arity F u
      · rw [ite_eq_left he, show i = _ from source_index F row u h he,
          FlatAffineCriticalIndexedRows.source_row]
        unfold source
        have hc := current_cast F row u h
        dsimp +instances only [FlatAffineFullSourcePositive.count, FlatAffineFullSourceTower.count,
          FlatAffineFullSourceTower.stageWidth, FlatAffineFullSourceTower.arity] at hc ⊢
        rw [rename_rename, hc]
      · rw [ite_eq_right he, show i = _ from height_index F row u h (by omega),
          FlatAffineCriticalIndexedRows.level_row]
        have hl : (height F row u) ∈ FlatAffineFullSourceTower.free F u (stage F row u) ↔
            FlatAffineFullSourceTower.active (levelRecord F row u) = true := by
          simp only [FlatAffineFullSourceTower.free, Finset.mem_filter, Finset.mem_univ, true_and]
          rfl
        by_cases ha : FlatAffineFullSourceTower.active (levelRecord F row u) = true
        · have hmapped := mappedLevel_eq F u (stage F row u) (stage_lt F row u h)
            (FlatAffineFullSourceTower.level F u (stage F row u) (height F row u))
          have hactual := actualLevel_eq F row u
          dsimp +instances only [FlatAffineFullSourcePositive.count, FlatAffineFullSourceTower.count,
            FlatAffineFullSourceTower.stageWidth, FlatAffineFullSourceTower.arity] at hmapped hactual ⊢
          rw [ite_eq_left (hl.mpr ha), map_sub, hmapped, hactual]
          simp only [levelRow, ha, ite_true, currentHeight, AffineHeightPolynomial.polynomial,
            map_sum, map_mul, rename_C, rename_X]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [← coordinate_current F u _ (stage_lt F row u h) j]
          rfl
        · rw [ite_eq_right (fun hh => ha (hl.mp hh)), rename_X]
          simp only [levelRow, ha]
          exact congrArg X (congrFun (multiplier_cast F row u h) (height F row u).succ)
  · have hi : row u = Fin.last (FlatAffineFullSourceTower.count F u) := by
      apply Fin.ext
      have H := (row u).isLt
      change index F row u < FlatAffineFullSourceTower.count F u + 1 at H
      change index F row u = FlatAffineFullSourceTower.count F u
      omega
    rw [hi, FlatAffineFullSourcePositive.system, PositivePolynomialSystem.new_row]
    simp only [polynomial, h, ite_false]

end LeanCanny.Encoding.FlatAffineRowIdentity
