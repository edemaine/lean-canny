/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffinePowerRowReaders
public import LeanCanny.Algebra.FlatAffinePowerOriginal

/-! # Actual positively completed power towers and their native row readers -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerPositive
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineRowLayout FlatAffineRowIdentity
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullCriticalSamples.polynomial

noncomputable def rawSystem (F : Inputs) (u : List Bool) :
    Fin (FlatAffineFullSourceTower.count F u) → MvPolynomial (Fin (FlatAffineFullSourceTower.count F u)) ℤ :=
  FlatAffinePowerTower.system (BoundedFullCriticalSamples.polynomial F.source u) (FlatAffinePowerControls.degree F u)
    (fun t : Fin (F.depth u) => FlatAffineFullSourceTower.free F u t.val)
    (fun t => FlatAffineFullSourceTower.direction F u t.val)
    (fun t => FlatAffineFullSourceTower.level F u t.val)

noncomputable def system (F : Inputs) (u : List Bool) :
    Fin (FlatAffineFullSourcePositive.count F u) → MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ :=
  PositivePolynomialSystem.system (rawSystem F u)

lemma current_cast (F : Inputs) (u : List Bool) (t : Fin (F.depth u)) :
    Fin.castSucc ∘ FlatAffinePowerTower.current (n := arity F u) t =
      fun i : Fin (arity F u) => coordinate F u t.val i.val := by
  funext i
  rw [Function.comp_apply, FlatAffinePowerTower.current_eq, ← coordinate_current F u t.val t.isLt i]

lemma multiplier_cast (F : Inputs) (u : List Bool) (t : Fin (F.depth u)) :
    Fin.castSucc ∘ FlatAffinePowerTower.multiplier (n := arity F u) t =
      fun r : Fin (arity F u + 1) => coordinate F u t.val (arity F u + r.val) := by
  funext r
  rw [Function.comp_apply, FlatAffinePowerTower.multiplier_eq, ← coordinate_multiplier F u t.val t.isLt r]

lemma levelPolynomial_eq (F : Inputs) (u : List Bool) (t : Fin (F.depth u))
    (v : FlatAffineCriticalTower.Level (arity F u) t.val ℤ) :
    rename Fin.castSucc (FlatAffinePowerTower.levelPolynomial t v) = mappedLevel F u v := by
  cases v with
  | constant c =>
    simp only [FlatAffinePowerTower.levelPolynomial, FlatAffinePowerTower.levelLinear,
      FlatAffinePowerTower.levelConstant, zero_add, rename_C, mappedLevel]
    rfl
  | height j a =>
    simp only [FlatAffinePowerTower.levelPolynomial, FlatAffinePowerTower.levelLinear,
      FlatAffinePowerTower.levelConstant, map_zero, add_zero, FlatAffinePowerTower.height,
      mappedLevel, AffineHeightPolynomial.polynomial, map_sum, map_mul, rename_C, rename_X]
    apply Finset.sum_congr rfl
    intro i _
    rw [show Fin.castSucc (FlatAffinePowerTower.current (n := arity F u) ⟨j.val, j.isLt.trans t.isLt⟩ i) =
      coordinate F u j.val i.val from congrFun (current_cast F u ⟨j.val, j.isLt.trans t.isLt⟩) i]
    rfl
  | midpoint l r a =>
    simp only [FlatAffinePowerTower.levelPolynomial, FlatAffinePowerTower.levelLinear,
      FlatAffinePowerTower.levelConstant, map_zero, add_zero, FlatAffinePowerTower.height,
      mappedLevel, AffineHeightPolynomial.polynomial, map_add, map_sum, map_mul, rename_C, rename_X]
    congr 1 <;> apply Finset.sum_congr rfl
    · intro i _
      rw [show Fin.castSucc (FlatAffinePowerTower.current (n := arity F u) ⟨l.val, l.isLt.trans t.isLt⟩ i) =
        coordinate F u l.val i.val from congrFun (current_cast F u ⟨l.val, l.isLt.trans t.isLt⟩) i]
      rfl
    · intro i _
      rw [show Fin.castSucc (FlatAffinePowerTower.current (n := arity F u) ⟨r.val, r.isLt.trans t.isLt⟩ i) =
        coordinate F u r.val i.val from congrFun (current_cast F u ⟨r.val, r.isLt.trans t.isLt⟩) i]
      rfl

lemma row_eq (F : Inputs) (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (u : List Bool) :
    system F u (row u) = FlatAffinePowerRowReaders.polynomial F row u := by
  by_cases h : index F row u < FlatAffineFullSourceTower.count F u
  · let i : Fin (FlatAffineFullSourceTower.count F u) := ⟨index F row u, h⟩
    let t : Fin (F.depth u) := ⟨stage F row u, stage_lt F row u h⟩
    have hi : row u = i.castSucc := Fin.ext rfl
    rw [hi, system, PositivePolynomialSystem.old_row]
    dsimp only [FlatAffineFullSourcePositive.count]
    unfold FlatAffinePowerRowReaders.polynomial FlatAffineRowSourceReaders.old
    rw [ite_eq_left h]
    by_cases hs : slot F row u < arity F u
    · have hj : i = FlatAffinePowerTower.rowEquiv (arity F u) (F.depth u) (t, Sum.inl (spatial F row u)) :=
        (gradient_index F row u h hs).trans (FlatAffinePowerTower.current_eq t (spatial F row u)).symm
      rw [ite_eq_left hs, hj, rawSystem, FlatAffinePowerTower.system_row]
      have hc := current_cast F u t
      have hm := multiplier_cast F u t
      dsimp +instances only [FlatAffineFullSourcePositive.count, FlatAffineFullSourceTower.count, FlatAffineFullSourceTower.stageWidth, FlatAffineFullSourceTower.arity, FlatAffinePowerTower.Index] at hc hm ⊢
      simp only [FlatAffinePowerTower.row, FlatAffinePowerTower.gradient, map_sub, map_sum, map_mul,
        map_pow, rename_C, rename_X, rename_rename]
      rw [hc]
      unfold FlatAffinePowerRowReaders.gradient FlatAffineRowSourceReaders.derivativePolynomial
      rw [FlatAffinePowerRowReaders.muPower_eq]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [show Fin.castSucc (FlatAffinePowerTower.multiplier (n := arity F u) t r) = multiplier F row u r from
        congrFun hm r]
      rfl
    · rw [ite_eq_right hs]
      by_cases he : slot F row u = arity F u
      · have hj : i = FlatAffinePowerTower.rowEquiv (arity F u) (F.depth u) (t, Sum.inr 0) :=
          (source_index F row u h he).trans (FlatAffinePowerTower.multiplier_eq t 0).symm
        rw [ite_eq_left he, hj, rawSystem, FlatAffinePowerTower.system_row]
        have hc := current_cast F u t
        dsimp +instances only [FlatAffineFullSourcePositive.count, FlatAffineFullSourceTower.count, FlatAffineFullSourceTower.stageWidth, FlatAffineFullSourceTower.arity, FlatAffinePowerTower.Index] at hc ⊢
        simp only [FlatAffinePowerTower.row, Fin.cases_zero, rename_rename, hc]
        rfl
      · have hj : i = FlatAffinePowerTower.rowEquiv (arity F u) (F.depth u) (t, Sum.inr (height F row u).succ) :=
          (height_index F row u h (by omega)).trans (FlatAffinePowerTower.multiplier_eq t (height F row u).succ).symm
        rw [ite_eq_right he, hj, rawSystem, FlatAffinePowerTower.system_row]
        have ha : (height F row u) ∈ FlatAffineFullSourceTower.free F u (stage F row u) ↔
            FlatAffineFullSourceTower.active (levelRecord F row u) = true := by
          simp only [FlatAffineFullSourceTower.free, Finset.mem_filter, Finset.mem_univ, true_and]
          rfl
        by_cases hr : FlatAffineFullSourceTower.active (levelRecord F row u) = true
        · simp only [FlatAffinePowerTower.row, Fin.cases_succ]
          have hmapped := levelPolynomial_eq F u t (FlatAffineFullSourceTower.level F u t.val (height F row u))
          have hactual := actualLevel_eq F row u
          dsimp +instances only [FlatAffineFullSourcePositive.count, FlatAffineFullSourceTower.count, FlatAffineFullSourceTower.stageWidth, FlatAffineFullSourceTower.arity, FlatAffinePowerTower.Index] at hmapped hactual ⊢
          rw [ite_eq_left (ha.mpr hr), map_sub, hmapped, hactual]
          simp only [FlatAffineRowPolynomials.levelRow, hr, ite_true, FlatAffineRowPolynomials.currentHeight,
            FlatAffinePowerTower.height, AffineHeightPolynomial.polynomial, map_sum, map_mul, rename_C, rename_X]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [show Fin.castSucc (FlatAffinePowerTower.current (n := arity F u) t j) = current F row u j from
            congrFun (current_cast F u t) j]
          rfl
        · simp only [FlatAffinePowerTower.row, Fin.cases_succ]
          rw [ite_eq_right (fun hh => hr (ha.mp hh)), rename_X]
          simp only [FlatAffineRowPolynomials.levelRow, hr]
          exact congrArg X (congrFun (multiplier_cast F u t) (height F row u).succ)
  · have hi : row u = Fin.last (FlatAffineFullSourceTower.count F u) := by
      apply Fin.ext
      have H := (row u).isLt
      change index F row u < FlatAffineFullSourceTower.count F u + 1 at H
      change index F row u = FlatAffineFullSourceTower.count F u
      omega
    rw [hi, system, PositivePolynomialSystem.new_row]
    simp only [FlatAffinePowerRowReaders.polynomial, FlatAffineRowSourceReaders.old, h, ite_false]

theorem evaluator {F : Inputs} (h : F.Access)
    (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (hr : UnaryFn (fun u => (row u).val))
    {W : List Bool → ℕ} {target modulus : List Bool → List Bool}
    (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (FlatAffineFullSourcePositive.count F) W (fun u => system F u (row u)) target modulus) := by
  have E := FlatAffinePowerRowReaders.evaluator h row hr hW ht hm
  exact E.congr (congrArg (fun p => FixedWidthRowBits.value (FlatAffineFullSourcePositive.count F) W p target modulus)
    (funext (row_eq F row)).symm)

end LeanCanny.Encoding.FlatAffinePowerPositive
