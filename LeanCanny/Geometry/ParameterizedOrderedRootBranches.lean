/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.ParameterizedRootQuerySign

/-! # Complete ordered root branches preserving actual polynomial queries

The labels are the actual squarefree-covering fiber at the anchor. Every
original real root is retained once, including heads with repeated roots.
The zero polynomial is explicitly excluded by the constructed head cut.
-/

@[expose] public section
namespace LeanCanny.Geometry.ParameterizedOrderedRootBranches
open Set Polynomial LeanCanny.Algebra ParameterizedRootQuerySign
open SymbolicScaledSquarefree (Coefficient scalarEvaluation exceptional)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev Index (p : Polynomial Coefficient) (a b : ℝ) (s : Ioo a b) :=
  RootBranches.Index (SymbolicUnivariateRootFamily.value (SymbolicScaledSquarefree.polynomial p)) a b s

theorem zero_head_no_avoids {J : Type*} (Q : J → Polynomial Coefficient) {a b : ℝ} (s : Ioo a b) :
    ¬ Avoids 0 Q a b := by
  intro h
  have H := h s.val s.property none
  simp only [cuts, exceptional, Polynomial.leadingCoeff_zero, zero_mul, map_zero, ne_eq, not_true_eq_false] at H

theorem finite_index {J : Type*} (p : Polynomial Coefficient) (Q : J → Polynomial Coefficient)
    {a b : ℝ} (h : Avoids p Q a b) (s : Ioo a b) : Finite (Index p a b s) := by
  have hp : scalarEvaluation s.val (exceptional p) ≠ 0 := h s.val s.property none
  have hl := (SymbolicScaledSquarefree.exceptional_conditions (scalarEvaluation s.val) p hp).1
  have hpn : p.map (scalarEvaluation s.val) ≠ 0 := by
    intro he
    have hc := congrArg (fun q : Polynomial ℝ => q.coeff p.natDegree) he
    rw [Polynomial.coeff_map, Polynomial.coeff_natDegree, Polynomial.coeff_zero] at hc
    exact hl hc
  let : Finite {x : ℝ // (p.map (scalarEvaluation s.val)).IsRoot x} :=
    (Polynomial.finite_setOfPred_isRoot hpn).to_subtype
  have parameter (i : Index p a b s) : i.val.val.val.1 = s.val := congrArg Subtype.val i.property
  have root (i : Index p a b s) : p.eval₂ (scalarEvaluation s.val) (i.val.val.val.2 0) = 0 := by
    apply (SymbolicUnivariateRootFamily.value_zero_iff p s.val i.val.val.val.2).mp
    apply (SymbolicUnivariateRootFamily.roots_away p s.val i.val.val.val.2 hp).mpr
    rw [← parameter i]
    exact i.val.val.property
  let f : Index p a b s → {x : ℝ // (p.map (scalarEvaluation s.val)).IsRoot x} := fun i =>
    ⟨i.val.val.val.2 0, by simpa only [Polynomial.IsRoot, Polynomial.eval_map] using root i⟩
  apply Finite.of_injective f
  intro i j hij
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext ((parameter i).trans (parameter j).symm)
  funext k
  have hk : k = 0 := Subsingleton.elim _ _
  simpa only [hk] using congrArg Subtype.val hij

theorem exists_ordered_branches {J : Type*} (p : Polynomial Coefficient) (Q : J → Polynomial Coefficient)
    {a b : ℝ} (h : Avoids p Q a b) (s : Ioo a b) :
    ∃ curve : Index p a b s → C(Ioo a b, Fin 1 → ℝ),
      (∀ i, curve i s = i.val.val.val.2) ∧
      (∀ i t, p.eval₂ (scalarEvaluation t.val) (curve i t 0) = 0) ∧
      (∀ t : Ioo a b, ∀ x : Fin 1 → ℝ,
        p.eval₂ (scalarEvaluation t.val) (x 0) = 0 ↔ ∃! i, curve i t = x) ∧
      (∀ i j u v, curve i u 0 < curve j u 0 ↔ curve i v 0 < curve j v 0) ∧
      (∀ i j u v, SignType.sign ((Q j).eval₂ (scalarEvaluation u.val) (curve i u 0)) =
        SignType.sign ((Q j).eval₂ (scalarEvaluation v.val) (curve i v 0))) := by
  have hp (t : ℝ) (ht : t ∈ Ioo a b) : scalarEvaluation t (exceptional p) ≠ 0 := h t ht none
  obtain ⟨curve, ha, hr, hc⟩ := RootBranches.exists_anchored_branches_of_covering
    (SymbolicUnivariateRootFamily.value (SymbolicScaledSquarefree.polynomial p)) a b s
    (SymbolicRootCurveOrder.covering p a b hp)
  have roots (i : Index p a b s) (t : Ioo a b) :
      p.eval₂ (scalarEvaluation t.val) (curve i t 0) = 0 := by
    apply (SymbolicUnivariateRootFamily.value_zero_iff p t.val (curve i t)).mp
    exact (SymbolicUnivariateRootFamily.roots_away p t.val (curve i t) (hp t.val t.property)).mpr (hr i t)
  refine ⟨curve, ha, roots, ?_, ?_, ?_⟩
  · intro t x
    rw [← SymbolicUnivariateRootFamily.value_zero_iff p t.val x,
      SymbolicUnivariateRootFamily.roots_away p t.val x (hp t.val t.property)]
    exact hc t x
  · intro i j u v
    exact (SymbolicRootCurveOrder.coordinate_comparison_iff p hp (curve i) (curve j) 0
      (roots i) (roots j) u v).2
  · intro i j u v
    let f : C(Ioo a b, ℝ) := ⟨fun t => curve i t 0, (continuous_apply 0).comp (curve i).continuous⟩
    exact root_path_sign p Q h f (roots i) j u v

theorem exists_ordered_branches_after_mass {J : Type*}
    (p : Polynomial Coefficient) (hp : p ≠ 0) (Q : J → Polynomial Coefficient)
    (M : ℕ) (hM : ∀ i, coefficientMass (cuts p Q i) ≤ M) {a b : ℝ}
    (ha : (M : ℝ) + 1 ≤ a) (s : Ioo a b) :
    ∃ curve : Index p a b s → C(Ioo a b, Fin 1 → ℝ),
      (∀ i, curve i s = i.val.val.val.2) ∧
      (∀ i t, p.eval₂ (scalarEvaluation t.val) (curve i t 0) = 0) ∧
      (∀ t : Ioo a b, ∀ x : Fin 1 → ℝ,
        p.eval₂ (scalarEvaluation t.val) (x 0) = 0 ↔ ∃! i, curve i t = x) ∧
      (∀ i j u v, curve i u 0 < curve j u 0 ↔ curve i v 0 < curve j v 0) ∧
      (∀ i j u v, SignType.sign ((Q j).eval₂ (scalarEvaluation u.val) (curve i u 0)) =
        SignType.sign ((Q j).eval₂ (scalarEvaluation v.val) (curve i v 0))) :=
  exists_ordered_branches p Q (avoids_after_mass p hp Q M hM a b ha) s

/-- A common bound computed from the actual finite exceptional-polynomial family. -/
noncomputable def cutMass {J : Type*} [Fintype J]
    (p : Polynomial Coefficient) (Q : J → Polynomial Coefficient) : ℕ :=
  Finset.univ.sup (fun i => coefficientMass (cuts p Q i))

theorem avoids_after_cutMass {J : Type*} [Fintype J]
    (p : Polynomial Coefficient) (hp : p ≠ 0) (Q : J → Polynomial Coefficient)
    (a b : ℝ) (ha : (cutMass p Q : ℝ) + 1 ≤ a) : Avoids p Q a b := by
  apply avoids_after_mass p hp Q (cutMass p Q) (fun i => ?_) a b ha
  exact Finset.le_sup (f := fun k : Option (J × Bool) => coefficientMass (cuts p Q k)) (Finset.mem_univ i)

end LeanCanny.Geometry.ParameterizedOrderedRootBranches
