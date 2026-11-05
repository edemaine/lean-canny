/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.SymbolicRootCurveOrder
public import LeanCanny.Geometry.SquarefreeRootFamily
public import LeanCanny.Algebra.IntegerPolynomialOuterSign

/-! # Actual exceptional cuts preserving queries on moving real roots

The cuts use the selected squarefree PSC of the head, each nonzero query,
and their products. Product-cover uniqueness preserves shared root branches;
queries identically zero need no exceptional factor.
-/

@[expose] public section
namespace LeanCanny.Geometry.ParameterizedRootQuerySign
open Set Polynomial LeanCanny.Algebra
open SymbolicScaledSquarefree (Coefficient scalarEvaluation exceptional)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def cuts {J : Type*} (p : Polynomial Coefficient) (Q : J → Polynomial Coefficient) :
    Option (J × Bool) → Coefficient
  | none => exceptional p
  | some (j, false) => if Q j = 0 then 1 else exceptional (Q j)
  | some (j, true) => if Q j = 0 then 1 else exceptional (p * Q j)

def Avoids {J : Type*} (p : Polynomial Coefficient) (Q : J → Polynomial Coefficient) (a b : ℝ) : Prop :=
  ∀ t ∈ Ioo a b, ∀ i, scalarEvaluation t (cuts p Q i) ≠ 0

theorem cuts_ne_zero {J : Type*} (p : Polynomial Coefficient) (hp : p ≠ 0)
    (Q : J → Polynomial Coefficient) (i : Option (J × Bool)) : cuts p Q i ≠ 0 := by
  cases i with
  | none => exact SymbolicScaledSquarefree.exceptional_ne_zero p hp
  | some i =>
    rcases i with ⟨j, side⟩
    cases side <;> simp only [cuts]
    · split_ifs with h
      · exact one_ne_zero
      · exact SymbolicScaledSquarefree.exceptional_ne_zero (Q j) h
    · split_ifs with h
      · exact one_ne_zero
      · exact SymbolicScaledSquarefree.exceptional_ne_zero (p * Q j) (mul_ne_zero hp h)

private theorem zero_iff_on_product (p q : Polynomial Coefficient) {a b : ℝ}
    (hq : ∀ t ∈ Ioo a b, scalarEvaluation t (exceptional q) ≠ 0)
    (hpq : ∀ t ∈ Ioo a b, scalarEvaluation t (exceptional (p * q)) ≠ 0)
    (f : C(Ioo a b, ℝ)) (hf : ∀ t, p.eval₂ (scalarEvaluation t.val) (f t) = 0)
    (s t : Ioo a b) : q.eval₂ (scalarEvaluation s.val) (f s) = 0 ↔
      q.eval₂ (scalarEvaluation t.val) (f t) = 0 := by
  have forward (u v : Ioo a b) (hu : q.eval₂ (scalarEvaluation u.val) (f u) = 0) :
      q.eval₂ (scalarEvaluation v.val) (f v) = 0 := by
    let F : C(Ioo a b, Fin 1 → ℝ) := ⟨fun z _ => f z, continuous_pi (fun _ => f.continuous)⟩
    let H := SymbolicUnivariateRootFamily.value (SymbolicScaledSquarefree.polynomial q)
    have hstart : H (u.val, F u) = 0 := by
      apply (SymbolicUnivariateRootFamily.roots_away q u.val (F u) (hq u.val u.property)).mp
      exact (SymbolicUnivariateRootFamily.value_zero_iff q u.val (F u)).mpr hu
    let i : RootBranches.Index H a b u := ⟨⟨⟨(u.val, F u), hstart⟩, u.property⟩, rfl⟩
    obtain ⟨curve, ha, hr, _⟩ := RootBranches.exists_anchored_branches_of_covering H a b u
      (SymbolicRootCurveOrder.covering q a b hq)
    let g := curve i
    have hg (z : Ioo a b) : q.eval₂ (scalarEvaluation z.val) (g z 0) = 0 := by
      apply (SymbolicUnivariateRootFamily.value_zero_iff q z.val (g z)).mp
      exact (SymbolicUnivariateRootFamily.roots_away q z.val (g z) (hq z.val z.property)).mpr (hr i z)
    have hanchor : g u = F u := ha i
    let P := SymbolicUnivariateRootFamily.value (SymbolicScaledSquarefree.polynomial (p * q))
    have hF (z : Ioo a b) : P (z.val, F z) = 0 := by
      apply (SymbolicUnivariateRootFamily.roots_away (p * q) z.val (F z) (hpq z.val z.property)).mp
      apply (SymbolicUnivariateRootFamily.value_zero_iff (p * q) z.val (F z)).mpr
      rw [Polynomial.eval₂_mul]
      change p.eval₂ (scalarEvaluation z.val) (f z) * q.eval₂ (scalarEvaluation z.val) (f z) = 0
      rw [hf z, zero_mul]
    have hG (z : Ioo a b) : P (z.val, g z) = 0 := by
      apply (SymbolicUnivariateRootFamily.roots_away (p * q) z.val (g z) (hpq z.val z.property)).mp
      apply (SymbolicUnivariateRootFamily.value_zero_iff (p * q) z.val (g z)).mpr
      rw [Polynomial.eval₂_mul, hg z, mul_zero]
    have he : F = g := RootBranches.curves_eq_of_anchor P
      (SymbolicRootCurveOrder.covering (p * q) a b hpq) F g hF hG u hanchor.symm
    have hv := congrArg (fun h : C(Ioo a b, Fin 1 → ℝ) => h v 0) he
    change f v = g v 0 at hv
    exact (congrArg (fun x : ℝ => q.eval₂ (scalarEvaluation v.val) x) hv).trans (hg v)
  exact ⟨forward s t, forward t s⟩

theorem root_path_zero_iff {J : Type*} (p : Polynomial Coefficient) (Q : J → Polynomial Coefficient)
    {a b : ℝ} (h : Avoids p Q a b) (f : C(Ioo a b, ℝ))
    (hf : ∀ t, p.eval₂ (scalarEvaluation t.val) (f t) = 0) (j : J) (s t : Ioo a b) :
    (Q j).eval₂ (scalarEvaluation s.val) (f s) = 0 ↔
      (Q j).eval₂ (scalarEvaluation t.val) (f t) = 0 := by
  by_cases hj : Q j = 0
  · simp only [hj, Polynomial.eval₂_zero]
  · apply zero_iff_on_product p (Q j) (fun z hz => ?_) (fun z hz => ?_) f hf s t
    · simpa only [cuts, ite_eq_right hj] using h z hz (some (j, false))
    · simpa only [cuts, ite_eq_right hj] using h z hz (some (j, true))

theorem root_path_sign {J : Type*} (p : Polynomial Coefficient) (Q : J → Polynomial Coefficient)
    {a b : ℝ} (h : Avoids p Q a b) (f : C(Ioo a b, ℝ))
    (hf : ∀ t, p.eval₂ (scalarEvaluation t.val) (f t) = 0) (j : J) (s t : Ioo a b) :
    SignType.sign ((Q j).eval₂ (scalarEvaluation s.val) (f s)) =
      SignType.sign ((Q j).eval₂ (scalarEvaluation t.val) (f t)) := by
  let : PreconnectedSpace (Ioo a b) := Subtype.preconnectedSpace isPreconnected_Ioo
  let F : Ioo a b → ℝ := fun z => (Q j).eval₂ (scalarEvaluation z.val) (f z)
  have hc : Continuous F := by
    apply ((AlgebraicBranchZero.continuous_evaluation (SquarefreeRootFamily.realPolynomial (Q j))).comp
      (continuous_subtype_val.prodMk f.continuous)).congr
    intro z
    exact SquarefreeRootFamily.eval_realPolynomial (Q j) z.val (f z)
  have hz (u v : Ioo a b) : F u = 0 ↔ F v = 0 := root_path_zero_iff p Q h f hf j u v
  have hs := AlgebraicBranchSign.sign_iff_of_zero_iff F hc hz s t
  change SignType.sign (F s) = SignType.sign (F t)
  rcases lt_trichotomy (F s) 0 with hn | he | hp
  · rw [sign_eq_neg_one_iff.mpr hn, sign_eq_neg_one_iff.mpr (hs.1.mp hn)]
  · rw [he, sign_zero, (hz s t).mp he, sign_zero]
  · rw [sign_eq_one_iff.mpr hp, sign_eq_one_iff.mpr (hs.2.mp hp)]

theorem avoids_after_mass {J : Type*} (p : Polynomial Coefficient) (hp : p ≠ 0)
    (Q : J → Polynomial Coefficient) (M : ℕ) (hM : ∀ i, coefficientMass (cuts p Q i) ≤ M)
    (a b : ℝ) (ha : (M : ℝ) + 1 ≤ a) : Avoids p Q a b := by
  intro t ht i
  apply IntegerPolynomialOuterSign.nonzero_after_mass (cuts p Q i) (cuts_ne_zero p hp Q i) t
  apply le_trans _ (ha.trans ht.1.le)
  exact_mod_cast Nat.add_le_add_right (hM i) 1

theorem root_path_sign_value (p : Polynomial Coefficient) {a b : ℝ}
    (h : Avoids p (fun _ : Unit => Polynomial.X) a b) (f : C(Ioo a b, ℝ))
    (hf : ∀ t, p.eval₂ (scalarEvaluation t.val) (f t) = 0) (s t : Ioo a b) :
    SignType.sign (f s) = SignType.sign (f t) := by
  simpa only [Polynomial.eval₂_X] using root_path_sign p (fun _ : Unit => Polynomial.X) h f hf () s t

theorem avoids_after_binary_mass {J : Type*} (p : Polynomial Coefficient) (hp : p ≠ 0)
    (Q : J → Polynomial Coefficient) (B : ℕ) (hB : ∀ i, coefficientMass (cuts p Q i) ≤ 2 ^ B)
    (a b : ℝ) (ha : (2 : ℝ) ^ (B + 1) ≤ a) : Avoids p Q a b := by
  apply avoids_after_mass p hp Q (2 ^ B) hB a b
  apply le_trans _ ha
  have H : 2 ^ B + 1 ≤ 2 ^ (B + 1) := by
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := B)
    omega
  exact_mod_cast H

end LeanCanny.Geometry.ParameterizedRootQuerySign
