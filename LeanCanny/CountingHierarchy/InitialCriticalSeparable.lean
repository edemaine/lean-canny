/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SeparatedCriticalValues
public import LeanCanny.CountingHierarchy.QuotientEvaluation
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Separable

/-! # Separability of the initial critical-value characteristic polynomial -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial Polynomial PurePowerResidue
open scoped Classical BigOperators

/-- Every initial critical point is obtained by multiplying the separated
 centers by a tuple of roots of unity. These `ell^n` points have distinct
 critical values, proving separability of the actual characteristic polynomial. -/
theorem initial_critical_charpoly_separable {n : ℕ} (ell : ℕ) (hell : 1 ≤ ell)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ ell) :
    (multiplicationMatrix hell
      (fun i : Fin n => MvPolynomial.C ((separatedCenters ell i : ℂ) ^ ell))
      (fun _ => by simpa only [totalDegree_C] using (show 0 < ell by omega))
      (potentialPolynomial ell (fun i => (separatedCenters ell i : ℂ)))).charpoly.Separable := by
  let a : Fin n → ℂ := fun i => (separatedCenters ell i : ℂ)
  let r : Fin n → MvPolynomial (Fin n) ℂ := fun i => MvPolynomial.C (a i ^ ell)
  let hr : ∀ i, (r i).totalDegree < ell := fun _ => by simpa only [r, totalDegree_C] using (show 0 < ell by omega)
  let v := potentialPolynomial ell a
  let q := (multiplicationMatrix hell r hr v).charpoly
  let z : NormalIndex n ell → Fin n → ℂ := fun b i => ζ ^ (b i).val
  let x : NormalIndex n ell → Fin n → ℂ := fun b i => a i * z b i
  let value : NormalIndex n ell → ℂ := fun b => MvPolynomial.eval (x b) v
  have hz (b : NormalIndex n ell) (i : Fin n) : z b i ^ ell = 1 := by
    dsimp only [z]
    rw [pow_right_comm, hζ.pow_eq_one, one_pow]
  have hinj : Function.Injective value := by
    intro b c hbc
    have hh : z b = z c := potential_at_separated_unity_injective ell hell _ _ (hz b) (hz c) hbc
    funext i
    exact Fin.ext (hζ.pow_inj (b i).isLt (c i).isLt (congrFun hh i))
  have hroot (b : NormalIndex n ell) : q.IsRoot (value b) := by
    have hx (i : Fin n) : MvPolynomial.aeval (x b) (r i) = x b i ^ ell := by
      simp only [r, x, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply, mul_pow, hz, mul_one]
    have hc := charpoly_eval_at_common_zero hell r hr v (x b) hx
    simpa only [Polynomial.IsRoot, Polynomial.coe_aeval_eq_eval, MvPolynomial.aeval_eq_eval,
      q, value] using hc
  have hq : q ≠ 0 := (multiplicationMatrix hell r hr v).charpoly_monic.ne_zero
  have hdegree : q.natDegree = ell ^ n := by
    rw [Matrix.charpoly_natDegree_eq_dim, card_normalIndex]
  let S := Finset.univ.image value
  have hScard : S.card = ell ^ n := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, card_normalIndex]
  have hsub : S ⊆ q.roots.toFinset := by
    intro y hy
    obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hy
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr (hroot b))
  have hge : ell ^ n ≤ q.roots.toFinset.card := by
    rw [← hScard]
    exact Finset.card_le_card hsub
  have hroots : q.roots.card ≤ ell ^ n := (Polynomial.card_roots' q).trans_eq hdegree
  have hnodup : q.roots.Nodup := by
    apply Multiset.toFinset_card_eq_card_iff_nodup.mp
    exact le_antisymm (Multiset.toFinset_card_le q.roots) (hroots.trans hge)
  exact (Polynomial.nodup_roots_iff_of_splits hq (IsAlgClosed.splits q)).mp hnodup

end LeanCanny.CountingHierarchy
