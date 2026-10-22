/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.GaloisDescent
public import Mathlib.FieldTheory.Perfect

/-!
# Algebraic univariate representation for two square-free polynomials

The Cartesian product of two root sets is stable under input-field automorphisms.
Descent therefore gives a monic separable primitive-coordinate polynomial of
degree `degree p₁ * degree p₂`, with coordinate polynomials over the input field.
The final theorem supplies its finite Galois ambient field as the splitting field
of `p₁ * p₂`. This is an existence theorem for the algebraic part of Canny's
Lemma 2.1, not its effective construction or polylogarithmic-space bound.
-/

@[expose] public section

namespace LeanCanny.Algebra

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

noncomputable def rootsFinset (p : Polynomial K) : Finset L := by
  classical
  exact (p.map (algebraMap K L)).roots.toFinset

noncomputable def rootPairs (p₁ p₂ : Polynomial K) : Finset (L × L) := by
  classical
  exact rootsFinset p₁ ×ˢ rootsFinset p₂

theorem mem_rootsFinset (p : Polynomial K) (hp : p ≠ 0) (x : L) :
    x ∈ rootsFinset p ↔ Polynomial.aeval x p = 0 := by
  classical
  simp only [rootsFinset, Multiset.mem_toFinset,
    Polynomial.mem_roots (Polynomial.map_ne_zero hp), Polynomial.IsRoot,
    Polynomial.eval_map_algebraMap]

theorem mem_rootPairs (p₁ p₂ : Polynomial K) (h₁ : p₁ ≠ 0) (h₂ : p₂ ≠ 0) (p : L × L) :
    p ∈ rootPairs p₁ p₂ ↔ Polynomial.aeval p.1 p₁ = 0 ∧ Polynomial.aeval p.2 p₂ = 0 := by
  classical
  simp only [rootPairs, Finset.mem_product, mem_rootsFinset _ h₁, mem_rootsFinset _ h₂]

theorem rootPairs_stable (p₁ p₂ : Polynomial K) (h₁ : p₁ ≠ 0) (h₂ : p₂ ≠ 0) :
    GaloisStable (K := K) (rootPairs (L := L) p₁ p₂) := by
  intro σ p hp
  obtain ⟨ha, hb⟩ := (mem_rootPairs p₁ p₂ h₁ h₂ p).mp hp
  apply (mem_rootPairs p₁ p₂ h₁ h₂ _).mpr
  simp only [actPoint, Polynomial.aeval_algHom_apply, ha, hb, map_zero, and_self]

theorem rootsFinset_card (p : Polynomial K) (hsep : p.Separable)
    (hsplit : (p.map (algebraMap K L)).Splits) : (rootsFinset (L := L) p).card = p.natDegree := by
  classical
  have hn := Polynomial.nodup_roots (hsep.map (f := algebraMap K L))
  rw [rootsFinset, Multiset.toFinset_card_of_nodup hn, ← hsplit.natDegree_eq_card_roots,
    Polynomial.natDegree_map]

theorem rootPairs_card (p₁ p₂ : Polynomial K) (h₁ : p₁.Separable) (h₂ : p₂.Separable)
    (hs₁ : (p₁.map (algebraMap K L)).Splits) (hs₂ : (p₂.map (algebraMap K L)).Splits) :
    (rootPairs (L := L) p₁ p₂).card = p₁.natDegree * p₂.natDegree := by
  classical
  rw [rootPairs, Finset.card_product, rootsFinset_card p₁ h₁ hs₁, rootsFinset_card p₂ h₂ hs₂]

section FiniteGalois
variable [FiniteDimensional K L] [IsGalois K L] [CharZero L]

/-- Over a common finite Galois splitting field, all pairs of roots have one
degree-bounded univariate representation over the original coefficient field. -/
theorem exists_primitive_coordinates (p₁ p₂ : Polynomial K) (h₁ : p₁.Separable) (h₂ : p₂.Separable)
    (hs₁ : (p₁.map (algebraMap K L)).Splits) (hs₂ : (p₂.map (algebraMap K L)).Splits) :
    ∃ (c : ℕ) (q r₁ r₂ : Polynomial K),
      c ≤ (p₁.natDegree * p₂.natDegree) ^ 2 ∧ q.Monic ∧ q.Separable ∧
      q.natDegree = p₁.natDegree * p₂.natDegree ∧
      r₁.degree < (p₁.natDegree * p₂.natDegree : WithBot ℕ) ∧
      r₂.degree < (p₁.natDegree * p₂.natDegree : WithBot ℕ) ∧
      (∀ θ : L, Polynomial.aeval θ q = 0 ↔ ∃ a b : L,
        Polynomial.aeval a p₁ = 0 ∧ Polynomial.aeval b p₂ = 0 ∧ θ = a + (c : L) * b) ∧
      ∀ a b : L, Polynomial.aeval a p₁ = 0 → Polynomial.aeval b p₂ = 0 →
        Polynomial.aeval (a + (c : L) * b) r₁ = a ∧ Polynomial.aeval (a + (c : L) * b) r₂ = b := by
  classical
  obtain ⟨c, q, r₁, r₂, hc, _, hmonic, hsep, hdegree, hdeg₁, hdeg₂, hroots, hcoords⟩ :=
    exists_univariate_coordinates_over_base (K := K) (L := L) (rootPairs (L := L) p₁ p₂)
      (rootPairs_stable p₁ p₂ h₁.ne_zero h₂.ne_zero)
  have hcard := rootPairs_card p₁ p₂ h₁ h₂ hs₁ hs₂
  rw [hcard] at hc hdegree hdeg₁ hdeg₂
  refine ⟨c, q, r₁, r₂, hc, hmonic, hsep, hdegree, hdeg₁, hdeg₂, ?_, ?_⟩
  · intro θ
    rw [hroots]
    constructor
    · rintro ⟨p, hp, hθ⟩
      obtain ⟨ha, hb⟩ := (mem_rootPairs p₁ p₂ h₁.ne_zero h₂.ne_zero p).mp hp
      exact ⟨p.1, p.2, ha, hb, hθ⟩
    · rintro ⟨a, b, ha, hb, hθ⟩
      exact ⟨(a, b), (mem_rootPairs p₁ p₂ h₁.ne_zero h₂.ne_zero _).mpr ⟨ha, hb⟩, hθ⟩
  · intro a b ha hb
    exact hcoords (a, b) ((mem_rootPairs p₁ p₂ h₁.ne_zero h₂.ne_zero _).mpr ⟨ha, hb⟩)

end FiniteGalois

/-- Algebraic existence in Canny's Lemma 2.1 for arbitrary square-free inputs
over a characteristic-zero field; a common finite Galois field is supplied. -/
theorem exists_primitive_coordinates_of_squarefree [CharZero K]
    (p₁ p₂ : Polynomial K) (h₁ : Squarefree p₁) (h₂ : Squarefree p₂) :
    let L := (p₁ * p₂).SplittingField
    ∃ (c : ℕ) (q r₁ r₂ : Polynomial K),
      c ≤ (p₁.natDegree * p₂.natDegree) ^ 2 ∧ q.Monic ∧ q.Separable ∧
      q.natDegree = p₁.natDegree * p₂.natDegree ∧
      r₁.degree < (p₁.natDegree * p₂.natDegree : WithBot ℕ) ∧
      r₂.degree < (p₁.natDegree * p₂.natDegree : WithBot ℕ) ∧
      (∀ θ : L, Polynomial.aeval θ q = 0 ↔ ∃ a b : L,
        Polynomial.aeval a p₁ = 0 ∧ Polynomial.aeval b p₂ = 0 ∧ θ = a + (c : L) * b) ∧
      ∀ a b : L, Polynomial.aeval a p₁ = 0 → Polynomial.aeval b p₂ = 0 →
        Polynomial.aeval (a + (c : L) * b) r₁ = a ∧ Polynomial.aeval (a + (c : L) * b) r₂ = b := by
  let L := (p₁ * p₂).SplittingField
  let : IsGalois K L := { to_isSeparable := inferInstance, to_normal := inferInstance }
  have hsep₁ : p₁.Separable := PerfectField.separable_iff_squarefree.mpr h₁
  have hsep₂ : p₂.Separable := PerfectField.separable_iff_squarefree.mpr h₂
  have hs : ((p₁ * p₂).map (algebraMap K L)).Splits := Polynomial.SplittingField.splits (p₁ * p₂)
  rw [Polynomial.map_mul] at hs
  have hs' := (Polynomial.splits_mul (Polynomial.map_ne_zero hsep₁.ne_zero)
    (Polynomial.map_ne_zero hsep₂.ne_zero)).mp hs
  exact exists_primitive_coordinates p₁ p₂ hsep₁ hsep₂ hs'.1 hs'.2

end LeanCanny.Algebra
