/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.IntegerGridValueCertificate
public import LeanCanny.Connectivity.PolynomialGridArcs
public import LeanCanny.Geometry.SymbolicUnivariateRootFamily

/-! # Original grid arcs with an explicit integer exceptional polynomial

Fixed Gram value certificates and squarefree coordinate factors construct one
nonzero integer polynomial excluding all changes in branch membership. Its
parameter degree is bounded by the coordinate and determinant degrees.
Original roots may be singular; coordinate roots may be repeated. Properness
and capture remain explicit inputs. Native readers are not asserted here.
-/

@[expose] public section
namespace LeanCanny.Connectivity.IntegerGridArcs
open Set Geometry LeanCanny.Algebra Polynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {κ : Type*} [Fintype κ]
abbrev Base := Polynomial ℤ

noncomputable def realRows (q : κ → MvPolynomial (Fin n) Base) :
    κ → MvPolynomial (Fin n) (Polynomial ℝ) :=
  fun k => (q k).map (Polynomial.mapRingHom (Int.castRingHom ℝ))

noncomputable def certificate (p : Fin n → Polynomial Base) (q : κ → MvPolynomial (Fin n) Base)
    (k : κ) : Polynomial Base := IntegerGridValueCertificate.polynomial p (q k)

noncomputable def exceptional (p : Fin n → Polynomial Base) (q : κ → MvPolynomial (Fin n) Base) : Base :=
  (∏ i, SymbolicScaledSquarefree.exceptional (p i)) * ∏ k, (certificate p q k).trailingCoeff

omit [Fintype κ] in
lemma real_value (q : κ → MvPolynomial (Fin n) Base) (t : ℝ) (x : Fin n → ℝ) (k : κ) :
    PolynomialGridValues.value (realRows q) (t, x) k =
      (q k).eval₂ (SymbolicScaledSquarefree.scalarEvaluation t) x := by
  change ((q k).map _).eval₂ (Polynomial.evalRingHom t) x = _
  rw [MvPolynomial.eval₂_map, SymbolicUnivariateRootFamily.evaluation_comp]

lemma trailing_realPolynomial (Q : Polynomial Base) :
    (SquarefreeRootFamily.realPolynomial Q).trailingCoeff =
      Q.trailingCoeff.map (Int.castRingHom ℝ) := by
  have hs := Polynomial.support_map_of_injective Q (f := Polynomial.mapRingHom (Int.castRingHom ℝ))
    (Polynomial.map_injective _ (Int.cast_injective (α := ℝ)))
  have hd : (SquarefreeRootFamily.realPolynomial Q).natTrailingDegree = Q.natTrailingDegree := by
    unfold SquarefreeRootFamily.realPolynomial Polynomial.natTrailingDegree Polynomial.trailingDegree
    rw [hs]
  rw [Polynomial.trailingCoeff, hd, SquarefreeRootFamily.realPolynomial, Polynomial.coeff_map]
  rfl

lemma exceptional_ne_zero (p : Fin n → Polynomial Base) (q : κ → MvPolynomial (Fin n) Base)
    (hp : ∀ i, 0 < (p i).natDegree) : exceptional p q ≠ 0 := by
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply SymbolicScaledSquarefree.exceptional_ne_zero
    exact Polynomial.ne_zero_of_natDegree_gt (hp i)
  · apply Finset.prod_ne_zero_iff.mpr
    intro k _
    exact Polynomial.trailingCoeff_ne_zero.mpr (IntegerGridValueCertificate.ne_zero p (q k) hp)

lemma exceptional_degree_le (p : Fin n → Polynomial Base) (q : κ → MvPolynomial (Fin n) Base)
    (E : ℕ) (hp : ∀ i k, ((p i).coeff k).natDegree ≤ E)
    (hq : ∀ k u, ((q k).coeff u).natDegree ≤ E) :
    (exceptional p q).natDegree ≤
      (∑ i, (2 * (p i).natDegree + 1) * E) +
        ∑ k, ProjectiveValueGram.dimension n (IntegerGridValueCertificate.width p (q k)) * E := by
  apply Polynomial.natDegree_mul_le.trans
  apply Nat.add_le_add
  · apply (Polynomial.natDegree_prod_le _ _).trans
    exact Finset.sum_le_sum (fun i _ => SymbolicScaledSquarefree.exceptional_degree (p i) E (hp i))
  · apply (Polynomial.natDegree_prod_le _ _).trans
    exact Finset.sum_le_sum (fun k _ => IntegerGridValueCertificate.parameter_degree_le p (q k) E hp (hq k) _)

lemma finite_exceptional (p : Fin n → Polynomial Base) (q : κ → MvPolynomial (Fin n) Base)
    (hp : ∀ i, 0 < (p i).natDegree) :
    {t : ℝ | SymbolicScaledSquarefree.scalarEvaluation t (exceptional p q) = 0}.Finite := by
  have hn : (exceptional p q).map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Int.cast_injective (α := ℝ))).mpr (exceptional_ne_zero p q hp)
  simpa only [Polynomial.IsRoot, Polynomial.eval_map, SymbolicScaledSquarefree.scalarEvaluation,
    Polynomial.coe_eval₂RingHom] using Polynomial.finite_setOfPred_isRoot hn

/-- Distinct exceptional parameters are bounded by the same source degree
bound, even when the exceptional polynomial has repeated factors. -/
lemma exceptional_root_count_le (p : Fin n → Polynomial Base) (q : κ → MvPolynomial (Fin n) Base)
    (E : ℕ) (hp : ∀ i k, ((p i).coeff k).natDegree ≤ E)
    (hq : ∀ k u, ((q k).coeff u).natDegree ≤ E) :
    ((exceptional p q).map (Int.castRingHom ℝ)).roots.toFinset.card ≤
      (∑ i, (2 * (p i).natDegree + 1) * E) +
        ∑ k, ProjectiveValueGram.dimension n (IntegerGridValueCertificate.width p (q k)) * E :=
  (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans
    (Polynomial.natDegree_map_le.trans (exceptional_degree_le p q E hp hq)))

/-- One actual original root labels each retained arc on every interval avoiding
roots of the explicit integer exceptional polynomial. No value certificate is an input. -/
theorem anchored_arcs (p : Fin n → Polynomial Base) (q : κ → MvPolynomial (Fin n) Base)
    (hp : ∀ i, 0 < (p i).natDegree)
    (hproper : IsProperMap (RootProjection.projection (SquarefreeRootFamily.value p)))
    (hcapture : ∀ t x, PolynomialGridValues.value (realRows q) (t, x) = 0 →
      SquarefreeRootFamily.value p (t, x) = 0)
    (a b : ℝ) (t₀ : Ioo a b)
    (havoid : ∀ t ∈ Ioo a b, SymbolicScaledSquarefree.scalarEvaluation t (exceptional p q) ≠ 0) :
    Finite (PolynomialGridArcs.Fiber (realRows q) t₀.val) ∧
    ∃ curve : PolynomialGridArcs.Fiber (realRows q) t₀.val → ℝ → Fin n → ℝ,
      (∀ j, curve j t₀.val = j.val) ∧
      (∀ j, ContinuousOn (curve j) (Icc a b)) ∧
      (∀ j t, t ∈ Icc a b → PolynomialGridValues.value (realRows q) (t, curve j t) = 0) ∧
      (∀ t : Ioo a b, ∀ x, PolynomialGridValues.value (realRows q) (t.val, x) = 0 ↔
        ∃! j, curve j t.val = x) ∧
      ∀ j, FrontierCover.Accessible ((fun t => (t, curve j t)) '' Ioo a b) := by
  have hsplit (t : ℝ) (ht : t ∈ Ioo a b) :
      (∀ i, SymbolicScaledSquarefree.scalarEvaluation t (SymbolicScaledSquarefree.exceptional (p i)) ≠ 0) ∧
      ∀ k, SymbolicScaledSquarefree.scalarEvaluation t (certificate p q k).trailingCoeff ≠ 0 := by
    have H := havoid t ht
    simp only [exceptional, map_mul, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
      Finset.mem_univ, forall_const] at H
    exact H
  apply PolynomialGridArcs.anchored_arcs_of_annihilators p
    (fun i => Polynomial.ne_zero_of_natDegree_gt (hp i)) (realRows q)
    (fun k => SquarefreeRootFamily.realPolynomial (certificate p q k)) ?_ hproper hcapture a b t₀
    (fun t ht => (hsplit t ht).1) ?_
  · intro t x hx k
    rw [SquarefreeRootFamily.eval_realPolynomial, real_value]
    exact IntegerGridValueCertificate.eval_eq_zero p (q k) _ x hx
  · intro k t ht
    rw [trailing_realPolynomial, Polynomial.eval_map]
    exact (hsplit t ht).2 k

end LeanCanny.Connectivity.IntegerGridArcs
