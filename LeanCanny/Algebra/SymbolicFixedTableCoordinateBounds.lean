/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableFinite

/-! # Uniform two-variable and mass bounds for every prepared coordinate

The coordinate envelope covers all admissible tables, not just the actual
successful table. Polynomial clearing at each path step stays within the
same fixed sixteenth-power recurrence used for parameter polynomials.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTable
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair
open SymbolicBalancedCoordinate (Coordinate)
open scoped Classical

structure CoordinateBounds (r : Coordinate) (T : ℕ) : Prop where
  degree : r.degree ≤ T
  numeratorInner : ∀ k, (r.numerator.coeff k).natDegree ≤ T
  denominatorInner : ∀ k, (r.denominator.coeff k).natDegree ≤ T
  numeratorMass : NestedMass.mass r.numerator ≤ 2 ^ T
  denominatorMass : NestedMass.mass r.denominator ≤ 2 ^ T

theorem CoordinateBounds.mono {r : Coordinate} {T U : ℕ} (h : CoordinateBounds r T) (hTU : T ≤ U) :
    CoordinateBounds r U :=
  ⟨h.degree.trans hTU, fun k => (h.numeratorInner k).trans hTU,
    fun k => (h.denominatorInner k).trans hTU,
    h.numeratorMass.trans (Nat.pow_le_pow_right (by decide) hTU),
    h.denominatorMass.trans (Nat.pow_le_pow_right (by decide) hTU)⟩

theorem coordinateMassExponent_mono {m m' n n' c c' bp bp' bq bq' : ℕ}
    (hm : m ≤ m') (hn : n ≤ n') (hc : c ≤ c') (hp : bp ≤ bp') (hq : bq ≤ bq') :
    coordinateMassExponent m n c bp bq ≤ coordinateMassExponent m' n' c' bp' bq' :=
  Nat.add_le_add (Nat.add_le_add (resultantMassExponent_mono hm hn hc hp hq) (shiftExponent_mono hm hc hp)) hq

theorem coordinateMassExponent_uniform (T : ℕ) (hT : 4 ≤ T) :
    coordinateMassExponent T T (T ^ 4) T T + (T ^ 4 + 1).size ≤ T ^ 12 := by
  have hr := resultantMassExponent_uniform T hT
  have hraw : coordinateMassExponent T T (T ^ 4) T T + (T ^ 4 + 1).size ≤
      T ^ 10 + T ^ 5 + T ^ 4 + 5 * T + 2 := by
    unfold coordinateMassExponent shiftExponent
    calc
      _ ≤ T ^ 10 + ((T + 1) + T + T + (T ^ 4 + 1) * T) + T + (T ^ 4 + 1) := by
        gcongr <;> exact Nat.size_le_self _
      _ = _ := by ring
  have h5 : T ^ 5 ≤ T ^ 10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h4 : T ^ 4 ≤ T ^ 10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h1 : T ≤ T ^ 10 := by simpa using Nat.pow_le_pow_right (n := T) (by omega) (show 1 ≤ 10 by decide)
  have h0 : 1 ≤ T ^ 10 := Nat.one_le_pow _ _ (by omega)
  exact (hraw.trans (by omega : T ^ 10 + T ^ 5 + T ^ 4 + 5 * T + 2 ≤ 16 * T ^ 10)).trans
    (CannyResultantBits.sixteen_mul_pow_le T 10 hT)

theorem pairCoordinate_bounds (B : Budget) (T : ℕ) (hT : 4 ≤ T) (hB : B.BoundedBy T)
    (p q : Polynomial Coefficient) (hp : B.Controls p) (hq : B.Controls q) (c : ℕ) (hc : c ≤ B.directionLimit)
    (right : Bool) : CoordinateBounds (pairCoordinate right p q c) (T ^ 12) := by
  have hpd := hp.1.trans hB.1
  have hqd := hq.1.trans hB.1
  have hE := hB.2.1
  have hcap : c ≤ T ^ 4 := hc.trans ((Nat.pow_le_pow_left (Nat.mul_le_mul hB.1 hB.1) 2).trans_eq (by ring))
  have hexp : coordinateMassExponent p.natDegree q.natDegree c B.massExponent B.massExponent + (c + 1).size ≤ T ^ 12 :=
    (Nat.add_le_add (coordinateMassExponent_mono hpd hqd hcap hB.2.2 hB.2.2)
      (Nat.size_le_size (Nat.add_le_add_right hcap _))).trans (coordinateMassExponent_uniform T hT)
  have hdegmax : max 1 ((q.natDegree - 1) * p.natDegree) ≤ T ^ 2 :=
    max_le (Nat.one_le_pow _ _ (by omega))
      ((Nat.mul_le_mul ((Nat.sub_le _ _).trans hqd) hpd).trans_eq (by ring))
  have hdeg : 1 + max 1 ((q.natDegree - 1) * p.natDegree) ≤ T ^ 12 := by
    have h0 : 1 ≤ T ^ 2 := Nat.one_le_pow _ _ (by omega)
    exact (by omega : 1 + max 1 ((q.natDegree - 1) * p.natDegree) ≤ 16 * T ^ 2).trans
      ((CannyResultantBits.sixteen_mul_pow_le T 2 hT).trans (Nat.pow_le_pow_right (by omega) (by decide)))
  have hinner : (p.natDegree + q.natDegree + 1) * (B.innerDegree + B.innerDegree) ≤ T ^ 12 := by
    have hi : (p.natDegree + q.natDegree + 1) * (B.innerDegree + B.innerDegree) ≤ 6 * T ^ 2 := by
      calc
        _ ≤ (3 * T) * (2 * T) := by gcongr <;> omega
        _ = _ := by ring
    exact hi.trans ((by omega : 6 * T ^ 2 ≤ 16 * T ^ 2).trans
      ((CannyResultantBits.sixteen_mul_pow_le T 2 hT).trans (Nat.pow_le_pow_right (by omega) (by decide))))
  have hd : (PrimitivePair.denominator p q c).natDegree ≤ T ^ 12 :=
    (PrimitivePair.denominator_degree p q c).trans (by omega)
  have hdi (k : ℕ) := (denominator_inner_degree p q c _ _ hp.2.1 hq.2.1 k).trans hinner
  have hdm := (denominator_mass p q c _ _ hp.2.2 hq.2.2).trans
    (Nat.pow_le_pow_right (by decide) (by omega : coordinateMassExponent p.natDegree q.natDegree c B.massExponent B.massExponent ≤ T ^ 12))
  cases right
  · exact ⟨max_le ((PrimitivePair.leftNumerator_degree p q c).trans hdeg) hd,
      fun k => (leftNumerator_inner_degree p q c _ _ hp.2.1 hq.2.1 k).trans hinner, hdi,
      (leftNumerator_mass p q c _ _ hp.2.2 hq.2.2).trans (Nat.pow_le_pow_right (by decide) hexp), hdm⟩
  · exact ⟨max_le ((PrimitivePair.rightNumerator_degree p q c).trans (by omega)) hd,
      fun k => (rightNumerator_inner_degree p q c _ _ hp.2.1 hq.2.1 k).trans hinner, hdi,
      (rightNumerator_mass p q c _ _ hp.2.2 hq.2.2).trans
        (Nat.pow_le_pow_right (by decide) (by omega)), hdm⟩

private theorem composition_exponent (T e : ℕ) (hT : 4 ≤ T) (he : e ≤ T) : T + e * T ^ 12 ≤ T ^ 16 := by
  have h1 : T ≤ T ^ 13 := by simpa using Nat.pow_le_pow_right (n := T) (by omega) (show 1 ≤ 13 by decide)
  have hm : e * T ^ 12 ≤ T ^ 13 := (Nat.mul_le_mul_right _ he).trans_eq (by ring)
  exact (by omega : T + e * T ^ 12 ≤ 16 * T ^ 13).trans
    ((CannyResultantBits.sixteen_mul_pow_le T 13 hT).trans (Nat.pow_le_pow_right (by omega) (by decide)))

theorem CoordinateBounds.comp {r s : Coordinate} {T : ℕ} (hT : 4 ≤ T)
    (hr : CoordinateBounds r T) (hs : CoordinateBounds s (T ^ 12)) : CoordinateBounds (r.comp s) (T ^ 16) := by
  have he := composition_exponent T r.degree hT hr.degree
  have hm := Coordinate.comp_mass r s T (T ^ 12) hr.numeratorMass hr.denominatorMass hs.numeratorMass hs.denominatorMass
  have hi := Coordinate.comp_inner_degree r s T (T ^ 12) hr.numeratorInner hr.denominatorInner hs.numeratorInner hs.denominatorInner
  refine ⟨(Coordinate.comp_degree r s).trans ((Nat.mul_le_mul hr.degree hs.degree).trans ?_),
    fun k => (hi k).1.trans he, fun k => (hi k).2.trans he,
    hm.1.trans (Nat.pow_le_pow_right (by decide) he), hm.2.trans (Nat.pow_le_pow_right (by decide) he)⟩
  exact (show T * T ^ 12 = T ^ 13 by ring).le.trans (Nat.pow_le_pow_right (by omega) (by decide))

theorem identity_bounds (T : ℕ) (hT : 1 ≤ T) : CoordinateBounds SymbolicBalancedCoordinate.identity T := by
  have h1 : coefficientMass (1 : ℤ[X]) = 1 := by
    simpa only [Polynomial.C_1, Int.natAbs_one] using coefficientMass_C (1 : ℤ)
  have hX : NestedMass.mass (X : Polynomial Coefficient) = 1 := by
    simpa only [monomial_one_one_eq_X, h1] using NestedMass.monomial 1 (1 : Coefficient)
  refine ⟨by simpa only [SymbolicBalancedCoordinate.identity, Coordinate.degree, natDegree_X,
    natDegree_one, max_eq_left (by decide : 0 ≤ 1)] using hT, ?_, ?_, ?_, ?_⟩
  · intro k
    simp only [SymbolicBalancedCoordinate.identity, coeff_X]
    split_ifs <;> simp
  · intro k
    simp only [SymbolicBalancedCoordinate.identity, coeff_one]
    split_ifs <;> simp
  · exact hX.le.trans (Nat.one_le_two_pow : 1 ≤ 2 ^ T)
  · change NestedMass.mass (Polynomial.C (1 : Coefficient)) ≤ _
    rw [NestedMass.C, h1]
    exact Nat.one_le_two_pow

theorem coordinate_uniform (B : Budget) (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ)
    (ha : ∀ i, B.Controls (a i)) (hc : Admissible B c) (T : ℕ) (hT : 4 ≤ T) (hB : B.BoundedBy T) (h i j : ℕ) :
    CoordinateBounds (coordinate a c h i j) (T ^ (16 ^ h)) := by
  induction h generalizing i j with
  | zero => simpa only [coordinate, pow_zero, pow_one] using identity_bounds T (by omega)
  | succ h ih =>
    have ht : T ≤ T ^ (16 ^ h) := by
      simpa only [pow_one] using Nat.pow_le_pow_right (n := T) (by omega) (Nat.one_le_pow h 16 (by decide))
    have hp (right : Bool) := pairCoordinate_bounds (treeBudget B h) _ (hT.trans ht) (treeBudget_bounded B T hT hB h)
      (node a c h (2 * i)) (node a c h (2 * i + 1)) (node_controls B a c ha hc h (2 * i))
      (node_controls B a c ha hc h (2 * i + 1)) (c h i) (hc h i) right
    by_cases hj : j < 2 ^ h
    · rw [coordinate, ite_eq_left hj]
      simpa only [← pow_mul, pow_succ (16 : ℕ) h] using (ih (2 * i) j).comp (hT.trans ht) (hp false)
    · rw [coordinate, ite_eq_right hj]
      simpa only [← pow_mul, pow_succ (16 : ℕ) h] using (ih (2 * i + 1) (j - 2 ^ h)).comp (hT.trans ht) (hp true)

end LeanCanny.Algebra.SymbolicFixedTable

namespace LeanCanny.Algebra.SymbolicFixedTableFinite.Family
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair SymbolicFixedTable
open scoped Classical

private def base (F : Family) : ℕ := F.budget.degree + 1 + F.budget.innerDegree + F.budget.massExponent + 4

private theorem base_four (F : Family) : 4 ≤ base F := by unfold base; omega

private theorem source_bounded (F : Family) : F.paddedBudget.BoundedBy (base F) := by
  unfold Budget.BoundedBy paddedBudget base
  dsimp only
  omega

private theorem base_le_pow (F : Family) : base F ≤ base F ^ 16 := by
  simpa only [pow_one] using Nat.pow_le_pow_right (n := base F) (by have := base_four F; omega) (show 1 ≤ 16 by decide)

private theorem envelope_le (F : Family) : (base F ^ 16) ^ (16 ^ F.count.size) ≤ F.exponent := by
  rw [exponent_eq]
  change _ ≤ base F ^ (65536 * (F.count + 1) ^ 4)
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by have := base_four F; omega)
  rw [show 16 * 16 ^ F.count.size = 16 ^ (F.count.size + 1) by rw [pow_succ]; omega]
  exact (FiniteAnnihilatorTree.heightExponent_le F.count).trans
    (Nat.mul_le_mul_right _ (by decide : 256 ≤ 65536))

theorem parameter_controls (F : Family) :
    (⟨F.exponent, F.exponent, F.exponent⟩ : Budget).Controls F.parameter := by
  have hc := node_controls F.paddedBudget.squarefree
    (fun i => SymbolicScaledSquarefree.polynomial (F.padded i)) F.directions
    (fun i => F.paddedBudget.squarefree_controls _ (F.padded_controls i))
    (F.reference.admissible _ F.padded_controls F.padded_nonzero) F.count.size 0
  have hb := treeBudget_bounded F.paddedBudget.squarefree (base F ^ 16)
    ((base_four F).trans (base_le_pow F))
    (F.paddedBudget.squarefree_bounded (base F) (base_four F) (source_bounded F)) F.count.size
  exact ⟨hc.1.trans (hb.1.trans (envelope_le F)),
    fun k => (hc.2.1 k).trans (hb.2.1.trans (envelope_le F)),
    fun k => (hc.2.2 k).trans (Nat.pow_le_pow_right (by decide) (hb.2.2.trans (envelope_le F)))⟩

theorem parameter_mass (F : Family) : NestedMass.mass F.parameter ≤ 2 ^ (2 * F.exponent + 1) := by
  exact (NestedMass.le_pow _ F.exponent F.exponent F.parameter_controls.1 F.parameter_controls.2.2).trans
    (Nat.pow_le_pow_right (by decide) (by have := Nat.size_le_self (F.exponent + 1); omega))

theorem parameter_ne_zero (F : Family) : F.parameter ≠ 0 := by
  exact (Polynomial.map_ne_zero_iff embedding_injective).mp
    ((F.reference.generic_separable F.padded F.padded_controls F.padded_nonzero F.count.size 0 le_rfl).ne_zero)

theorem coordinate_bounds (F : Family) (i : Fin F.count) : CoordinateBounds (F.coordinate i) F.exponent := by
  have hc := coordinate_uniform F.paddedBudget.squarefree
    (fun i => SymbolicScaledSquarefree.polynomial (F.padded i)) F.directions
    (fun i => F.paddedBudget.squarefree_controls _ (F.padded_controls i))
    (F.reference.admissible _ F.padded_controls F.padded_nonzero) (base F ^ 16)
    ((base_four F).trans (base_le_pow F))
    (F.paddedBudget.squarefree_bounded (base F) (base_four F) (source_bounded F)) F.count.size 0 i.val
  exact hc.mono (envelope_le F)

end LeanCanny.Algebra.SymbolicFixedTableFinite.Family
