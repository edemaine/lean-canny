/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedRelativeScalar

/-! # Actual affine-expression and bank heights in mixed histories

A shared denominator costs the number of retained scalars times their
height. Integer affine syntax then controls the actual multiplication
entries of every frozen height. These bounds feed the existing relative
critical coefficient estimate and both actual mixed bank extensions.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHistory
open LeanCanny.Encoding LeanCanny.Computation IntegralHistorySampler UniformIntegralPrefix FixedWidthPolynomial
open scoped Classical

noncomputable def AffineExpr.height (m G : ℕ) : AffineExpr → ℕ
  | .constant c => m * G + c.natAbs.size
  | .reference _ => G + m * G
  | .add a b => max (a.height m G) (b.height m G) + 1
  | .scale c a => c.natAbs.size + a.height m G

def AffineExpr.nodes : AffineExpr → ℕ
  | .constant _ | .reference _ => 1
  | .add a b => a.nodes + b.nodes + 1
  | .scale _ a => a.nodes + 1

def AffineExpr.CoefficientsBound (C : ℕ) : AffineExpr → Prop
  | .constant c => c.natAbs.size ≤ C
  | .reference _ => True
  | .add a b => a.CoefficientsBound C ∧ b.CoefficientsBound C
  | .scale c a => c.natAbs.size ≤ C ∧ a.CoefficientsBound C

theorem AffineExpr.height_le (a : AffineExpr) (m G C : ℕ) (hC : a.CoefficientsBound C) :
    a.height m G ≤ a.nodes * ((m + 1) * G + C + 1) := by
  let T := (m + 1) * G + C + 1
  have HT : 1 ≤ T := by dsimp only [T]; omega
  have HC : C ≤ T := by dsimp only [T]; omega
  induction a with
  | constant c =>
    change m * G + c.natAbs.size ≤ 1 * T
    change c.natAbs.size ≤ C at hC
    dsimp only [T]
    nlinarith
  | reference _ =>
    change G + m * G ≤ 1 * T
    dsimp only [T]
    nlinarith
  | add a b ha hb =>
    have HA := ha hC.1
    have HB := hb hC.2
    have HM : max (a.height m G) (b.height m G) ≤ (a.nodes + b.nodes) * T := by
      apply max_le
      · exact HA.trans (Nat.mul_le_mul_right T (Nat.le_add_right _ _))
      · exact HB.trans (Nat.mul_le_mul_right T (Nat.le_add_left _ _))
    change max (a.height m G) (b.height m G) + 1 ≤ (a.nodes + b.nodes + 1) * T
    nlinarith
  | scale c a ha =>
    have HA := ha hC.2
    change a.height m G ≤ a.nodes * T at HA
    have HS := hC.1
    change c.natAbs.size + a.height m G ≤ (a.nodes + 1) * T
    nlinarith

theorem commonDenominator_height {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (G : ℕ) (HG : x.bank.Bounds G) :
    (commonDenominator x).natAbs ≤ 2 ^ (m * G) := by
  simpa only [commonDenominator, Finset.card_univ, Fintype.card_fin] using
    CommonIntegerDenominator.denominator_height Finset.univ x.bank.denominator G (fun i _ => HG.denominator i)

theorem expression_height {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (G : ℕ) (HG : x.bank.Bounds G) (a : AffineExpr)
    (r t : Fin (count m B)) :
    (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis (expression x a) r t).natAbs ≤ 2 ^ a.height m G := by
  induction a with
  | constant c =>
    have HC : ((commonDenominator x) * c).natAbs ≤ 2 ^ (m * G + c.natAbs.size) := by
      rw [Int.natAbs_mul, pow_add]
      exact Nat.mul_le_mul (commonDenominator_height x G HG) (Nat.lt_size_self _).le
    rw [expression, ← Int.cast_mul]
    exact IntegralHistoryCriticalBits.integer_entry_height _ _ _ HC r t
  | reference j =>
    simp only [expression]
    by_cases hj : j < m
    · rw [dite_eq_left hj]
      exact (CommonIntegerDenominator.numerator_height x.sampler.scalarPrefix.basis.finBasis Finset.univ
        x.bank.denominator x.bank.numerator G G (fun i _ => HG.denominator i) ⟨j, hj⟩
        (HG.numerator ⟨j, hj⟩) r t).trans_eq (by rw [Finset.card_univ, Fintype.card_fin]; rfl)
    · rw [dite_eq_right hj, map_zero, Matrix.zero_apply, Int.natAbs_zero]
      exact Nat.zero_le _
  | add a b ha hb =>
    rw [expression, map_add, Matrix.add_apply]
    apply (Int.natAbs_add_le _ _).trans
    apply (Nat.add_le_add ha hb).trans
    calc
      _ ≤ 2 ^ max (a.height m G) (b.height m G) + 2 ^ max (a.height m G) (b.height m G) :=
        Nat.add_le_add (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
          (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
      _ = 2 ^ (AffineExpr.add a b).height m G := by
        rw [AffineExpr.height, pow_succ]
        omega
  | scale c a ha =>
    rw [expression, IntegralActionHeightBounds.int_multiply_entry, Int.natAbs_mul]
    exact (Nat.mul_le_mul (Nat.lt_size_self c.natAbs).le ha).trans_eq (pow_add _ _ _).symm

noncomputable def retainedBudget {n : ℕ} (m G : ℕ) (r : CriticalRule n) : ℕ :=
  Finset.univ.sup (fun i => (r.heights i).height m G)

noncomputable def scaleBudget {n : ℕ} (r : CriticalRule n) : ℕ :=
  Finset.univ.sup (fun i => (r.scales i).natAbs.size)

noncomputable def familyBounds {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) (G C : ℕ) (HG : x.bank.Bounds G)
    (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2 ^ C) : IntegralHistoryCriticalBits.Bounds (family x hm r) where
  coefficientHeight _ := C
  retainedHeight _ := retainedBudget m G r
  scaleHeight _ := m * G + scaleBudget r
  leadingHeight _ := P.leading.natAbs.size
  coefficient _ := HC
  retained _ i u v := (expression_height x G HG (r.heights i) u v).trans
    (Nat.pow_le_pow_right (by decide) (Finset.le_sup (f := fun i => (r.heights i).height m G) (Finset.mem_univ i)))
  scale _ i := by
    change (commonDenominator x * r.scales i).natAbs ≤ _
    rw [Int.natAbs_mul, pow_add]
    exact Nat.mul_le_mul (commonDenominator_height x G HG)
      ((Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide)
        (Finset.le_sup (f := fun i => (r.scales i).natAbs.size) (Finset.mem_univ i))))
  leading _ := (Nat.lt_size_self _).le

noncomputable def criticalHeight {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) (G C : ℕ) (HG : x.bank.Bounds G)
    (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2 ^ C) :=
  IntegralHistoryCriticalBits.budget (family x hm r) (familyBounds x hm r G C HG HC) []

theorem criticalStep_bank_bounds {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) (G C : ℕ) (HG : x.bank.Bounds G)
    (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2 ^ C) :
    (criticalStep x hm r).bank.Bounds
      (max G (bankStepHeight (count m B) (2 ^ B) (criticalHeight x hm r G C HG HC))) := by
  let H := familyBounds x hm r G C HG HC
  have HP := IntegralHistoryCriticalBits.coefficient_height (family x hm r) H []
  exact x.bank.rootStep_bounds hm _ _ _ G _ HG HP
    (IntegralClearedCriticalLeadingBits.integer_height (IntegralHistoryCriticalBits.source (family x hm r)) [] _ HP)

theorem integerStep_bank_bounds {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (p : Polynomial ℤ) (hp : p ≠ 0) (hcap : p.natDegree ≤ 2 ^ B)
    (G C : ℕ) (HG : x.bank.Bounds G) (HC : ∀ k, (p.coeff k).natAbs ≤ 2 ^ C) :
    (integerStep x hm p hp hcap).bank.Bounds (max G (bankStepHeight (count m B) (2 ^ B) C)) := by
  apply x.bank.rootStep_bounds hm _ _ C G _ HG
  · intro k r t
    rw [Polynomial.coeff_map]
    exact IntegralHistoryCriticalBits.integer_entry_height _ _ _ (HC k) r t
  · exact HC p.natDegree

end LeanCanny.Algebra.IntegralMixedHistory
