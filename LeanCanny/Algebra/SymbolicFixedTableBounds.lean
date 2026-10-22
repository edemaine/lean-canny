/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicBalancedBounds
public import LeanCanny.Algebra.ResultantBounds

/-! # Bounds independent of symbolic primitive-tree choices

Every direction in the prescribed search interval satisfies the same bounds,
including unsuccessful directions. The resulting reference exponent depends
only on source bounds and tree depth, rather than a chosen symbolic table.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTable
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair
open scoped Classical BigOperators
attribute [local irreducible] Matrix.det

structure Budget where
  degree : ℕ
  innerDegree : ℕ
  massExponent : ℕ

def Budget.Controls (B : Budget) (p : Polynomial Coefficient) : Prop :=
  p.natDegree ≤ B.degree ∧
    (∀ k, (p.coeff k).natDegree ≤ B.innerDegree) ∧
    ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ B.massExponent

theorem gcdMassExponent_mono {D D' b b' : ℕ} (hD : D ≤ D') (hb : b ≤ b') :
    gcdMassExponent D b ≤ gcdMassExponent D' b' := by
  unfold gcdMassExponent
  exact Nat.add_le_add
    (Nat.mul_le_mul (Nat.size_le_size (Nat.mul_le_mul_left _ hD)) (Nat.mul_le_mul_left _ hD))
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ hD) (Nat.add_le_add hb (Nat.size_le_size hD)))

theorem squarefreeMassExponent_mono {D D' b b' : ℕ} (hD : D ≤ D') (hb : b ≤ b') :
    SymbolicScaledSquarefree.massExponent D b ≤ SymbolicScaledSquarefree.massExponent D' b' := by
  unfold SymbolicScaledSquarefree.massExponent
  exact Nat.add_le_add
    (Nat.mul_le_mul (Nat.size_le_size (Nat.add_le_add_right hD _)) (Nat.add_le_add_right hD _))
    (Nat.mul_le_mul (Nat.add_le_add_right hD _) (Nat.add_le_add (gcdMassExponent_mono hD hb) hb))

theorem shiftExponent_mono {D D' c c' b b' : ℕ}
    (hD : D ≤ D') (hc : c ≤ c') (hb : b ≤ b') :
    shiftExponent D c b ≤ shiftExponent D' c' b' := by
  unfold shiftExponent
  exact Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (Nat.size_le_size (Nat.add_le_add_right hD _)) hD) hb)
    (Nat.mul_le_mul (Nat.size_le_size (Nat.add_le_add_right hc _)) hD)

theorem resultantMassExponent_mono {m m' n n' c c' bp bp' bq bq' : ℕ}
    (hm : m ≤ m') (hn : n ≤ n') (hc : c ≤ c') (hp : bp ≤ bp') (hq : bq ≤ bq') :
    resultantMassExponent m n c bp bq ≤ resultantMassExponent m' n' c' bp' bq' := by
  unfold resultantMassExponent
  exact Nat.add_le_add
    (Nat.mul_le_mul (Nat.size_le_size (Nat.add_le_add hm hn)) (Nat.add_le_add hm hn))
    (Nat.mul_le_mul (Nat.add_le_add hm hn) (Nat.add_le_add (shiftExponent_mono hm hc hp) hq))

def Budget.squarefree (B : Budget) : Budget where
  degree := B.degree
  innerDegree := (B.degree + 1) * ((2 * B.degree + 1) * B.innerDegree)
  massExponent := SymbolicScaledSquarefree.massExponent B.degree B.massExponent

theorem Budget.squarefree_controls (B : Budget) (p : Polynomial Coefficient) (hp : B.Controls p) :
    B.squarefree.Controls (SymbolicScaledSquarefree.polynomial p) := by
  refine ⟨(polynomial_natDegree_le p).trans hp.1, ?_, ?_⟩
  · intro k
    exact (polynomial_inner_degree p _ hp.2.1 k).trans
      (Nat.mul_le_mul (Nat.add_le_add_right hp.1 _)
        (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ hp.1) _)))
  · intro k
    exact (polynomial_coefficient_mass p _ hp.2.2 k).trans
      (Nat.pow_le_pow_right (by decide) (squarefreeMassExponent_mono hp.1 le_rfl))

def Budget.directionLimit (B : Budget) : ℕ := (B.degree * B.degree) ^ 2

def Budget.pair (B : Budget) : Budget where
  degree := B.degree * B.degree
  innerDegree := (B.degree + B.degree) * (B.innerDegree + B.innerDegree)
  massExponent := resultantMassExponent B.degree B.degree B.directionLimit B.massExponent B.massExponent

theorem Budget.pair_controls (B : Budget) (p q : Polynomial Coefficient) (c : ℕ)
    (hp : B.Controls p) (hq : B.Controls q) (hc : c ≤ B.directionLimit) :
    B.pair.Controls (cannyResultant p q c) := by
  refine ⟨(cannyResultant_natDegree_le p q c).trans (Nat.mul_le_mul hp.1 hq.1), ?_, ?_⟩
  · intro k
    exact (resultant_inner_degree p q c _ _ hp.2.1 hq.2.1 k).trans
      (Nat.mul_le_mul_right _ (Nat.add_le_add hp.1 hq.1))
  · intro k
    exact ((NestedMass.coeff_le _ k).trans (resultant_mass p q c _ _ hp.2.2 hq.2.2)).trans
      (Nat.pow_le_pow_right (by decide) (resultantMassExponent_mono hp.1 hq.1 hc le_rfl le_rfl))

def treeBudget (B : Budget) : ℕ → Budget
  | 0 => B
  | h + 1 => (treeBudget B h).pair

noncomputable def node {R : Type*} [CommRing R] (a : ℕ → Polynomial R)
    (c : ℕ → ℕ → ℕ) : ℕ → ℕ → Polynomial R
  | 0, i => a i
  | h + 1, i => cannyResultant (node a c h (2 * i)) (node a c h (2 * i + 1)) (c h i)

def Admissible (B : Budget) (c : ℕ → ℕ → ℕ) : Prop :=
  ∀ h i, c h i ≤ (treeBudget B h).directionLimit

theorem node_controls (B : Budget) (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ)
    (ha : ∀ i, B.Controls (a i)) (hc : Admissible B c) (h i : ℕ) :
    (treeBudget B h).Controls (node a c h i) := by
  induction h generalizing i with
  | zero => exact ha i
  | succ h ih => exact Budget.pair_controls _ _ _ _ (ih (2 * i)) (ih (2 * i + 1)) (hc h i)

def Budget.testExponent (B : Budget) : ℕ := B.massExponent + gcdMassExponent B.degree B.massExponent + 1

def referenceExponent (B : Budget) (h : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (h + 1), (treeBudget B d).testExponent

theorem testExponent_le_reference (B : Budget) (h d : ℕ) (hd : d ≤ h) :
    (treeBudget B d).testExponent ≤ referenceExponent B h := by
  unfold referenceExponent
  exact Finset.single_le_sum (f := fun j => (treeBudget B j).testExponent)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : d < h + 1))

private theorem eval_ne_zero_of_small (q : ℤ[X]) (hq : q ≠ 0) (b s : ℕ)
    (hm : coefficientMass q ≤ 2 ^ b) (hs : b < s)
    (beta : ℝ) (hb : 0 < beta) (hbs : beta ≤ InfinitesimalSign.dyadic s) :
    scalarEvaluation beta q ≠ 0 := by
  have he := InfinitesimalSign.integer_sign_eval_le_dyadic q b s hm hs beta hb hbs
  intro hz
  change SignType.sign (scalarEvaluation beta q) = _ at he
  rw [hz, sign_zero] at he
  exact (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hq) (sign_eq_zero_iff.mp he.symm)

theorem zero_iff_of_mass (q : ℤ[X]) (b s : ℕ) (hm : coefficientMass q ≤ 2 ^ b)
    (hs : b < s) (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic s) :
    scalarEvaluation beta q = 0 ↔ q = 0 := by
  constructor
  · intro hz
    by_contra hn
    exact eval_ne_zero_of_small q hn b s hm hs beta hb he hz
  · intro hz
    rw [hz, map_zero]

theorem Budget.coefficient_zero_iff (B : Budget) (p : Polynomial Coefficient) (hp : B.Controls p)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic B.testExponent) (k : ℕ) :
    scalarEvaluation beta (p.coeff k) = 0 ↔ p.coeff k = 0 := by
  constructor
  · intro hz
    by_contra hn
    exact eval_ne_zero_of_small _ hn _ _ (hp.2.2 k) (by unfold Budget.testExponent; omega) beta hb he hz
  · intro hz
    rw [hz, map_zero]

theorem Budget.degree_map (B : Budget) (p : Polynomial Coefficient) (hp : B.Controls p)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic B.testExponent) :
    (p.map (scalarEvaluation beta)).natDegree = p.natDegree := by
  apply natDegree_map_eq_iff.mpr
  by_cases hz : p = 0
  · exact Or.inr (by rw [hz, natDegree_zero])
  · exact Or.inl (fun h => (leadingCoeff_ne_zero.mpr hz)
      ((B.coefficient_zero_iff p hp beta hb he p.natDegree).mp h))

theorem Budget.discriminant_zero_iff (B : Budget) (p : Polynomial Coefficient) (hp : B.Controls p)
    (beta : ℝ) (hb : 0 < beta) (he : beta ≤ InfinitesimalSign.dyadic B.testExponent) :
    scalarEvaluation beta (discriminant p) = 0 ↔ discriminant p = 0 := by
  constructor
  · intro hz
    by_contra hn
    apply eval_ne_zero_of_small _ hn (gcdMassExponent B.degree B.massExponent) B.testExponent
      ((discriminant_mass p _ hp.2.2).trans
        (Nat.pow_le_pow_right (by decide) (gcdMassExponent_mono hp.1 le_rfl)))
      (by unfold Budget.testExponent; omega) beta hb he hz
  · intro hz
    rw [hz, map_zero]

theorem node_degree_map (B : Budget) (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ)
    (ha : ∀ i, B.Controls (a i)) (hc : Admissible B c) (height h i : ℕ) (hh : h ≤ height)
    (beta : ℝ) (hb : 0 < beta)
    (he : beta ≤ InfinitesimalSign.dyadic (referenceExponent B height)) :
    ((node a c h i).map (scalarEvaluation beta)).natDegree = (node a c h i).natDegree := by
  exact Budget.degree_map _ _ (node_controls B a c ha hc h i) beta hb
    (he.trans (dyadic_antitone (testExponent_le_reference B height h hh)))

theorem node_discriminant_zero_iff (B : Budget) (a : ℕ → Polynomial Coefficient) (c : ℕ → ℕ → ℕ)
    (ha : ∀ i, B.Controls (a i)) (hc : Admissible B c) (height h i : ℕ) (hh : h ≤ height)
    (beta : ℝ) (hb : 0 < beta)
    (he : beta ≤ InfinitesimalSign.dyadic (referenceExponent B height)) :
    scalarEvaluation beta (discriminant (node a c h i)) = 0 ↔ discriminant (node a c h i) = 0 := by
  exact Budget.discriminant_zero_iff _ _ (node_controls B a c ha hc h i) beta hb
    (he.trans (dyadic_antitone (testExponent_le_reference B height h hh)))

end LeanCanny.Algebra.SymbolicFixedTable
