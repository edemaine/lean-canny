/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableTests
public import LeanCanny.Algebra.DyadicSpecialization
public import LeanCanny.Algebra.ScaledSquarefree

/-! # Nonzero scalar clearing preserves primitive preparation

Integer denominator clearing changes a specialized polynomial by a nonzero
scalar. Its scaled squarefree output is associated to the symbolic squarefree
specialization. Separating-direction tests are invariant under those changes.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTable
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair
open scoped Classical BigOperators

theorem derivative_associated {K : Type*} [Field K] {p q : K[X]} (h : Associated p q) :
    Associated p.derivative q.derivative := by
  obtain ⟨u, hu⟩ := h
  refine ⟨u, ?_⟩
  have hd : (u : K[X]).derivative = 0 := by
    rw [eq_C_of_natDegree_eq_zero (natDegree_coe_units u), derivative_C]
  simpa only [derivative_mul, hd, mul_zero, add_zero] using congrArg derivative hu

theorem common_associated {K : Type*} [Field K] [DecidableEq K] {p q : K[X]} (h : Associated p q) :
    Associated (SquarefreePart.common p) (SquarefreePart.common q) := by
  have hd := derivative_associated h
  apply associated_of_dvd_dvd
  · exact EuclideanDomain.dvd_gcd
      ((EuclideanDomain.gcd_dvd_left p p.derivative).trans h.dvd)
      ((EuclideanDomain.gcd_dvd_right p p.derivative).trans hd.dvd)
  · exact EuclideanDomain.dvd_gcd
      ((EuclideanDomain.gcd_dvd_left q q.derivative).trans h.dvd')
      ((EuclideanDomain.gcd_dvd_right q q.derivative).trans hd.dvd')

theorem part_associated {K : Type*} [Field K] [DecidableEq K] {p q : K[X]}
    (hp : p ≠ 0) (h : Associated p q) : Associated (SquarefreePart.part p) (SquarefreePart.part q) := by
  have hq : q ≠ 0 := h.ne_zero_iff.mp hp
  exact Associated.of_mul_left (by rw [SquarefreePart.factorization p hp,
    SquarefreePart.factorization q hq]; exact h) (common_associated h) (SquarefreePart.common_ne_zero p hp)

theorem rootPairs_eq_of_associated {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p p' q q' : K[X]} (hp : Associated p p') (hq : Associated q q') :
    rootPairs (L := L) p q = rootPairs (L := L) p' q' := by
  simp only [rootPairs, rootsFinset, (associated_map_map (algebraMap K L) hp).roots_eq,
    (associated_map_map (algebraMap K L) hq).roots_eq]

theorem resultant_separable_iff_of_associated {K : Type*} [Field K]
    {p p' q q' : K[X]} (hp : Associated p p') (hq : Associated q q')
    (hps : p.Separable) (hqs : q.Separable) (c : ℕ) :
    (cannyResultant p q c).Separable ↔ (cannyResultant p' q' c).Separable := by
  rw [PrimitivePair.resultant_separable_iff (L := AlgebraicClosure K) p q c hps hqs
      (IsAlgClosed.splits _) (IsAlgClosed.splits _),
    PrimitivePair.resultant_separable_iff (L := AlgebraicClosure K) p' q' c (hp.separable hps) (hq.separable hqs)
      (IsAlgClosed.splits _) (IsAlgClosed.splits _), rootPairs_eq_of_associated hp hq]

theorem shiftFamily_C_mul {K : Type*} [CommRing K] (p : K[X]) (a : K) (c : ℕ) :
    shiftFamily (C a * p) c = C (C a) * shiftFamily p c := by
  simp only [shiftFamily, Polynomial.map_mul, Polynomial.map_C, mul_comp, C_comp]

theorem cannyResultant_C_mul {K : Type*} [Field K] (p q : K[X]) (a b : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (c : ℕ) :
    cannyResultant (C a * p) (C b * q) c =
      C (a ^ q.natDegree * b ^ p.natDegree) * cannyResultant p q c := by
  rw [cannyResultant, natDegree_C_mul ha, natDegree_C_mul hb,
    shiftFamily_C_mul, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.resultant_C_mul_left, Polynomial.resultant_C_mul_right]
  simp only [← Polynomial.C_pow, Polynomial.C_mul, mul_assoc, cannyResultant]

theorem resultant_associated {K : Type*} [Field K] {p p' q q' : K[X]}
    (hp : Associated p p') (hq : Associated q q') (c : ℕ) :
    Associated (cannyResultant p q c) (cannyResultant p' q' c) := by
  obtain ⟨u, hu⟩ := hp
  obtain ⟨v, hv⟩ := hq
  have heu : p' = C ((u : K[X]).coeff 0) * p := by
    rw [← hu, eq_C_of_natDegree_eq_zero (natDegree_coe_units u), mul_comm]
    simp
  have hev : q' = C ((v : K[X]).coeff 0) * q := by
    rw [← hv, eq_C_of_natDegree_eq_zero (natDegree_coe_units v), mul_comm]
    simp
  rw [heu, hev, cannyResultant_C_mul p q _ _ (coeff_coe_units_zero_ne_zero u) (coeff_coe_units_zero_ne_zero v)]
  exact (associated_unit_mul_left _ _ (isUnit_C.mpr (isUnit_iff_ne_zero.mpr
    (mul_ne_zero (pow_ne_zero _ (coeff_coe_units_zero_ne_zero u))
      (pow_ne_zero _ (coeff_coe_units_zero_ne_zero v)))))).symm

theorem node_associated {K : Type*} [Field K] (a a' : ℕ → K[X]) (c : ℕ → ℕ → ℕ)
    (ha : ∀ i, Associated (a i) (a' i)) (h i : ℕ) :
    Associated (node a c h i) (node a' c h i) := by
  induction h generalizing i with
  | zero => exact ha i
  | succ h ih => exact resultant_associated (ih (2 * i)) (ih (2 * i + 1)) (c h i)

noncomputable def clear (p : Polynomial Coefficient) (E s : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (p.natDegree + 1), monomial k (DyadicSpecialization.numerator (p.coeff k) E s)

theorem clear_coeff (p : Polynomial Coefficient) (E s k : ℕ) :
    (clear p E s).coeff k = DyadicSpecialization.numerator (p.coeff k) E s := by
  by_cases hk : k < p.natDegree + 1
  · simp [clear, coeff_monomial, hk]
  · have hz : p.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp [clear, coeff_monomial, hk, hz]

theorem clear_map (p : Polynomial Coefficient) (E s : ℕ)
    (hE : ∀ k, (p.coeff k).natDegree ≤ E) :
    (clear p E s).map (Int.castRingHom ℝ) =
      C ((2 : ℝ) ^ (s * E)) * p.map (scalarEvaluation (InfinitesimalSign.dyadic s)) := by
  ext k
  simp only [coeff_map, clear_coeff, coeff_C_mul]
  exact DyadicSpecialization.numerator_eval (p.coeff k) E s (hE k)

theorem clear_associated (p : Polynomial Coefficient) (E s : ℕ)
    (hE : ∀ k, (p.coeff k).natDegree ≤ E) :
    Associated ((clear p E s).map (Int.castRingHom ℝ))
      (p.map (scalarEvaluation (InfinitesimalSign.dyadic s))) := by
  rw [clear_map p E s hE]
  exact associated_unit_mul_left _ _ (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))))

theorem integer_squarefree_associated {L : Type*} [Field L] [CharZero L]
    (p : ℤ[X]) (hp : p ≠ 0) :
    Associated ((ScaledSquarefree.polynomial p).map (Int.castRingHom L))
      (SquarefreePart.part (p.map (Int.castRingHom L))) := by
  have h := associated_map_map (Rat.castHom L) (ScaledSquarefree.map_associated_part p hp)
  have hc : (Rat.castHom L).comp (Int.castRingHom ℚ) = Int.castRingHom L := by ext z; simp
  simpa only [SquarefreePart.part_map, Polynomial.map_map, hc] using h

theorem integer_gcd_degree_in_field {L : Type*} [Field L] [CharZero L] (p : ℤ[X]) :
    ScaledSquarefree.degree p = (SquarefreePart.common (p.map (Int.castRingHom L))).natDegree := by
  have hc : (Rat.castHom L).comp (Int.castRingHom ℚ) = Int.castRingHom L := by ext z; simp
  have hm : (SquarefreePart.common (p.map (Int.castRingHom ℚ))).map (Rat.castHom L) =
      SquarefreePart.common (p.map (Int.castRingHom L)) := by
    simp only [SquarefreePart.common, derivative_map]
    rw [← gcd_map, Polynomial.map_map, Polynomial.map_map, hc]
  have h := congrArg Polynomial.natDegree hm
  rw [natDegree_map_eq_of_injective (Rat.castHom L).injective] at h
  simpa only [ScaledSquarefree.degree, PolynomialGCDBits.degree, SquarefreePart.common,
    derivative_map] using h

theorem Budget.cleared_degree (B : Budget) (p : Polynomial Coefficient)
    (hp : B.Controls p) (s : ℕ) (hs : B.testExponent ≤ s) :
    (clear p B.innerDegree s).natDegree = p.natDegree := by
  have ha := clear_associated p B.innerDegree s hp.2.1
  have hd := PrincipalSubresultant.natDegree_eq_of_associated ha
  rw [natDegree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℝ) from Int.cast_injective)] at hd
  exact hd.trans (B.degree_map p hp _ (by unfold InfinitesimalSign.dyadic; positivity) (dyadic_antitone hs))

theorem Budget.cleared_gcd_degree (B : Budget) (p : Polynomial Coefficient)
    (hp : B.Controls p) (hn : p ≠ 0) (s : ℕ) (hs : B.testExponent ≤ s) :
    ScaledSquarefree.degree (clear p B.innerDegree s) = SymbolicScaledSquarefree.degree p := by
  have ha := common_associated (clear_associated p B.innerDegree s hp.2.1)
  exact (integer_gcd_degree_in_field (L := ℝ) _).trans
    ((PrincipalSubresultant.natDegree_eq_of_associated ha).trans
      (B.gcd_degree p hp hn _ (by unfold InfinitesimalSign.dyadic; positivity) (dyadic_antitone hs)))

theorem Budget.clear_ne_zero (B : Budget) (p : Polynomial Coefficient)
    (hp : B.Controls p) (hn : p ≠ 0) (s : ℕ) (hs : B.testExponent ≤ s) :
    clear p B.innerDegree s ≠ 0 := by
  have ha := clear_associated p B.innerDegree s hp.2.1
  have hmap : p.map (scalarEvaluation (InfinitesimalSign.dyadic s)) ≠ 0 := by
    intro hz
    have h := congrArg (fun q : ℝ[X] => q.coeff p.natDegree) hz
    rw [coeff_map, coeff_zero] at h
    exact (leadingCoeff_ne_zero.mpr hn) ((B.coefficient_zero_iff p hp _
      (by unfold InfinitesimalSign.dyadic; positivity) (dyadic_antitone hs) _).mp h)
  intro hz
  have hn' := ha.ne_zero_iff.mpr hmap
  rw [hz, Polynomial.map_zero] at hn'
  exact hn' rfl

theorem Budget.cleared_squarefree_associated (B : Budget) (p : Polynomial Coefficient)
    (hp : B.Controls p) (hn : p ≠ 0) (s : ℕ) (hs : B.testExponent ≤ s) :
    Associated ((ScaledSquarefree.polynomial (clear p B.innerDegree s)).map (Int.castRingHom ℝ))
      ((SymbolicScaledSquarefree.polynomial p).map (scalarEvaluation (InfinitesimalSign.dyadic s))) := by
  have hb : 0 < InfinitesimalSign.dyadic s := by unfold InfinitesimalSign.dyadic; positivity
  have he : InfinitesimalSign.dyadic s ≤ InfinitesimalSign.dyadic B.testExponent := dyadic_antitone hs
  have hpmap : p.map (scalarEvaluation (InfinitesimalSign.dyadic s)) ≠ 0 := by
    intro hz
    have hc := congrArg (fun q : ℝ[X] => q.coeff p.natDegree) hz
    rw [coeff_map, coeff_zero] at hc
    exact (leadingCoeff_ne_zero.mpr hn) ((B.coefficient_zero_iff p hp _ hb he _).mp hc)
  have ha := clear_associated p B.innerDegree s hp.2.1
  have hclear : clear p B.innerDegree s ≠ 0 := by
    intro hz
    have hmap := ha.ne_zero_iff.mpr hpmap
    rw [hz, Polynomial.map_zero] at hmap
    exact hmap rfl
  have hcontrols := small_controls p hn B.massExponent hp.2.2 _ hb
    (he.trans (dyadic_antitone (by
      unfold SymbolicScaledSquarefree.smallExponent Budget.testExponent
      exact Nat.add_le_add_right (Nat.add_le_add_left (gcdMassExponent_mono hp.1 le_rfl) _) _)))
  exact (integer_squarefree_associated _ hclear).trans
    ((part_associated (ha.ne_zero_iff.mpr hpmap) ha).trans
      (specialized_associated_part _ p hcontrols.1 hcontrols.2).symm)

end LeanCanny.Algebra.SymbolicFixedTable
