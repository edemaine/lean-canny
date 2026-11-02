/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerSource
/-! # Literal leaves and nonvanishing of the marked integer prelude -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegerPolynomialSourceChoice
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem reindex_nonzero (S : IntegerPolynomialRootQueriesBits.Source)
    (hS : ∀q,S.polynomial q≠0) (f : List Bool → List Bool) :
    ∀q,(reindex S f).polynomial q≠0 := fun q=>hS (f q)
private theorem choose_nonzero (p : List Bool → Prop) (S T : IntegerPolynomialRootQueriesBits.Source)
    (hS : ∀q,S.polynomial q≠0) (hT : ∀q,T.polynomial q≠0) :
    ∀q,(choose p S T).polynomial q≠0 := by
  intro q
  dsimp only [choose]
  split_ifs
  · exact hS q
  · exact hT q
private theorem power_nonzero (E : List Bool → ℕ) :
    ∀q,(PowerIntegerPolynomial.source (fun _=>False) E).polynomial q≠0 := by
  intro q H
  have HD := PowerIntegerPolynomial.degree False (E q)
  change (PowerIntegerPolynomial.polynomial False (E q)).natDegree=1 at HD
  change PowerIntegerPolynomial.polynomial False (E q)=0 at H
  rw [H,Polynomial.natDegree_zero] at HD
  omega

theorem nonzero {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool → ℕ) (q : List Bool) : (source hn ht ha R).polynomial q≠0 := by
  have HC : ∀z,(IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).polynomial z≠0 := by
    intro z
    exact IntegralMixedFramedCoordinateCharacteristicBits.nonzero _ _ _ _
  unfold source
  exact choose_nonzero _ _ _ (reindex_nonzero _ HC _)
    (choose_nonzero _ _ _ (reindex_nonzero _ (IntegralMixedAuxiliaryParametricSlackSource.sphere_nonzero hn ht ha _) _)
    (choose_nonzero _ _ _ (reindex_nonzero _ (IntegralMixedAuxiliaryParametricSlackSource.regular_nonzero hn ht ha _) _)
    (choose_nonzero _ _ _ (power_nonzero _)
    (choose_nonzero _ _ _ (power_nonzero _)
    (choose_nonzero _ _ _ (power_nonzero _)
    (choose_nonzero _ _ _ (power_nonzero _) (fun _=>Polynomial.X_ne_zero))))))) q

theorem coordinate_polynomial {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool → ℕ) (q : List Bool) (hi : tag q<number n (pairFst q)) :
    (source hn ht ha R).polynomial q=
      (IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).polynomial (coordinateQuery n q) := by
  simp only [source,choose,reindex,Function.comp_apply]
  rw [ite_eq_left hi]

theorem sphere_polynomial {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool → ℕ) (q : List Bool) (hi : tag q=number n (pairFst q)) :
    (source hn ht ha R).polynomial q=
      (IntegralMixedAuxiliaryParametricSlackSource.sphereSource hn ht ha (R∘tail)).polynomial (oldKey n t (pairFst q)) := by
  have HL : ¬tag q<number n (pairFst q) := by omega
  simp only [source,choose,reindex,Function.comp_apply]
  rw [ite_eq_right HL,ite_eq_left hi]

theorem regular_polynomial {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool → ℕ) (q : List Bool) (hi : tag q=number n (pairFst q)+2) :
    (source hn ht ha R).polynomial q=
      (IntegralMixedAuxiliaryParametricSlackSource.regularSource hn ht ha (R∘tail)).polynomial (oldKey n t (pairFst q)) := by
  have HL : ¬tag q<number n (pairFst q) := by omega
  have HE : ¬tag q=number n (pairFst q) := by omega
  simp only [source,choose,reindex,Function.comp_apply]
  rw [ite_eq_right HL,ite_eq_right HE,ite_eq_left hi]

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerSource
