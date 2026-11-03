/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
public import LeanCanny.Geometry.BoundedRegularCoordinateCutoff
/-! # Two original signed-power cutoff leaves extend the marked prelude

The old n+8 sources stay literal. Births n+8 and n+9 are X-2^E and
X+2^E, with E the actual regular-source coordinate-cutoff exponent.
No power integer or polynomial AST is expanded into a metadata word.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryOuterIntegerSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number original tag degreeBound)
open IntegerPolynomialSourceChoice
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def exponent (n : List Bool→ℕ) (t : List Bool→Term) (R : List Bool→ℕ) (context : List Bool) :=
  LeanCanny.Geometry.BoundedRegularCoordinateCutoff.exponent (number n context) (t (original context)).toData.size (R context)

theorem exponent_binary {n : List Bool→ℕ} {t : List Bool→Term} {R : List Bool→ℕ}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (hR : BinaryFn R) : BinaryFn (exponent n t R) :=
  LeanCanny.Geometry.BoundedRegularCoordinateCutoff.exponent_binary
    (IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn)
    (BinaryFn.ofUnary ((LeanCanny.Geometry.AuxiliaryCandidateRegularLift.allowance_unary ht).comp
      IntegralMixedAuxiliaryMarkedIntegerPlan.original_FP)) hR

noncomputable def source {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (R : List Bool→ℕ) :=
  choose (fun q=>tag q=number n (pairFst q)+8)
    (PowerIntegerPolynomial.source (fun _=>False) (exponent n t R∘pairFst))
    (choose (fun q=>tag q=number n (pairFst q)+9)
      (PowerIntegerPolynomial.source (fun _=>True) (exponent n t R∘pairFst))
      (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R))

theorem access {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool→ℕ} (hR : BinaryFn R) : IntegerPolynomialRootQueriesBits.Access (source hn ht ha R) := by
  have HI:BinaryFn tag:=BinaryFn.fromBits pairSnd_mem_FP
  have HN:BinaryFn (fun q=>number n (pairFst q)) := (BinaryFn.ofUnary (IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn)).comp pairFst_mem_FP
  have HE:BinaryFn (exponent n t R∘pairFst) := (exponent_binary hn ht hR).comp pairFst_mem_FP
  exact choose_access (HI.eq (HN.add (BinaryFn.const 8))) _ _
    (PowerIntegerPolynomial.access (FPPred.const False) HE)
    (choose_access (HI.eq (HN.add (BinaryFn.const 9))) _ _
      (PowerIntegerPolynomial.access (FPPred.const True) HE) (IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha hR))

private theorem power_nonzero (negative : Prop) (E : ℕ) : PowerIntegerPolynomial.polynomial negative E≠0 := by
  intro he
  have H:=PowerIntegerPolynomial.degree negative E
  rw [he,Polynomial.natDegree_zero] at H
  omega

theorem nonzero {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (q : List Bool) : (source hn ht ha R).polynomial q≠0 := by
  unfold source choose
  dsimp only
  split_ifs
  · exact power_nonzero _ _
  · exact power_nonzero _ _
  · exact IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R q

theorem degree_le {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (q : List Bool) : (source hn ht ha R).degree q≤degreeBound hn ht ha (pairFst q) := by
  have H1 : 1≤degreeBound hn ht ha (pairFst q) := by unfold degreeBound; omega
  unfold source choose
  dsimp only
  split_ifs
  · exact H1
  · exact H1
  · exact IntegralMixedAuxiliaryMarkedIntegerSource.degree_le hn ht ha R q

theorem agree_before {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (q : List Bool) (hi : tag q<number n (pairFst q)+8) :
    (source hn ht ha R).polynomial q=(IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).polynomial q := by
  simp only [source,choose]
  rw [ite_eq_right (by omega),ite_eq_right (by omega)]

theorem positive_polynomial {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (q : List Bool) (hi : tag q=number n (pairFst q)+8) :
    (source hn ht ha R).polynomial q=PowerIntegerPolynomial.polynomial False (exponent n t R (pairFst q)) := by
  simp only [source,choose,hi,ite_true,Function.comp_apply,PowerIntegerPolynomial.source]

theorem negative_polynomial {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (q : List Bool) (hi : tag q=number n (pairFst q)+9) :
    (source hn ht ha R).polynomial q=PowerIntegerPolynomial.polynomial True (exponent n t R (pairFst q)) := by
  simp only [source,choose]
  rw [ite_eq_right (by omega),ite_eq_left hi]
  rfl

end LeanCanny.Encoding.IntegralMixedAuxiliaryOuterIntegerSource
