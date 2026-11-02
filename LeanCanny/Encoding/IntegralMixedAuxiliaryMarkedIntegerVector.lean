/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerProperties
public import LeanCanny.Algebra.IntegralMixedSourceIntegerRealization
/-! # One prescribed marked root vector for the native integer bank

The x/u/v roots are hypotheses about these literal original polynomials.
All remaining root identities, including the four huge power leaves, are
proved here. Realization uses the whole vector at one joint tuple.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegerPolynomialSourceChoice
open IntegralMixedAuxiliaryParametricSlackSource (regularizationAt penaltyAt)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def values (n : List Bool → ℕ) (t : List Bool → Term) (R : List Bool → ℕ)
    (context : List Bool) (x : ℕ → ℝ) (u v : ℝ) (i : ℕ) : ℝ :=
  if i<number n context then x i else if i=number n context then u else if i=number n context+2 then v
  else if i=number n context+4 then (2 : ℝ)^R context
  else if i=number n context+5 then (2 : ℝ)^regularizationAt n t (R∘tail) (oldKey n t context)
  else if i=number n context+6 then (2 : ℝ)^beta n t (R∘tail) (oldKey n t context)
  else if i=number n context+7 then (2 : ℝ)^penaltyAt n t (R∘tail) (oldKey n t context)
  else 0

private theorem positive_power_root (E : ℕ) :
    (PowerIntegerPolynomial.polynomial False E).eval₂ (Int.castRingHom ℝ) ((2 : ℝ)^E)=0 := by
  rw [PowerIntegerPolynomial.root_iff]
  simp only [PowerIntegerPolynomial.value,ite_false,Int.cast_pow,Int.cast_ofNat]

theorem roots {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool → ℕ) (context : List Bool) (x : ℕ → ℝ) (u v : ℝ)
    (hx : ∀i<number n context,
      ((IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).polynomial
        (pair (candidate context) (BinaryNatCode.encode (number n context-i)))).eval₂ (Int.castRingHom ℝ) (x i)=0)
    (hu : ((IntegralMixedAuxiliaryParametricSlackSource.sphereSource hn ht ha (R∘tail)).polynomial
      (oldKey n t context)).eval₂ (Int.castRingHom ℝ) u=0)
    (hv : ((IntegralMixedAuxiliaryParametricSlackSource.regularSource hn ht ha (R∘tail)).polynomial
      (oldKey n t context)).eval₂ (Int.castRingHom ℝ) v=0) (i : ℕ) :
    ((source hn ht ha R).polynomial (pair context (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ)
      (values n t R context x u v i)=0 := by
  simp only [source,choose,reindex,Function.comp_apply,tag,coordinateQuery,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits,PowerIntegerPolynomial.source,IntegerPolynomialZeroRootSource.source,values]
  split_ifs with hi hs hr hR hL hB hK
  · exact hx i hi
  · exact hu
  · exact hv
  · exact positive_power_root _
  · exact positive_power_root _
  · exact positive_power_root _
  · exact positive_power_root _
  · simp only [Polynomial.eval₂_X]

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerSource
