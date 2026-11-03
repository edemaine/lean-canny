/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryOuterIntegerSource
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerVector
/-! # Correlated marked values plus the two prescribed outer cuts

Only the original marked-root premises are reused. Both additional coordinates
are uniquely prescribed signed powers; no independent sample is identified.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryOuterIntegerSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number original tag)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def values (n : List Bool→ℕ) (t : List Bool→Term) (R : List Bool→ℕ)
    (root : List Bool) (x : ℕ→ℝ) (u v : ℝ) (i : ℕ) : ℝ :=
  if i<number n root+8 then IntegralMixedAuxiliaryMarkedIntegerSource.values n t R root x u v i
  else if i=number n root+8 then (2:ℝ)^exponent n t R root
  else if i=number n root+9 then -((2:ℝ)^exponent n t R root) else 0

theorem values_before (n : List Bool→ℕ) (t : List Bool→Term) (R : List Bool→ℕ)
    (root : List Bool) (x : ℕ→ℝ) (u v : ℝ) (i : ℕ) (hi : i<number n root+8) :
    values n t R root x u v i=IntegralMixedAuxiliaryMarkedIntegerSource.values n t R root x u v i :=
  ite_eq_left hi

theorem positive_root {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (root : List Bool) :
    ((source hn ht ha R).polynomial (pair root (BinaryNatCode.encode (number n root+8)))).eval₂
      (Int.castRingHom ℝ) ((2:ℝ)^exponent n t R root)=0 := by
  rw [positive_polynomial hn ht ha R _ (by simp only [tag,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits])]
  rw [PowerIntegerPolynomial.root_iff]
  simp only [pairFst_pair,PowerIntegerPolynomial.value,ite_false,Int.cast_pow,Int.cast_ofNat]

theorem negative_root {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (root : List Bool) :
    ((source hn ht ha R).polynomial (pair root (BinaryNatCode.encode (number n root+9)))).eval₂
      (Int.castRingHom ℝ) (-((2:ℝ)^exponent n t R root))=0 := by
  rw [negative_polynomial hn ht ha R _ (by simp only [tag,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits])]
  rw [PowerIntegerPolynomial.root_iff]
  simp only [pairFst_pair,PowerIntegerPolynomial.value,ite_true,Int.cast_neg,Int.cast_pow,Int.cast_ofNat]

theorem roots {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool→ℕ) (root : List Bool) (x : ℕ→ℝ) (u v : ℝ)
    (hold : ∀i<number n root+8,((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).polynomial
      (pair root (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ)
        (IntegralMixedAuxiliaryMarkedIntegerSource.values n t R root x u v i)=0) :
    ∀i<number n root+10,((source hn ht ha R).polynomial (pair root (BinaryNatCode.encode i))).eval₂
      (Int.castRingHom ℝ) (values n t R root x u v i)=0 := by
  intro i hi
  by_cases hb : i<number n root+8
  · rw [agree_before hn ht ha R _ (by simpa only [tag,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using hb),values_before n t R root x u v i hb]
    exact hold i hb
  · have H : i=number n root+8 ∨ i=number n root+9 := by omega
    rcases H with rfl|rfl
    · rw [values,ite_eq_right (by omega),ite_eq_left rfl]
      exact positive_root hn ht ha R root
    · rw [values,ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left rfl]
      exact negative_root hn ht ha R root

theorem coordinate_lt (n : List Bool→ℕ) (t : List Bool→Term) (R : List Bool→ℕ)
    (root : List Bool) (w : Fin (number n root+4)→ℝ)
    (hw : (FermatCriticalHomogenization.polynomial
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root).low
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root).leading
      (IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root).degree).eval₂ (Int.castRingHom ℝ) w=0)
    (j : Fin (number n root+4)) : |w j|<(2:ℝ)^exponent n t R root := by
  rw [IntegralMixedAuxiliaryMarkedIntegerPlan.spatial,BoundedRegularLowCoefficient.readers_source_polynomial] at hw
  exact LeanCanny.Geometry.BoundedRegularCoordinateCutoff.coordinate_lt _ _ _ _ w hw j

end LeanCanny.Encoding.IntegralMixedAuxiliaryOuterIntegerSource
