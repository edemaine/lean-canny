/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedSlackMatrices
public import LeanCanny.Algebra.IntegralParameterMatrixBounds
public import LeanCanny.Algebra.IntegralFrozenConstantBounds
/-! # Original bank bounds control the two marked slack matrices -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedSlackMatrixBounds
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedClearedMatrixBits (family rank matrix Active)
open IntegralMixedFramedSlackMatrixBits
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem mul_bound (x y : ℤ) (H G : ℕ) (hx : x.natAbs≤2^H) (hy : y.natAbs≤2^G) :
    (x*y).natAbs≤2^(H+G) := by
  rw [Int.natAbs_mul,pow_add]
  exact Nat.mul_le_mul hx hy
private theorem pow_bound (x : ℤ) (H e : ℕ) (hx : x.natAbs≤2^H) : (x^e).natAbs≤2^(e*H) := by
  rw [Int.natAbs_pow]
  apply (Nat.pow_le_pow_left hx e).trans_eq
  rw [←pow_mul,Nat.mul_comm H e]
private theorem diagonal_bound {n : ℕ} (z : ℤ) (H : ℕ) (hz : z.natAbs≤2^H) (r t : Fin n) :
    ((z : Matrix (Fin n) (Fin n) ℤ) r t).natAbs≤2^H := by
  rw [Matrix.intCast_apply]
  split_ifs
  · simpa only [Int.cast_id] using hz
  · exact Nat.zero_le _
private theorem smul_bound {n : ℕ} (z : ℤ) (M : Matrix (Fin n) (Fin n) ℤ) (H G : ℕ)
    (hz : z.natAbs≤2^H) (hM : ∀ r t,(M r t).natAbs≤2^G) (r t : Fin n) :
    ((z • M) r t).natAbs≤2^(H+G) := by
  simpa only [Matrix.smul_apply,zsmul_eq_mul,Int.cast_id] using mul_bound z (M r t) H G hz (hM r t)

def baseHeight (m G : ℕ) := G+m*G
def powerSumHeight (n N e H : ℕ) := e*(H+N.size)+n.size
def sphereHeight (m n N G R : ℕ) := (2*(m*G)+2*R)+powerSumHeight n N 2 (baseHeight m G)+1
def regularDiagonalHeight (m G d L K : ℕ) := (L+d*(m*G)+K)+d*(m*G)+1
def regularHeight (m n N G d R L K : ℕ) :=
  (regularDiagonalHeight m G d L K+(L+powerSumHeight n N d (baseHeight m G))+1)+
    (L+(d/2)*(sphereHeight m n N G R+N.size))+1

theorem base_bound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (G : ℕ) (HG : ((family P D H).state key).bank.Bounds G) (i : ℕ)
    (r t : Fin (rank P D H key)) : (matrix P D H key i r t).natAbs≤2^baseHeight ((family P D H).birth key) G := by
  by_cases ha : Active P key
  · by_cases hi : i<(family P D H).birth key
    · rw [IntegralMixedFramedClearedMatrixBits.matrix_actual P D H key ha ⟨i,hi⟩]
      exact IntegralMixedBankCoordinatePolynomial.matrix_bound ((family P D H).state key) HG ⟨i,hi⟩ r t
    · rw [matrix,ite_eq_left ha]
      unfold IntegralMixedFramedOldHeightBankBits.sourceEntry
      rw [dite_eq_right (fun hv=>hi hv.1)]
      exact Nat.zero_le _
  · rw [matrix,ite_eq_right ha]
    exact Nat.zero_le _

theorem powerSum_bound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (G : ℕ) (HG : ((family P D H).state key).bank.Bounds G)
    (n e : List Bool → ℕ) (r t : Fin (rank P D H key)) :
    (IntegralMixedFramedClearedPowerSumBits.matrixSum P D H n e key r t).natAbs≤
      2^powerSumHeight (n key) (rank P D H key) (e key) (baseHeight ((family P D H).birth key) G) := by
  rw [IntegralMixedFramedClearedPowerSumBits.matrixSum,Matrix.sum_apply]
  calc
    _ ≤ ∑ i ∈ Finset.range (n key), ((matrix P D H key (n key-i)^e key) r t).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (n key), 2^(e key*(baseHeight ((family P D H).birth key) G+(rank P D H key).size)) := by
      apply Finset.sum_le_sum
      intro i _
      exact IntegralParameterMatrixBounds.pow_height (matrix P D H key (n key-i))
        (baseHeight ((family P D H).birth key) G) (base_bound P D H key G HG _) (e key) r t
    _ = n key*2^(e key*(baseHeight ((family P D H).birth key) G+(rank P D H key).size)) := by simp
    _ ≤ 2^(n key).size*2^(e key*(baseHeight ((family P D H).birth key) G+(rank P D H key).size)) :=
      Nat.mul_le_mul_right _ (Nat.lt_size_self (n key)).le
    _ = _ := by rw [←pow_add,powerSumHeight]; congr 1; omega

theorem common_bound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (G : ℕ) (HG : ((family P D H).state key).bank.Bounds G) :
    (commonAt P D H key).natAbs≤2^((family P D H).birth key*G) :=
  IntegralMixedBankCoordinatePolynomial.common_bound ((family P D H).state key) HG

theorem sphereCoefficient_bound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (G : ℕ) (HG : ((family P D H).state key).bank.Bounds G) (R : List Bool → ℕ) :
    (sphereCoefficient P D H R key).natAbs≤2^(2*((family P D H).birth key*G)+2*R key) := by
  have HR : ((2 : ℤ)^R key).natAbs≤2^R key := by simp only [Int.natAbs_pow]; exact le_rfl
  exact mul_bound _ _ _ _ (pow_bound _ _ 2 (common_bound P D H key G HG)) (pow_bound _ _ 2 HR)

theorem regularCoefficient_bound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (G : ℕ) (HG : ((family P D H).state key).bank.Bounds G) (d L K : List Bool → ℕ) :
    (regularCoefficient P D H d L K key).natAbs≤2^regularDiagonalHeight ((family P D H).birth key) G (d key) (L key) (K key) := by
  have HL : ((2 : ℤ)^L key).natAbs≤2^L key := by simp only [Int.natAbs_pow]; exact le_rfl
  have HK : ((2 : ℤ)^K key).natAbs≤2^K key := by simp only [Int.natAbs_pow]; exact le_rfl
  have HQ := pow_bound _ _ (d key) (common_bound P D H key G HG)
  exact IntegralFrozenConstantBounds.add_bound _ _ _ _ (mul_bound _ _ _ _ (mul_bound _ _ _ _ HL HQ) HK) HQ

theorem sphere_bound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (G : ℕ) (HG : ((family P D H).state key).bank.Bounds G) (n R : List Bool → ℕ)
    (r t : Fin (rank P D H key)) :
    (sphere P D H n R key r t).natAbs≤2^sphereHeight ((family P D H).birth key) (n key) (rank P D H key) G (R key) := by
  rw [sphere,Matrix.sub_apply]
  exact IntegralFrozenConstantBounds.subtract_bound _ _ _ _
    (diagonal_bound _ _ (sphereCoefficient_bound P D H key G HG R) r t)
    (powerSum_bound P D H key G HG n (fun _=>2) r t)

theorem regular_bound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (G : ℕ) (HG : ((family P D H).state key).bank.Bounds G) (n d R L K : List Bool → ℕ)
    (r t : Fin (rank P D H key)) :
    (regular P D H n d R L K key r t).natAbs≤2^regularHeight ((family P D H).birth key) (n key) (rank P D H key) G (d key) (R key) (L key) (K key) := by
  have HL : ((2 : ℤ)^L key).natAbs≤2^L key := by simp only [Int.natAbs_pow]; exact le_rfl
  have HS := smul_bound _ _ _ _ HL (powerSum_bound P D H key G HG n d) r t
  have HU := IntegralParameterMatrixBounds.pow_height (sphere P D H n R key)
    (sphereHeight ((family P D H).birth key) (n key) (rank P D H key) G (R key))
    (sphere_bound P D H key G HG n R) (d key/2)
  have HUP := smul_bound _ _ _ _ HL HU r t
  rw [regular,Matrix.sub_apply,Matrix.sub_apply]
  exact IntegralFrozenConstantBounds.subtract_bound _ _ _ _
    (IntegralFrozenConstantBounds.subtract_bound _ _ _ _
      (diagonal_bound _ _ (regularCoefficient_bound P D H key G HG d L K) r t) HS) HUP

theorem baseHeight_binary {m G : List Bool → ℕ} (hm : BinaryFn m) (hG : BinaryFn G) :
    BinaryFn (fun q=>baseHeight (m q) (G q)) := hG.add (hm.mul hG)
theorem powerSumHeight_binary {n N e H : List Bool → ℕ} (hn : BinaryFn n) (hN : BinaryFn N) (he : BinaryFn e) (hH : BinaryFn H) :
    BinaryFn (fun q=>powerSumHeight (n q) (N q) (e q) (H q)) := (he.mul (hH.add hN.size)).add hn.size

theorem sphereHeight_binary {m n N G R : List Bool → ℕ} (hm : BinaryFn m) (hn : BinaryFn n)
    (hN : BinaryFn N) (hG : BinaryFn G) (hR : BinaryFn R) :
    BinaryFn (fun q=>sphereHeight (m q) (n q) (N q) (G q) (R q)) :=
  ((((BinaryFn.const 2).mul (hm.mul hG)).add ((BinaryFn.const 2).mul hR)).add
    (powerSumHeight_binary hn hN (BinaryFn.const 2) (baseHeight_binary hm hG))).add (BinaryFn.const 1)
theorem regularDiagonalHeight_binary {m G d L K : List Bool → ℕ} (hm : BinaryFn m) (hG : BinaryFn G)
    (hd : BinaryFn d) (hL : BinaryFn L) (hK : BinaryFn K) :
    BinaryFn (fun q=>regularDiagonalHeight (m q) (G q) (d q) (L q) (K q)) :=
  (((hL.add (hd.mul (hm.mul hG))).add hK).add (hd.mul (hm.mul hG))).add (BinaryFn.const 1)
theorem regularHeight_binary {m n N G d R L K : List Bool → ℕ} (hm : BinaryFn m) (hn : BinaryFn n)
    (hN : BinaryFn N) (hG : BinaryFn G) (hd : BinaryFn d) (hR : BinaryFn R) (hL : BinaryFn L) (hK : BinaryFn K) :
    BinaryFn (fun q=>regularHeight (m q) (n q) (N q) (G q) (d q) (R q) (L q) (K q)) :=
  ((((regularDiagonalHeight_binary hm hG hd hL hK).add
    (hL.add (powerSumHeight_binary hn hN hd (baseHeight_binary hm hG)))).add (BinaryFn.const 1)).add
      (hL.add ((hd.div (BinaryFn.const 2)).mul ((sphereHeight_binary hm hn hN hG hR).add hN.size)))).add (BinaryFn.const 1)

theorem sphereScalar_bound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (G : ℕ) (HG : ((family P D H).state key).bank.Bounds G) :
    (commonAt P D H key^2).natAbs≤2^(2*((family P D H).birth key*G)) := pow_bound _ _ 2 (common_bound P D H key G HG)
theorem regularScalar_bound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (G : ℕ) (HG : ((family P D H).state key).bank.Bounds G) (d L : List Bool → ℕ) :
    ((2 : ℤ)^L key*commonAt P D H key^d key).natAbs≤2^(L key+d key*((family P D H).birth key*G)) :=
  mul_bound _ _ _ _ (by simp only [Int.natAbs_pow]; exact le_rfl) (pow_bound _ _ _ (common_bound P D H key G HG))

end LeanCanny.Algebra.IntegralMixedFramedSlackMatrixBounds
