/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralRelativeCharacteristicBounds
public import LeanCanny.Algebra.IntegralCoefficientBlocks
public import LeanCanny.Algebra.ScaledGradedReductionAnnihilator

/-! # Heights of actual relative actions and integer rescalings

Integer block powering bounds old multiplication-matrix entries of an
algebra-valued power. Zero padding and column shifts preserve that bound.
The relative characteristic polynomial keeps its original outer degree;
integer rescaling adds only a linear leading-coefficient height term.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralActionHeightBounds
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralRelativeCharacteristicBounds
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] {M L : ℕ}

theorem block_height (b : Module.Basis (Fin M) ℤ A) (T : Matrix (Fin L) (Fin L) A) (H : ℕ)
    (h : ∀ i j r t, (Algebra.leftMulMatrix b (T i j) r t).natAbs ≤ 2 ^ H) (i j : Fin (L * M)) :
    (IntegralCoefficientBlocks.blockHom b L T i j).natAbs ≤ 2 ^ H := by
  obtain ⟨p, rfl⟩ := (finProdFinEquiv : Fin L × Fin M ≃ Fin (L * M)).surjective i
  obtain ⟨q, rfl⟩ := (finProdFinEquiv : Fin L × Fin M ≃ Fin (L * M)).surjective j
  rw [IntegralCoefficientBlocks.block_entry]
  exact h p.1 q.1 p.2 q.2

theorem power_height (b : Module.Basis (Fin M) ℤ A) (T : Matrix (Fin L) (Fin L) A) (H e : ℕ)
    (h : ∀ i j r t, (Algebra.leftMulMatrix b (T i j) r t).natAbs ≤ 2 ^ H) (i j : Fin L) (r t : Fin M) :
    (Algebra.leftMulMatrix b ((T ^ e) i j) r t).natAbs ≤ 2 ^ (e * (H + (L * M).size)) := by
  rw [← IntegralCoefficientBlocks.block_power_entry b T e i j r t]
  exact IntegralParameterMatrixBounds.pow_height _ H (block_height b T H h) e _ _

theorem padded_height (b : Module.Basis (Fin M) ℤ A) (T : Matrix (Fin L) (Fin L) A)
    (normal : Fin L → Prop) (bound : ℕ) (shift : Fin L → Fin L) (H : ℕ)
    (h : ∀ i j r t, (Algebra.leftMulMatrix b (T i j) r t).natAbs ≤ 2 ^ H) (i j : Fin L) (r t : Fin M) :
    (Algebra.leftMulMatrix b (GradedReductionAnnihilator.paddedMatrix T normal bound shift i j) r t).natAbs ≤
      2 ^ ((bound + 1) * (H + (L * M).size)) := by
  unfold GradedReductionAnnihilator.paddedMatrix
  by_cases hj : normal j
  · rw [ite_eq_left hj]
    exact power_height b T H (bound + 1) h i (shift j) r t
  · rw [ite_eq_right hj, map_zero, Matrix.zero_apply, Int.natAbs_zero]
    exact Nat.zero_le _

theorem int_multiply_entry (b : Module.Basis (Fin M) ℤ A) (z : ℤ) (x : A) (r t : Fin M) :
    Algebra.leftMulMatrix b ((z : A) * x) r t = z * Algebra.leftMulMatrix b x r t := by
  rw [← zsmul_eq_mul, map_zsmul, Matrix.smul_apply, zsmul_eq_mul]
  simp only [Int.cast_id]

def scaledHeight (L M e H G : ℕ) : ℕ := characteristicHeight L M H + e * L * G

theorem scaledHeight_binary {L M e H G : List Bool → ℕ} (hL : BinaryFn L) (hM : BinaryFn M)
    (he : BinaryFn e) (hH : BinaryFn H) (hG : BinaryFn G) :
    BinaryFn (fun c => scaledHeight (L c) (M c) (e c) (H c) (G c)) :=
  (characteristicHeight_binary hL hM hH).add ((he.mul hL).mul hG)

theorem scaled_coefficient_height [Nontrivial A] (b : Module.Basis (Fin M) ℤ A)
    (T : Matrix (Fin L) (Fin L) A) (c : ℤ) (e H G : ℕ)
    (h : ∀ i j r t, (Algebra.leftMulMatrix b (T i j) r t).natAbs ≤ 2 ^ H)
    (hc : c.natAbs ≤ 2 ^ G) (k : ℕ) (r t : Fin M) :
    (Algebra.leftMulMatrix b ((ScaledGradedReductionAnnihilator.polynomial T (c : A) e).coeff k) r t).natAbs ≤
      2 ^ scaledHeight L M e H G := by
  rw [ScaledGradedReductionAnnihilator.coefficient]
  by_cases hk : k ≤ L
  · rw [← Int.cast_pow, mul_comm (T.charpoly.coeff k), int_multiply_entry, Int.natAbs_mul, Int.natAbs_pow]
    calc
      _ ≤ (2 ^ G) ^ (e * k) * 2 ^ characteristicHeight L M H :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hc _) (coefficient_height b T H h k r t)
      _ = 2 ^ (characteristicHeight L M H + e * k * G) := by rw [← pow_mul, ← pow_add]; congr 1; ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide)
        (Nat.add_le_add_left (Nat.mul_le_mul_right G (Nat.mul_le_mul_left e hk)) _)
  · have HD : T.charpoly.natDegree < k := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt HD, zero_mul, map_zero, Matrix.zero_apply, Int.natAbs_zero]
    exact Nat.zero_le _

def criticalHeight (L M bound H G : ℕ) : ℕ :=
  scaledHeight L M (bound + 1) ((bound + 1) * (H + (L * M).size)) G

theorem criticalHeight_binary {L M bound H G : List Bool → ℕ} (hL : BinaryFn L) (hM : BinaryFn M)
    (hb : BinaryFn bound) (hH : BinaryFn H) (hG : BinaryFn G) :
    BinaryFn (fun c => criticalHeight (L c) (M c) (bound c) (H c) (G c)) :=
  scaledHeight_binary hL hM (hb.add (BinaryFn.const 1))
    ((hb.add (BinaryFn.const 1)).mul (hH.add (hL.mul hM).size)) hG

theorem padded_annihilator_height [Nontrivial A] (b : Module.Basis (Fin M) ℤ A)
    (T : Matrix (Fin L) (Fin L) A) (normal : Fin L → Prop) (bound : ℕ) (shift : Fin L → Fin L)
    (c : ℤ) (H G : ℕ) (h : ∀ i j r t, (Algebra.leftMulMatrix b (T i j) r t).natAbs ≤ 2 ^ H)
    (hc : c.natAbs ≤ 2 ^ G) (k : ℕ) (r t : Fin M) :
    (Algebra.leftMulMatrix b ((ScaledGradedReductionAnnihilator.polynomial
      (GradedReductionAnnihilator.paddedMatrix T normal bound shift) (c : A) (bound + 1)).coeff k) r t).natAbs ≤
        2 ^ criticalHeight L M bound H G :=
  scaled_coefficient_height b _ c (bound + 1) _ G (padded_height b T normal bound shift H h) hc k r t

def criticalFactor (L M bound : ℕ) : ℕ :=
  L * (bound + 1) + L * ((bound + 1) * (L * M).size + M.size + L.size + 1)

theorem criticalFactor_binary {L M bound : List Bool → ℕ} (hL : BinaryFn L) (hM : BinaryFn M) (hb : BinaryFn bound) :
    BinaryFn (fun c => criticalFactor (L c) (M c) (bound c)) :=
  (hL.mul (hb.add (BinaryFn.const 1))).add
    (hL.mul (((((hb.add (BinaryFn.const 1)).mul (hL.mul hM).size).add hM.size).add hL.size).add (BinaryFn.const 1)))

theorem criticalHeight_linear_bound (L M bound H G : ℕ) :
    criticalHeight L M bound H G ≤ criticalFactor L M bound * (H + G + 1) := by
  let U := L * (bound + 1)
  let V := L * ((bound + 1) * (L * M).size + M.size + L.size + 1)
  have HE : criticalHeight L M bound H G = U * (H + G) + V := by
    unfold criticalHeight scaledHeight
    rw [characteristicHeight_linear]
    dsimp only [U, V]
    ring
  rw [HE]
  change U * (H + G) + V ≤ (U + V) * (H + G + 1)
  calc
    _ ≤ (U + V) * (H + G) + (U + V) := Nat.add_le_add
      (Nat.mul_le_mul_right _ (Nat.le_add_right U V)) (Nat.le_add_left V U)
    _ = _ := by ring

end LeanCanny.Algebra.IntegralActionHeightBounds
