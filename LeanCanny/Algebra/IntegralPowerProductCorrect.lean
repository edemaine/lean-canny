/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralPowerProductSource

/-! # Actual algebra powers and ordered products behind native factor queries -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralPowerProductBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def ordered {A : Type*} [Monoid A] (a : ℕ → A) (s : ℕ) : ℕ → A
  | 0 => 1
  | n + 1 => a s * ordered a (s + 1) n

theorem ordered_finprod {A : Type*} [CommMonoid A] (a : ℕ → A) (s n : ℕ) :
    ordered a s n = ∏ i : Fin n, a (s + i.val) := by
  induction n generalizing s with
  | zero => simp only [ordered, Fin.prod_univ_zero]
  | succ n ih =>
    rw [ordered, ih, Fin.prod_univ_succ]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    omega

theorem map_ordered_matrix {A B : Type*} [Semiring A] [Semiring B] {M : ℕ}
    (f : A →+* Matrix (Fin M) (Fin M) B) (a : ℕ → A) (s n : ℕ) :
    f (ordered a s n) = MatrixProduct.product (fun i => f (a i)) s n := by
  induction n generalizing s with
  | zero => simp only [ordered, map_one, MatrixProduct.product]
  | succ n ih => rw [ordered, map_mul, ih, MatrixProduct.product]

theorem power_packet (F : Family) (c : List Bool) (s : ℕ) (r t : Fin (F.rank c)) :
    letI := F.ring c
    (powerFamily F).value (pair c (pair (BinaryNatCode.encode s)
      (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      residueBits ((Algebra.leftMulMatrix (F.basis c) (F.factor c s ^ F.exponent c s) r t : ℤ) : ZMod (F.modulus c)) := by
  let := F.ring c
  generalize hz : pair c (pair (BinaryNatCode.encode s)
    (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))) = q
  have hc : pairFst q = c := by rw [← hz, pairFst_pair]
  have hs : Nat.fromBitsLE (factorWord q) = s := by
    rw [factorWord, ← hz]
    simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hr : (oldIndex F rowWord q).val = r.val := by
    change Nat.fromBitsLE (rowWord q) % F.rank (pairFst q) = r.val
    rw [rowWord, ← hz]
    simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.mod_eq_of_lt r.isLt]
  have ht : (oldIndex F colWord q).val = t.val := by
    change Nat.fromBitsLE (colWord q) % F.rank (pairFst q) = t.val
    rw [colWord, ← hz]
    simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.mod_eq_of_lt t.isLt]
  subst c
  have HR : oldIndex F rowWord q = r := Fin.ext hr
  have HT : oldIndex F colWord q = t := Fin.ext ht
  rw [MatrixPower.ModularFamily.value]
  let T := Algebra.leftMulMatrix (F.basis (pairFst q)) (F.factor (pairFst q) (Nat.fromBitsLE (factorWord q)))
  change residueBits ((T.map (Int.castRingHom (ZMod (F.modulus (pairFst q)))) ^
    F.exponent (pairFst q) (Nat.fromBitsLE (factorWord q))) (oldIndex F rowWord q) (oldIndex F colWord q)) = _
  rw [← Matrix.map_pow, Matrix.map_apply]
  dsimp only [T]
  rw [← map_pow, hs, HR, HT]
  rfl

noncomputable def Family.value (F : Family) (c : List Bool) : List Bool := by
  letI := F.ring c
  exact residueBits ((Algebra.leftMulMatrix (F.basis c)
    (ordered (fun s => F.factor c s ^ F.exponent c s) 0 (F.count c)) (F.row c) (F.col c) : ℤ) : ZMod (F.modulus c))

noncomputable def productFamily (F : Family) : MatrixProductBits.Family where
  width := F.rank
  count := F.count
  modulus := F.modulus
  row := F.row
  col := F.col
  factor c s := by
    letI := F.ring c
    exact (Algebra.leftMulMatrix (F.basis c) (F.factor c s ^ F.exponent c s)).map (Int.castRingHom (ZMod (F.modulus c)))
  modulus_ne_zero := F.modulus_ne_zero

theorem product_value (F : Family) : (productFamily F).value = F.value := by
  funext c
  let := F.ring c
  let f : F.carrier c →+* Matrix (Fin (F.rank c)) (Fin (F.rank c)) (ZMod (F.modulus c)) :=
    (Int.castRingHom (ZMod (F.modulus c))).mapMatrix.comp (Algebra.leftMulMatrix (F.basis c)).toRingHom
  have HP := map_ordered_matrix f (fun s => F.factor c s ^ F.exponent c s) 0 (F.count c)
  change residueBits (MatrixProduct.product (fun s => f (F.factor c s ^ F.exponent c s))
    0 (F.count c) (F.row c) (F.col c)) = _
  rw [← HP]
  rfl

end LeanCanny.Algebra.IntegralPowerProductBits
