/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralParameterExtensionMatrix
public import LeanCanny.Algebra.MatrixProductSpace
public import LeanCanny.Algebra.ModularNegFP

/-! # Streamed normalization columns for integral parameter extensions

Each normalized coefficient matrix is the old coefficient matrix times a
binary power of the selected leading-coefficient matrix. One ordered product
computes a requested entry using only the original coefficient reader.
The matrices, powers, and final column are never materialized.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralNormalizationMatrixBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Family where
  width : List Bool → ℕ
  degree : List Bool → ℕ
  index : List Bool → ℕ
  modulus : List Bool → ℕ
  row : (c : List Bool) → Fin (width c)
  col : (c : List Bool) → Fin (width c)
  coefficient : (c : List Bool) → ℕ → Matrix (Fin (width c)) (Fin (width c)) (ZMod (modulus c))
  modulus_ne_zero : ∀ c, modulus c ≠ 0

noncomputable def Family.value (F : Family) (c : List Bool) : List Bool :=
  residueBits ((F.coefficient c (F.index c) *
    F.coefficient c (F.degree c) ^ (F.degree c - 1 - F.index c)) (F.row c) (F.col c))

attribute [local irreducible] Family.value MatrixProductBits.Family.value

structure Access (F : Family) where
  width : BinaryFn F.width
  degree : BinaryFn F.degree
  index : BinaryFn F.index
  modulus : BinaryFn F.modulus
  row : BinaryFn (fun c => (F.row c).val)
  col : BinaryFn (fun c => (F.col c).val)
  entry : List Bool → List Bool
  entry_eq : ∀ c k (i j : Fin (F.width c)),
    entry (LeanCanny.pair c (LeanCanny.pair (BinaryNatCode.encode k)
      (LeanCanny.pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
        residueBits (F.coefficient c k i j)

noncomputable def productFamily (F : Family) : MatrixProductBits.Family where
  width := F.width
  count c := F.degree c - 1 - F.index c + 1
  modulus := F.modulus
  row := F.row
  col := F.col
  factor c s := F.coefficient c (if s = 0 then F.index c else F.degree c)
  modulus_ne_zero := F.modulus_ne_zero

theorem constant_tail {R : Type*} [Semiring R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) (s e : ℕ) (hs : 0 < s) :
    MatrixProduct.product (fun k => if k = 0 then A else B) s e = B ^ e := by
  induction e generalizing s with
  | zero => simp only [MatrixProduct.product, pow_zero]
  | succ e ih =>
    rw [MatrixProduct.product, ite_eq_right (by omega), ih (s + 1) (by omega), pow_succ']

theorem product_value (F : Family) : (productFamily F).value = F.value := by
  funext c
  unfold MatrixProductBits.Family.value
  change residueBits (MatrixProduct.product
    (fun s => F.coefficient c (if s = 0 then F.index c else F.degree c)) 0
    (F.degree c - 1 - F.index c + 1) (F.row c) (F.col c)) = F.value c
  have HF : (fun s => F.coefficient c (if s = 0 then F.index c else F.degree c)) =
      (fun s => if s = 0 then F.coefficient c (F.index c) else F.coefficient c (F.degree c)) := by
    funext s
    split_ifs <;> rfl
  rw [HF, MatrixProduct.product, ite_eq_left rfl, Nat.zero_add, constant_tail _ _ 1 _ (by omega)]
  unfold Family.value
  rfl

def factorQuery (F : Family) (r : List Bool) : List Bool :=
  let c := LeanCanny.pairFst r
  let s := Nat.fromBitsLE (LeanCanny.pairFst (LeanCanny.pairSnd r))
  LeanCanny.pair c (LeanCanny.pair
    (BinaryNatCode.encode (if s = 0 then F.index c else F.degree c))
    (LeanCanny.pairSnd (LeanCanny.pairSnd r)))

theorem factorQuery_FP (F : Family) (a : Access F) : factorQuery F ∈ FP := by
  have hs : BinaryFn (fun r => Nat.fromBitsLE (LeanCanny.pairFst (LeanCanny.pairSnd r))) :=
    (BinaryFn.fromBits pairFst_mem_FP).comp pairSnd_mem_FP
  have hp := hs.eq (BinaryFn.const 0)
  have hk := BinaryFn.ite hp (a.index.comp pairFst_mem_FP) (a.degree.comp pairFst_mem_FP)
  exact mem_FP_pair pairFst_mem_FP
    (mem_FP_pair hk.bits_mem_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))

noncomputable def productAccess (F : Family) (a : Access F) : MatrixProductBits.Access (productFamily F) where
  width := a.width
  count := ((a.degree.sub (BinaryFn.const 1)).sub a.index).add (BinaryFn.const 1)
  modulus := a.modulus
  row := a.row
  col := a.col
  entry := a.entry ∘ factorQuery F
  entry_eq c s i j := by
    simpa only [Function.comp_apply, factorQuery, LeanCanny.pairFst_pair,
      LeanCanny.pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, productFamily] using
      a.entry_eq c (if s = 0 then F.index c else F.degree c) i j

theorem evaluator (F : Family) (a : Access F) (E : SpaceFunction a.entry) : SpaceFunction F.value :=
  (MatrixProductBits.evaluator (productFamily F) (productAccess F a)
    (E.precompose (factorQuery F) (factorQuery_FP F a))).congr (product_value F)

noncomputable def Family.negativeValue (F : Family) (c : List Bool) : List Bool :=
  residueBits (-((F.coefficient c (F.index c) *
    F.coefficient c (F.degree c) ^ (F.degree c - 1 - F.index c)) (F.row c) (F.col c)))

attribute [local irreducible] Family.negativeValue

def negateQuery (F : Family) (r : List Bool) : List Bool :=
  LeanCanny.pair (BinaryNatCode.encode (F.modulus (LeanCanny.pairFst r))) (LeanCanny.pairSnd r)

theorem negateQuery_FP (F : Family) (a : Access F) : negateQuery F ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP a.modulus.bits_mem_FP) pairSnd_mem_FP

theorem negative_evaluator (F : Family) (a : Access F) (E : SpaceFunction a.entry) :
    SpaceFunction F.negativeValue := by
  have H : SpaceFunction (ArithmeticBits.negate ∘ negateQuery F ∘ (fun c => LeanCanny.pair c (F.value c))) :=
    ((evaluator F a E).withInput.postcompose (negateQuery F) (negateQuery_FP F a)).postcompose
    ArithmeticBits.negate ArithmeticBits.negate_mem_FP
  apply H.congr
  funext c
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  simp only [Function.comp_apply, negateQuery, LeanCanny.pairFst_pair, LeanCanny.pairSnd_pair,
    Family.value, Family.negativeValue, ArithmeticBits.negate_residueBits]

theorem column_packet {A : Type*} [CommRing A] [Nontrivial A] {n d m : ℕ}
    (b : Module.Basis (Fin n) ℤ A) (p : Polynomial A) (i j : Fin d) (hj : j.val + 1 = d)
    (u v : Fin n) :
    residueBits (-(((Algebra.leftMulMatrix b (p.coeff i.val)).map (Int.castRingHom (ZMod m)) *
      (Algebra.leftMulMatrix b (p.coeff d)).map (Int.castRingHom (ZMod m)) ^ (d - 1 - i.val)) u v)) =
      residueBits ((Algebra.leftMulMatrix (IntegralParameterExtension.basis b p d)
        (AdjoinRoot.root _) (u, i) (v, j) : ℤ) : ZMod m) := by
  rw [IntegralParameterExtension.basis_root_matrix_of_coefficients]
  dsimp only [Prod.fst, Prod.snd]
  rw [ite_eq_right (by omega), ← Matrix.map_pow, ← Matrix.map_mul]
  simp only [Matrix.map_apply, Int.cast_neg]
  rfl

end LeanCanny.Algebra.IntegralNormalizationMatrixBits
