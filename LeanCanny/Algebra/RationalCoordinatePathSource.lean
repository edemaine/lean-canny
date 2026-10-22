/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalCoordinatePathMatrix
public import LeanCanny.Algebra.MatrixProductSpace

/-! # The modular product problem computing a whole coordinate path

Coefficient width includes the requested output index and all clearing
exponents. Capping unused stage indices makes the entry interface total.
Neither a stage-degree promise nor a nonzero-denominator promise is needed
to compute the defined integer path polynomials.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalCoordinatePathBits
open Polynomial UnivariateRational
open LeanCanny.Encoding LeanCanny.Computation
open RationalSubstitution.IntegerBits (context selectedDegree mValue coefficientResidue)

structure Source where
  inner : List Bool → ℕ → Coordinate
  degree : List Bool → ℕ
  depth : List Bool → ℕ

noncomputable def Source.coordinate (F : Source) (c : List Bool) : Coordinate :=
  RationalCoordinatePath.path (F.degree c) (F.inner c) (F.depth c)

noncomputable def Source.component (F : Source) (numerator : Bool) (c : List Bool) : ℤ[X] :=
  if numerator then (F.coordinate c).numerator else (F.coordinate c).denominator

def width (F : Source) (q : List Bool) : ℕ :=
  (F.degree (context q) + 1) ^ F.depth (context q) + Nat.fromBitsLE (selectedDegree q) + 2

theorem width_gt_one (F : Source) (q : List Bool) : 1 < width F q := by unfold width; omega

theorem index_lt_width (F : Source) (q : List Bool) : Nat.fromBitsLE (selectedDegree q) < width F q := by unfold width; omega

theorem exponent_lt_width (F : Source) (q : List Bool) (s : ℕ) (hs : s ≤ F.depth (context q)) :
    F.degree (context q) ^ s < width F q := by
  have h1 : F.degree (context q) ^ s ≤ (F.degree (context q) + 1) ^ s :=
    Nat.pow_le_pow_left (Nat.le_succ (F.degree (context q))) s
  have h2 : (F.degree (context q) + 1) ^ s ≤ (F.degree (context q) + 1) ^ F.depth (context q) :=
    Nat.pow_le_pow_right (by omega : 1 ≤ F.degree (context q) + 1) hs
  unfold width
  omega

theorem width_binary (F : Source) (hD : BinaryFn F.degree) (hK : UnaryFn F.depth) : BinaryFn (width F) := by
  have hd : BinaryFn (F.degree ∘ context) := hD.comp RationalSubstitution.IntegerBits.context_mem_FP
  have hk : UnaryFn (F.depth ∘ context) := hK.comp RationalSubstitution.IntegerBits.context_mem_FP
  exact (((hd.add (BinaryFn.const 1)).powUnary hk).add (BinaryFn.fromBits RationalSubstitution.IntegerBits.selectedDegree_mem_FP)).add (BinaryFn.const 2)

noncomputable def factor (F : Source) (q : List Bool) (s : ℕ) : Matrix (Fin (width F q)) (Fin (width F q)) ℤ :=
  RationalCoordinatePath.matrices (width F q) (F.degree (context q)) (F.inner (context q)) (min s (F.depth (context q)))

noncomputable def productFamily (F : Source) (numerator : Bool) : MatrixProductBits.Family where
  width := width F
  count q := F.depth (context q)
  modulus := mValue
  row q := ⟨if numerator then 1 else 0, by have h := width_gt_one F q; cases numerator <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> omega⟩
  col q := ⟨Nat.fromBitsLE (selectedDegree q), index_lt_width F q⟩
  factor q s := (factor F q s).map (Int.castRingHom (ZMod (mValue q)))
  modulus_ne_zero q := by unfold mValue; omega

theorem value_eq (F : Source) (numerator : Bool) :
    (productFamily F numerator).value = PrimitivePairBits.coefficient (F.component numerator) := by
  funext q
  let c := context q
  let k := F.depth c
  let N := width F q
  let A := RationalCoordinatePath.matrices N (F.degree c) (F.inner c)
  have hN : 1 < N := width_gt_one F q
  have hj : Nat.fromBitsLE (selectedDegree q) < N := index_lt_width F q
  have H := RationalCoordinatePath.product_entries N (F.degree c) (F.inner c) k hN
    (fun s hs => exponent_lt_width F q s hs.le) (⟨Nat.fromBitsLE (selectedDegree q), hj⟩ : Fin N)
  have hcap : MatrixProduct.product (fun s => A (min s k)) 0 k = MatrixProduct.product A 0 k := by
    apply MatrixProduct.product_congr
    intro s hs
    simp only [Nat.zero_add, min_eq_left (by omega : s ≤ k)]
  cases numerator with
  | false =>
    change MatrixPower.residueBits (MatrixProduct.product
      (fun s => (A (min s k)).map (Int.castRingHom (ZMod (mValue q)))) 0 k
        (⟨0, by omega⟩ : Fin N) ⟨Nat.fromBitsLE (selectedDegree q), hj⟩) =
      coefficientResidue ((RationalCoordinatePath.path (F.degree c) (F.inner c) k).denominator.coeff
        (Nat.fromBitsLE (selectedDegree q))) (mValue q)
    rw [MatrixProduct.product_map, hcap]
    exact congrArg (fun z : ℤ => coefficientResidue z (mValue q)) H.2
  | true =>
    change MatrixPower.residueBits (MatrixProduct.product
      (fun s => (A (min s k)).map (Int.castRingHom (ZMod (mValue q)))) 0 k
        (⟨1, hN⟩ : Fin N) ⟨Nat.fromBitsLE (selectedDegree q), hj⟩) =
      coefficientResidue ((RationalCoordinatePath.path (F.degree c) (F.inner c) k).numerator.coeff
        (Nat.fromBitsLE (selectedDegree q))) (mValue q)
    rw [MatrixProduct.product_map, hcap]
    exact congrArg (fun z : ℤ => coefficientResidue z (mValue q)) H.1

end LeanCanny.Algebra.RationalCoordinatePathBits
