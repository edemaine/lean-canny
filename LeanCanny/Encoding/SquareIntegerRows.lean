/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleAccess
public import LeanCanny.Algebra.FixedWidthRowArithmetic

/-! # Native original-row access independent of sampling certificates

Square systems can be transformed before their coordinate annihilators are
constructed. Canonical row queries charge the original coefficient program;
native context changes retain every width, exponent, and modulus field.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareIntegerRows
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

structure Family where
  count : List Bool → ℕ
  count_pos : ∀ u, 0 < count u
  system : (u : List Bool) → Fin (count u) → MvPolynomial (Fin (count u)) ℤ

def selected (F : Family) (u w : List Bool) : Fin (F.count u) :=
  ⟨min (Nat.fromBitsLE w) (F.count u - 1), by have := F.count_pos u; omega⟩

noncomputable def valueAt (F : Family) (u i : List Bool) (w : ℕ) (e m : List Bool) : List Bool :=
  residueBits (((F.system u (selected F u i)).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) w (Nat.fromBitsLE e))) : ZMod (Nat.fromBitsLE m + 1))

noncomputable def coefficient (F : Family) (q : List Bool) : List Bool :=
  valueAt F (SquareSampleInput.source q) (SquareSampleInput.indexWord q)
    (SquareSampleInput.widthWord q).length (SquareSampleInput.rankWord q) (SquareSampleInput.modulusWord q)

structure Family.Access (F : Family) : Prop where
  count : UnaryFn F.count
  coefficient : SpaceFunction (coefficient F)

theorem selected_encode (F : Family) (u : List Bool) (i : Fin (F.count u)) :
    selected F u (BinaryNatCode.encode i.val) = i := by
  apply Fin.ext
  change min (Nat.fromBitsLE (BinaryNatCode.encode i.val)) (F.count u - 1) = i.val
  rw [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.min_eq_left (by have := i.isLt; omega)]

theorem packet (F : Family) (u : List Bool) (i : Fin (F.count u)) (w e m : List Bool) :
    coefficient F (SquareSampleInput.query u (BinaryNatCode.encode i.val) w e m) =
      residueBits (((F.system u i).coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) w.length (Nat.fromBitsLE e))) :
        ZMod (Nat.fromBitsLE m + 1)) := by
  simp only [coefficient, SquareSampleInput.query, SquareSampleInput.source, SquareSampleInput.indexWord,
    SquareSampleInput.widthWord, SquareSampleInput.rankWord, SquareSampleInput.modulusWord, pairFst_pair, pairSnd_pair]
  unfold valueAt
  rw [selected_encode]

theorem rowEvaluator {F : Family} (A : F.Access) (ctx : List Bool → List Bool) (hctx : ctx ∈ FP)
    (row : (q : List Bool) → Fin (F.count (ctx q))) (hr : UnaryFn (fun q => (row q).val))
    {W : List Bool → ℕ} (hW : UnaryFn W) {target modulus : List Bool → List Bool}
    (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (F.count ∘ ctx) W (fun q => F.system (ctx q) (row q)) target modulus) := by
  let prepare (q : List Bool) := SquareSampleInput.query (ctx q) (BinaryNatCode.encode (row q).val)
    (List.replicate (W q) true) (target q) (modulus q)
  have hp := SquareSampleInput.query_FP hctx (bits_mem_FP hr) (hW.replicate_mem_FP true) ht hm
  refine (A.coefficient.precompose prepare hp).congr (funext fun q => ?_)
  change coefficient F (SquareSampleInput.query _ _ _ _ _) = _
  rw [packet, List.length_replicate]
  rfl

noncomputable def comp (F : Family) (f : List Bool → List Bool) : Family where
  count := F.count ∘ f
  count_pos u := F.count_pos (f u)
  system u := F.system (f u)

theorem access_comp {F : Family} (A : F.Access) {f : List Bool → List Bool} (hf : f ∈ FP) : (comp F f).Access := by
  refine ⟨A.count.comp hf, (A.coefficient.precompose (SquareSampleInput.mapSource f)
    (SquareSampleInput.mapSource_FP hf)).congr (funext fun q => ?_)⟩
  simp only [Function.comp_apply, coefficient, SquareSampleInput.mapSource, SquareSampleInput.query, SquareSampleInput.source,
    SquareSampleInput.indexWord, SquareSampleInput.widthWord, SquareSampleInput.rankWord, SquareSampleInput.modulusWord,
    pairFst_pair, pairSnd_pair]
  rfl

end LeanCanny.Encoding.SquareIntegerRows
