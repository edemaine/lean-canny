/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointRows

/-! # Context-preserving raw endpoint coefficient queries

Queries contain the prepared source record, row index, unary width word,
exponent word, and modulus predecessor. Every raw query is total; out-of-range
row indices are clamped. Widths are charged by the actual query-word length.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointCoefficient
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

def base (q : List Bool) : List Bool := pairFst (pairFst q)
def index (q : List Bool) : List Bool := pairFst (pairSnd q)
def widthWord (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd q))
def target (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd (pairSnd q)))
def modulus (q : List Bool) : List Bool := pairSnd (pairSnd (pairSnd (pairSnd q)))

theorem base_FP : base ∈ FP := by polytime [base]
theorem index_FP : index ∈ FP := by polytime [index]
theorem widthWord_FP : widthWord ∈ FP := by polytime [widthWord]
theorem target_FP : target ∈ FP := by polytime [target]
theorem modulus_FP : modulus ∈ FP := by polytime [modulus]

def dimension (F : Inputs) (q : List Bool) : ℕ := FlatAffineEndpointRows.arity F (pairFst q)
def width (q : List Bool) : ℕ := (widthWord q).length

theorem dimension_unary {F : Inputs} (h : F.Access) : UnaryFn (dimension F) :=
  (FlatAffineEndpointRows.arity_unary h).comp pairFst_mem_FP

noncomputable def rowAt (F : Inputs) (r : List Bool) (j : ℕ) : Fin (FlatAffineEndpointRows.arity F r) :=
  ⟨min j (FlatAffineEndpointRows.arity F r - 1), by dsimp [FlatAffineEndpointRows.arity]; omega⟩

lemma rowAt_val (F : Inputs) (r : List Bool) (j : Fin (FlatAffineEndpointRows.arity F r)) : rowAt F r j.val = j := by
  apply Fin.ext
  apply Nat.min_eq_left
  have H := j.isLt
  omega

noncomputable def selected (F : Inputs) (q : List Bool) : Fin (dimension F q) :=
  rowAt F (pairFst q) (Nat.fromBitsLE (index q))

theorem selected_unary {F : Inputs} (h : F.Access) : UnaryFn (fun q => (selected F q).val) :=
  UnaryFn.fromBitsLE_min index_FP ((dimension_unary h).sub (UnaryFn.const 1))

noncomputable def valueAt (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (r : List Bool) (j w : ℕ) (e m : List Bool) : List Bool :=
  residueBits (((FlatAffineEndpointPreparation.system F height r (rowAt F r j)).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) w (Nat.fromBitsLE e)) : ℤ) : ZMod (Nat.fromBitsLE m + 1))

noncomputable def coefficient (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : List Bool :=
  valueAt F height (pairFst q) (Nat.fromBitsLE (index q)) (width q) (target q) (modulus q)

theorem evaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (coefficient F height) := by
  let G := FlatAffineFullSourceContext.comp F pairFst
  have hG := FlatAffineFullSourceContext.access h pairFst_mem_FP
  have ER := PolynomialFamilyProductBits.reindexEvaluator (FlatAffineHeightSlabExceptional.evaluator h height hh) base base_FP
  have H := FlatAffineEndpointRows.evaluatorWithRetained hG (fun r => height (pairFst r)) (hh.comp pairFst_mem_FP)
    (selected F) (selected_unary h) (UnaryFn.length widthWord_FP)
    (FlatAffineHeightSlabExceptional.polynomial F height ∘ base) ER target_FP modulus_FP
  refine H.congr (funext fun q => ?_)
  have hs := funext (FlatAffinePowerPositive.system_comp F pairFst (pairFst q))
  have he : FrozenAffineCopies.system (FlatAffinePowerPositive.system G (pairFst q))
      ((FlatAffineHeightSlabExceptional.polynomial F height ∘ base) q) (height (pairFst (pairFst q)))
        FlatAffineEndpointPreparation.frozen = FlatAffineEndpointPreparation.system F height (pairFst q) := by
    unfold FlatAffineEndpointPreparation.system
    rw [hs]
    rfl
  change residueBits (((FrozenAffineCopies.system (FlatAffinePowerPositive.system G (pairFst q))
    ((FlatAffineHeightSlabExceptional.polynomial F height ∘ base) q) (height (pairFst (pairFst q)))
      FlatAffineEndpointPreparation.frozen (selected F q)).coeff _) : ZMod _) = _
  rw [he]
  rfl

theorem packet (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool)
    (j : Fin (FlatAffineEndpointRows.arity F r)) (w : ℕ) (e m : List Bool) :
    coefficient F height (pair r (pair (BinaryNatCode.encode j.val) (pair (List.replicate w true) (pair e m)))) =
      residueBits (((FlatAffineEndpointPreparation.system F height r j).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl _) w (Nat.fromBitsLE e)) : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  change valueAt F height _ _ _ _ _ = _
  simp only [index, width, widthWord, target, modulus, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, List.length_replicate]
  rw [valueAt, rowAt_val]

theorem rowEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (ctx : List Bool → List Bool) (hctx : ctx ∈ FP)
    (row : (q : List Bool) → Fin (FlatAffineEndpointRows.arity F (ctx q)))
    (hr : UnaryFn (fun q => (row q).val)) {W : List Bool → ℕ} (hW : UnaryFn W)
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (FlatAffineEndpointRows.arity F ∘ ctx) W
      (fun q => FlatAffineEndpointPreparation.system F height (ctx q) (row q)) target modulus) := by
  let prepare := fun q => pair (ctx q) (pair (BinaryNatCode.encode (row q).val)
    (pair (List.replicate (W q) true) (pair (target q) (modulus q))))
  have hp : prepare ∈ FP := mem_FP_pair hctx (mem_FP_pair (bits_mem_FP hr)
    (mem_FP_pair (hW.replicate_mem_FP true) (mem_FP_pair ht hm)))
  refine ((evaluator h height hh).precompose prepare hp).congr (funext fun q => ?_)
  exact packet F height (ctx q) (row q) (W q) (target q) (modulus q)

end LeanCanny.Encoding.FlatAffineEndpointCoefficient
