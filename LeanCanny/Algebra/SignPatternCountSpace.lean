/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SignPatternSpace

/-! # Exact numbers of distinct roots realizing a finite sign pattern

The scaled count is divisible by 2^k. That factor has polynomial binary length
under the family-size hypothesis, so certified FP division returns the count.
-/

@[expose] public section

namespace LeanCanny.Algebra.SignPatternBits
open Complexity Polynomial
open LeanCanny.Encoding
open LeanCanny.Computation

noncomputable def rootCount (F : Family) (c : List Bool) : ℕ := RootSignQueries.signCount
  (((F.root c).map (algebraMap ℤ ℝ)).roots.toFinset)
  (fun i : Fin (Nat.fromBitsLE (F.count c)) => (F.polynomial c i.val).map (algebraMap ℤ ℝ))
  (fun i => F.pattern c i.val)

theorem scaledCount_eq_rootCount (F : Family) (c : List Bool) :
    scaledCount F c = ((2 ^ Nat.fromBitsLE (F.count c) * rootCount F c : ℕ) : ℤ) := by
  unfold scaledCount rootCount
  rw [RootSignQueries.scaledRootCount_eq, Fintype.card_fin]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem zeros_value (n : ℕ) : Nat.fromBitsLE (List.replicate n false ++ [true]) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, Nat.fromBitsLE_cons, Bool.false_eq_true,
      ↓reduceIte, Nat.zero_add, ih, pow_succ]
    omega

def scaleCode (F : Family) (c : List Bool) : List Bool := List.replicate (Nat.fromBitsLE (F.count c)) false ++ [true]

theorem scaleCode_mem_FP (F : Family) (hF : ControlsPolyTime F) : scaleCode F ∈ FP :=
  Cobham.appendFn_mem_FP (hF.countUnary.replicate_mem_FP false) (constFn_mem_FP [true])

def unscale (F : Family) (z : List Bool) : List Bool :=
  BinaryNat.div (pair (pairFst (pairSnd z)) (scaleCode F (pairFst z)))

theorem unscale_mem_FP (F : Family) (hF : ControlsPolyTime F) : unscale F ∈ FP := by
  have hv := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hs := mem_FP_comp pairFst_mem_FP (scaleCode_mem_FP F hF)
  have h := mem_FP_comp (mem_FP_pair hv hs) BinaryNat.div_mem_FP
  refine mem_FP_of_eq (g := unscale F) h ?_
  intro z
  simp only [unscale, Function.comp_apply]

theorem unscale_pair (F : Family) (c : List Bool) :
    unscale F (pair c (SignStatisticBits.integerCode (scaledCount F c))) = BinaryNatCode.encode (rootCount F c) := by
  rw [scaledCount_eq_rootCount]
  simp only [unscale, SignStatisticBits.integerCode, pairFst_pair, pairSnd_pair, BinaryNat.div_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Int.toNat_natCast, scaleCode, zeros_value]
  rw [Nat.mul_div_cancel_left _ (pow_pos (by decide) _)]

noncomputable def rootCountEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (hs : a.pattern ∈ FP) (H : SpaceFunction a.rootCoefficient) (P : SpaceFunction a.polynomialCoefficient) :
    SpaceFunction (fun c => BinaryNatCode.encode (rootCount F c)) := by
  let E := (evaluator a hF hs H P).withInput.postcompose (unscale F) (unscale_mem_FP F hF)
  refine E.congr (funext fun c => ?_)
  exact unscale_pair F c

end LeanCanny.Algebra.SignPatternBits
