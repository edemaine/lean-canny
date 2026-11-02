/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.SuppliedFrozenMaskPin
public import LeanCanny.Encoding.FlatAffineExceptionalScalarRecipe
/-! # Original affine recipes use the supplied frozen set on every word -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSuppliedRecipe
open LeanCanny.Algebra LeanCanny.Computation MatrixPower LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Layout (F : Inputs) extends FlatAffineExceptionalScalarRecipe.Layout F where
  mask : List Bool → List Bool
structure Access {F : Inputs} (L : Layout F) : Prop extends FlatAffineExceptionalScalarRecipe.Access L.toLayout where
  mask : L.mask ∈ FP

noncomputable def frozen {F : Inputs} (L : Layout F) (q : List Bool) := SuppliedFrozenMaskBits.selected (arity F (L.input q)) (L.mask q)
noncomputable def order {F : Inputs} (L : Layout F) (q : List Bool) := FrozenCoordinateOrdering.permutation (frozen L q)
noncomputable def coarseOrder {F : Inputs} (L : Layout F) (q : List Bool) := FrozenCoordinateOrdering.permutation ((frozen L q).erase (L.height (L.input q)))

def orderCode {F : Inputs} (L : Layout F) (q : List Bool) := SuppliedFrozenMaskBits.forward (arity F (L.input q)) (L.mask q) (L.row q).val

theorem orderCode_FP {F : Inputs} (hF : F.Access) (L : Layout F) (hL : Access L) : orderCode L ∈ FP :=
  SuppliedFrozenMaskBits.forward_FP _ ((FlatAffineFullSourceTower.arity_unary hF).comp hL.input) _ hL.mask _ hL.row

theorem orderCode_eq {F : Inputs} (L : Layout F) (q : List Bool) : orderCode L q = BinaryNatCode.encode ((order L q) (L.row q)).val :=
  SuppliedFrozenMaskBits.forward_packet _ _ _

def coarseMask {F : Inputs} (L : Layout F) (q : List Bool) := FrozenCoordinatePermutationBits.eraseBit
  (pair (BinaryNatCode.encode (L.height (L.input q)).val) (SuppliedFrozenMaskBits.normalize (arity F (L.input q)) (L.mask q)))

theorem coarseMask_FP {F : Inputs} (hF : F.Access) (L : Layout F) (hL : Access L) : coarseMask L ∈ FP := by
  have HH : BinaryFn (fun q => (L.height (L.input q)).val) := hL.height.comp hL.input
  exact mem_FP_comp (mem_FP_pair HH.bits_mem_FP
    (SuppliedFrozenMaskBits.normalize_FP _ ((FlatAffineFullSourceTower.arity_unary hF).comp hL.input) _ hL.mask)) FrozenCoordinatePermutationBits.eraseBit_FP

theorem coarseMask_eq {F : Inputs} (L : Layout F) (q : List Bool) : coarseMask L q =
    FrozenCoordinatePermutationBits.mask ((frozen L q).erase (L.height (L.input q))) := by
  rw [coarseMask, SuppliedFrozenMaskBits.normalize_mask, FrozenCoordinatePermutationBits.eraseBit_mask]
  rfl

def coarseCode {F : Inputs} (L : Layout F) (q : List Bool) := FrozenCoordinatePermutationBits.reader (pair (coarseMask L q) (BinaryNatCode.encode (L.row q).val))
attribute [local irreducible] FrozenCoordinatePermutationBits.reader

theorem coarseCode_FP {F : Inputs} (hF : F.Access) (L : Layout F) (hL : Access L) : coarseCode L ∈ FP :=
  mem_FP_comp (mem_FP_pair (coarseMask_FP hF L hL) hL.row.bits_mem_FP) FrozenCoordinatePermutationBits.reader_FP

theorem coarseCode_eq {F : Inputs} (L : Layout F) (q : List Bool) : coarseCode L q = BinaryNatCode.encode ((coarseOrder L q) (L.row q)).val := by
  rw [coarseCode, coarseMask_eq]
  exact FrozenCoordinatePermutationBits.reader_mask _ _

noncomputable def expression {F : Inputs} (L : Layout F) (q : List Bool) : IntegralMixedHistory.AffineExpr :=
  if L.mode q = 1 then FlatAffineExceptionalMixedExpressions.shifted F L.height (L.input q) (order L q (L.row q))
  else if L.mode q = 2 then FlatAffineExceptionalMixedExpressions.shifted F L.height (L.input q) (coarseOrder L q (L.row q))
  else .constant 0
noncomputable def word {F : Inputs} (L : Layout F) (q : List Bool) := IntegralMixedAffineCode.encode (expression L q)

theorem syntax_space {F : Inputs} (hF : F.Access) (L : Layout F) (hL : Access L) : SpaceFunction (word L) := by
  have HO := FlatAffineExceptionalMixedExpressions.shifted_encode_space_source hF L.input hL.input L.height hL.height _
    ((SpaceFunction.ofFP _ (orderCode_FP hF L hL)).congr (funext (orderCode_eq L)))
  have HC := FlatAffineExceptionalMixedExpressions.shifted_encode_space_source hF L.input hL.input L.height hL.height _
    ((SpaceFunction.ofFP _ (coarseCode_FP hF L hL)).congr (funext (coarseCode_eq L)))
  have H2 := SpaceFunction.branch (fun q => decide (L.mode q = 2)) (hL.mode.eq (BinaryFn.const 2)).flag_mem_FP HC
    (SpaceFunction.ofFP _ (constFn_mem_FP (IntegralMixedAffineCode.encode (.constant 0))))
  have H1 := SpaceFunction.branch (fun q => decide (L.mode q = 1)) (hL.mode.eq (BinaryFn.const 1)).flag_mem_FP HO H2
  apply H1.congr
  funext q
  simp only [word, expression, decide_eq_true_eq]
  split_ifs <;> rfl

def heightCode {F : Inputs} (L : Layout F) (q : List Bool) := SuppliedFrozenMaskBits.inverse (arity F (L.input q)) (L.mask q) (L.height (L.input q)).val

theorem heightCode_FP {F : Inputs} (hF : F.Access) (L : Layout F) (hL : Access L) : heightCode L ∈ FP :=
  SuppliedFrozenMaskBits.inverse_FP _ ((FlatAffineFullSourceTower.arity_unary hF).comp hL.input) _ hL.mask _ (hL.height.comp hL.input)

theorem heightCode_eq {F : Inputs} (L : Layout F) (q : List Bool) : heightCode L q = BinaryNatCode.encode (((order L q).symm) (L.height (L.input q))).val :=
  SuppliedFrozenMaskBits.inverse_packet _ _ _

noncomputable def slope {F : Inputs} (L : Layout F) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (A : List Bool → ℕ) (q : List Bool) : ℤ :=
  if L.sweep q then if A q = ((order L q).symm (L.height (L.input q))).val then
    FlatAffineExceptionalBankSource.denominator F C L.height (L.input q) else 0
  else if A q = 0 then 1 else 0

theorem slope_space {F : Inputs} (hF : F.Access) (L : Layout F) (hL : Access L)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (A : List Bool → ℕ) (hA : BinaryFn A)
    (mod : List Bool → List Bool) (hm : mod ∈ FP) :
    SpaceFunction (fun q => residueBits (slope L C A q : ZMod (Nat.fromBitsLE (mod q) + 1))) := by
  have HI : BinaryFn (fun q => ((order L q).symm (L.height (L.input q))).val) :=
    (BinaryFn.fromBits (heightCode_FP hF L hL)).of_eq (fun q => by rw [heightCode_eq]; exact Nat.fromBitsLE_bits _)
  have HQ := FlatAffineExceptionalSelectorSpace.initial_denominator_space hF C L.height hL.height L.input mod hL.input hm
  have HZ := SpaceFunction.ofFP (fun _ : List Bool => []) (constFn_mem_FP [])
  have HS0 := SpaceFunction.branch (fun q => decide (A q = ((order L q).symm (L.height (L.input q))).val))
    (hA.eq HI).flag_mem_FP HQ HZ
  have HS : SpaceFunction (fun q => residueBits ((if A q = ((order L q).symm (L.height (L.input q))).val then
      FlatAffineExceptionalBankSource.denominator F C L.height (L.input q) else 0 : ℤ) : ZMod (Nat.fromBitsLE (mod q) + 1))) := by
    apply HS0.congr
    funext q
    simp only [decide_eq_true_eq]
    split_ifs
    · rfl
    · simpa only [ArithmeticBits.zero, Int.cast_zero] using ArithmeticBits.zero_residueBits (Nat.fromBitsLE (mod q) + 1)
  have H1 : SpaceFunction (fun q => residueBits ((if A q = 0 then 1 else 0 : ℤ) : ZMod (Nat.fromBitsLE (mod q) + 1))) := by
    have HC0 := (hA.eq (BinaryFn.const 0)).ite_mem_FP
      (constFn_mem_FP (SignStatisticBits.integerCode 1)) (constFn_mem_FP (SignStatisticBits.integerCode 0))
    have HC : (fun q => SignStatisticBits.integerCode (if A q = 0 then 1 else 0 : ℤ)) ∈ FP :=
      mem_FP_of_eq HC0 (fun q => by split_ifs <;> rfl)
    exact SignedIntegerResidue.evaluator (SpaceFunction.ofFP _ HC) hm
  have H := SpaceFunction.branch L.sweep hL.sweep HS H1
  apply H.congr
  funext q
  simp only [slope]
  split_ifs <;> rfl
end LeanCanny.Encoding.FlatAffineExceptionalSuppliedRecipe
