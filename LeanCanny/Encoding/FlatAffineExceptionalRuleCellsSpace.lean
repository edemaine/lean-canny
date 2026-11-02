/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalShiftedSyntaxSpace
public import LeanCanny.Encoding.FlatAffineExceptionalSlopeSource
/-! # Actual ordered and coarse rule cells from original level syntax -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalRuleCellsSpace
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem ordered_syntax {F : Inputs} (hF : F.Access) (input : List Bool → List Bool) (hi : input ∈ FP)
    (h : (u : List Bool) → Fin (arity F u)) (hh : BinaryFn (fun u => (h u).val))
    (r : (q : List Bool) → Fin (arity F (input q)))
    (hr : ∀ q, r q ∉ FlatAffineExceptionalOrderedRule.frozen F (input q))
    (row : (q : List Bool) → Fin (arity F (input q)))
    (ho : SpaceFunction (fun q => BinaryNatCode.encode ((FlatAffineExceptionalOrderedRule.order F (input q)) (row q)).val)) :
    SpaceFunction (fun q => IntegralMixedAffineCode.encode
      ((FlatAffineExceptionalOrderedRule.rule F h (input q) (r q) (hr q)).heights (row q))) :=
  FlatAffineExceptionalMixedExpressions.shifted_encode_space_source hF input hi h hh _ ho

theorem ordered_reference {F : Inputs} (hF : F.Access) (input mod : List Bool → List Bool) (hi : input ∈ FP) (hm : mod ∈ FP)
    (h : (u : List Bool) → Fin (arity F u)) (hh : BinaryFn (fun u => (h u).val))
    (r : (q : List Bool) → Fin (arity F (input q)))
    (hr : ∀ q, r q ∉ FlatAffineExceptionalOrderedRule.frozen F (input q))
    (row : (q : List Bool) → Fin (arity F (input q)))
    (ho : SpaceFunction (fun q => BinaryNatCode.encode ((FlatAffineExceptionalOrderedRule.order F (input q)) (row q)).val))
    (I : List Bool → ℕ) (hI : BinaryFn I) :
    SpaceFunction (fun q => residueBits (IntegralMixedAffineCoefficients.referenceCoefficient
      ((FlatAffineExceptionalOrderedRule.rule F h (input q) (r q) (hr q)).heights (row q)) (I q) : ZMod (Nat.fromBitsLE (mod q) + 1))) :=
  FlatAffineExceptionalMixedExpressions.shifted_reference_space hF input mod hi hm h hh _ ho I hI

theorem coarse_syntax {F : Inputs} (hF : F.Access) (input : List Bool → List Bool) (hi : input ∈ FP)
    (h : (u : List Bool) → Fin (arity F u)) (hh : BinaryFn (fun u => (h u).val))
    (row : (q : List Bool) → Fin (arity F (input q)))
    (ho : SpaceFunction (fun q => BinaryNatCode.encode ((FlatAffineExceptionalCoarseRule.order F h (input q)) (row q)).val)) :
    SpaceFunction (fun q => IntegralMixedAffineCode.encode
      ((FlatAffineExceptionalCoarseRule.rule F h (input q)).heights (row q))) :=
  FlatAffineExceptionalMixedExpressions.shifted_encode_space_source hF input hi h hh _ ho

theorem coarse_constant {F : Inputs} (hF : F.Access) (input mod : List Bool → List Bool) (hi : input ∈ FP) (hm : mod ∈ FP)
    (h : (u : List Bool) → Fin (arity F u)) (hh : BinaryFn (fun u => (h u).val))
    (row : (q : List Bool) → Fin (arity F (input q)))
    (ho : SpaceFunction (fun q => BinaryNatCode.encode ((FlatAffineExceptionalCoarseRule.order F h (input q)) (row q)).val)) :
    SpaceFunction (fun q => residueBits (IntegralMixedAffineCoefficients.constantCoefficient
      ((FlatAffineExceptionalCoarseRule.rule F h (input q)).heights (row q)) : ZMod (Nat.fromBitsLE (mod q) + 1))) :=
  FlatAffineExceptionalMixedExpressions.shifted_constant_space hF input mod hi hm h hh _ ho
end LeanCanny.Encoding.FlatAffineExceptionalRuleCellsSpace
