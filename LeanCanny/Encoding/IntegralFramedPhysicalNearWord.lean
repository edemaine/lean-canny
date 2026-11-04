/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalNearGuard
/-! # Near guards use the decoded rank of their literal rank word -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalNear
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem pack_rank (a b u v w x y : List Bool) (he : Nat.fromBitsLE a=Nat.fromBitsLE b) :
    OrderedWindowStatisticBits.Accept (OrderedWindowStatisticBits.pack a u v w x y)↔
      OrderedWindowStatisticBits.Accept (OrderedWindowStatisticBits.pack b u v w x y) :=by
  simp only [OrderedWindowStatisticBits.Accept,OrderedWindowStatisticBits.positive,
    OrderedWindowStatisticBits.negative,OrderedWindowStatisticBits.pack,OrderedWindowStatisticBits.unit,
    OrderedWindowStatisticBits.lowerSquare,OrderedWindowStatisticBits.lower,OrderedWindowStatisticBits.upperSquare,
    OrderedWindowStatisticBits.upper,pairFst_pair,pairSnd_pair,he]

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (parent terminal : List Bool→List Bool) (center selected : List Bool→ℕ)
  (hpos : ∀q,0<(family P D H).birth (terminal q))
  (hf : ∀root,1≤F root) (hd : ∀key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
  (right : Bool)
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

 theorem accept_rank_word (q w code : List Bool) :
    pair (pair q w) code∈Accept P D H L F C hs parent terminal center selected hpos hf hd right ↔
      pair (pair q w) (BinaryNatCode.encode (Nat.fromBitsLE code))∈
        Accept P D H L F C hs parent terminal center selected hpos hf hd right :=by
  unfold Accept packet reset
  simp only [Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair]
  exact pack_rank _ _ _ _ _ _ _ (Nat.fromBitsLE_bits _).symm

end LeanCanny.Encoding.IntegralFramedPhysicalNear
