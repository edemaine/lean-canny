/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedFramedRowSource
public import LeanCanny.Algebra.PaddedIntegralGeneratorSourceComp
public import LeanCanny.Algebra.FixedWidthBlockRenameSpace

/-! # Native labels of the creating source for an actual prefix row

A requested row is capped to the current positive prefix. Subtracting its
newest-first index recovers the exact original birth. The query retains the
full original root; every counter is bounded by the original unary horizon.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedRowBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan prefixLength keyAt)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def count (P : Parameters) (key : List Bool→List Bool) (q : List Bool) := prefixLength P (key q)
def selected (P : Parameters) (key index : List Bool→List Bool) (q : List Bool) :=
  min (Nat.fromBitsLE (index q)) (count P key q-1)
def birth (P : Parameters) (key index : List Bool→List Bool) (q : List Bool) :=
  count P key q-1-selected P key index q

def creatorKey (P : Parameters) (key index : List Bool→List Bool) (q : List Bool) :=
  keyAt (pairFst (key q)) (birth P key index q) []

theorem count_unary (P : Parameters) (a : Access P) (key : List Bool→List Bool) (hk : key∈FP) :
    UnaryFn (count P key) := (IntegralMixedFullHistoryFamilyBits.prefix_unary P a).comp hk

theorem selected_unary (P : Parameters) (a : Access P) (key index : List Bool→List Bool)
    (hk : key∈FP) (hi : index∈FP) : UnaryFn (selected P key index) :=
  UnaryFn.fromBitsLE_min hi ((count_unary P a key hk).sub (UnaryFn.const 1))

theorem birth_unary (P : Parameters) (a : Access P) (key index : List Bool→List Bool)
    (hk : key∈FP) (hi : index∈FP) : UnaryFn (birth P key index) :=
  ((count_unary P a key hk).sub (UnaryFn.const 1)).sub (selected_unary P a key index hk hi)

theorem creatorKey_FP (P : Parameters) (a : Access P) (key index : List Bool→List Bool)
    (hk : key∈FP) (hi : index∈FP) : creatorKey P key index∈FP :=
  mem_FP_pair (mem_FP_comp hk pairFst_mem_FP)
    (mem_FP_pair (BinaryFn.ofUnary (birth_unary P a key index hk hi)).bits_mem_FP (constFn_mem_FP []))

theorem creatorKey_root (P : Parameters) (key index : List Bool→List Bool) (q : List Bool) :
    pairFst (creatorKey P key index q)=pairFst (key q) :=
  IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _

theorem birth_bound (P : Parameters) (key index : List Bool→List Bool) (q : List Bool) :
    birth P key index q≤P.cap (pairFst (key q))+1 :=
  (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (min_le_right _ _))

theorem creatorKey_birth (P : Parameters) (key index : List Bool→List Bool) (q : List Bool) :
    prefixLength P (creatorKey P key index q)=birth P key index q :=
  IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P _ _ _ (birth_bound P key index q)

theorem selected_lt (P : Parameters) (key index : List Bool→List Bool) (q : List Bool)
    (hpos : 0<count P key q) : selected P key index q<count P key q := by
  have H : selected P key index q≤count P key q-1 := min_le_right _ _
  omega

theorem creator_arity (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key index : List Bool→List Bool) (q : List Bool) :
    (IntegralMixedFramedCompanionBits.source P D H).arity (creatorKey P key index q)=birth P key index q := by
  change (IntegralMixedFramedHistoryFamilyBits.family P D H).birth _=_
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth,creatorKey_birth]

theorem source_arity_unary (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) : UnaryFn (IntegralMixedFramedCompanionBits.source P D H).arity :=
  (IntegralMixedFullHistoryFamilyBits.prefix_unary P a).of_eq
    (fun key=>(IntegralMixedFramedHistoryFamilyBits.family_birth P D H key).symm)

theorem source_width_unary (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) : UnaryFn (IntegralMixedFramedCompanionBits.source P D H).width :=
  a.width.comp pairFst_mem_FP

end LeanCanny.Algebra.IntegralMixedFramedRowBits
