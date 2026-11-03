/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalRowSelector
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalColumn
/-! # Full-row scalar selectors recover the exact newest-first bank index -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalScalarSelection
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedPhysicalRowSelector IntegralMixedFramedPhysicalIndex
open IntegralMixedHeaderTablesBits (Tables)
open IntegralMixedFramedHistoryFamilyBits (prefixLength)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def index (P : Parameters) (T : Tables) (q : List Bool) :=prefixLength P (pairFst q)-1-rowBirth P T q

theorem index_unary (P : Parameters) (a : Access P) (T : Tables) (ht : IntegralMixedHeaderTablesBits.Access T) :
    UnaryFn (index P T) :=
  (((IntegralMixedFullHistoryFamilyBits.prefix_unary P a).comp pairFst_mem_FP).sub (UnaryFn.const 1)).sub (rowBirth_unary P a T ht)

theorem index_lt (P : Parameters) (T : Tables) (key : List Bool) (r : ℕ)
    (hr : r<fullArity P T (pair key (BinaryNatCode.encode r))) :
    index P T (pair key (BinaryNatCode.encode r))<prefixLength P key := by
  have HB:=(rowBirth_interval P T key r hr).1
  unfold index
  rw [pairFst_pair]
  omega

theorem scalar_column (P : Parameters) (T : Tables) (key : List Bool) (r : ℕ)
    (hr : r<fullArity P T (pair key (BinaryNatCode.encode r)))
    (hs : IsScalar P T (pair key (BinaryNatCode.encode r))) :
    scalarColumn P T (pair key (BinaryNatCode.encode (index P T (pair key (BinaryNatCode.encode r)))))=r := by
  obtain ⟨hb,hl,hu⟩:=rowBirth_interval P T key r hr
  have HL:=hs.2
  unfold localRow at HL
  have HC : Nat.fromBitsLE (pairSnd (pair key (BinaryNatCode.encode r)))=r := by
    rw [pairSnd_pair]
    exact Nat.fromBitsLE_bits r
  rw [HC,min_eq_left hr.le] at HL
  have HE:=prefix_succ P T key (rowBirth P T (pair key (BinaryNatCode.encode r)))
  have HP : retainedPrefix P (pair key (BinaryNatCode.encode (index P T (pair key (BinaryNatCode.encode r)))))=
      rowBirth P T (pair key (BinaryNatCode.encode r))+1 := by
    rw [retainedPrefix,pairFst_pair,pairSnd_pair]
    rw [show Nat.fromBitsLE (BinaryNatCode.encode (index P T (pair key (BinaryNatCode.encode r))))=
      index P T (pair key (BinaryNatCode.encode r)) from Nat.fromBitsLE_bits _]
    rw [min_eq_left (index_lt P T key r hr).le]
    unfold index
    rw [pairFst_pair]
    omega
  unfold scalarColumn columnPacket
  rw [pairFst_pair,HP]
  have HB : birthPacket P T (pair key (BinaryNatCode.encode r))=
      pair key (List.replicate (rowBirth P T (pair key (BinaryNatCode.encode r))) true) :=by
    simp only [birthPacket,pairFst_pair]
  rw [HB] at HL
  have HS:=span_pos P T (birthPacket P T (pair key (BinaryNatCode.encode r)))
  rw [HB] at HS
  omega

end LeanCanny.Algebra.IntegralMixedFramedPhysicalScalarSelection
