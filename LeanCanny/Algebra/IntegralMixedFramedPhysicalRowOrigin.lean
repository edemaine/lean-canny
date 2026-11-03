/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalRowDegree

/-! # A nonscalar physical row has a genuine critical creator inside the budget -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalRowOrigin
open LeanCanny LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan prefixLength defaultInstruction)
open IntegralMixedFramedHistoryScript (chronological)
open IntegralMixedFramedPhysicalIndex (span)
open IntegralMixedFramedPhysicalRowSelector
open IntegralMixedFramedPhysicalRowDegree (header)
open IntegralMixedHeaderTablesBits (Tables)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem nonScalar_context (P : Parameters) (T : Tables) (key : List Bool) (r : ℕ)
    (hr : r<fullArity P T (pair key (BinaryNatCode.encode r)))
    (hs : ¬IsScalar P T (pair key (BinaryNatCode.encode r))) :
    (header P T (pair key (BinaryNatCode.encode r))).context=1 := by
  by_contra H
  simp only [header,pairFst_pair] at H
  have HL:=localRow_lt_span P T key r hr
  have HE : span P T (birthPacket P T (pair key (BinaryNatCode.encode r)))=1 :=by
    simp only [span,birthPacket,pairFst_pair,pairSnd_pair,List.length_replicate,ite_eq_right H]
  apply hs
  refine ⟨?_,?_⟩
  · simpa only [pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] using hr
  · rw [HE] at HL ⊢
    omega

theorem critical_before_end (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (ht : IntegralMixedFramedHeaderBits.Represents P D H T) (key : List Bool) (b : ℕ)
    (hb : (IntegralMixedCommandHeaderBits.lookup (T.commands (pairFst key)) b).context=1) :
    b<(D.rules (pairFst key)).length := by
  by_contra HH
  have HN : chronological (D.rules (pairFst key)) b=none :=
    List.getElem?_eq_none (by rw [List.length_reverse]; exact Nat.le_of_not_gt HH)
  rw [ht.commands,IntegralMixedFramedHeaderBits.lookup_words _
    (defaultInstruction P D (pairFst key)) (by rfl),HN] at hb
  exact (by decide : (0:ℕ)≠1) hb

theorem nonScalar_birth_lt (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (ht : IntegralMixedFramedHeaderBits.Represents P D H T) (key : List Bool) (r : ℕ)
    (hr : r<fullArity P T (pair key (BinaryNatCode.encode r)))
    (hs : ¬IsScalar P T (pair key (BinaryNatCode.encode r))) :
    rowBirth P T (pair key (BinaryNatCode.encode r))<(D.rules (pairFst key)).length := by
  have HC:=nonScalar_context P T key r hr hs
  apply critical_before_end P D H T ht key _
  simpa only [header,pairFst_pair] using HC

theorem nonScalar_below_cap (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (ht : IntegralMixedFramedHeaderBits.Represents P D H T) (key : List Bool) (r : ℕ)
    (hr : r<fullArity P T (pair key (BinaryNatCode.encode r)))
    (hs : ¬IsScalar P T (pair key (BinaryNatCode.encode r))) :
    rowBirth P T (pair key (BinaryNatCode.encode r))<P.cap (pairFst key) := by
  have HB:=nonScalar_birth_lt P D H T ht key r hr hs
  have HR:=D.room (pairFst key)
  omega

theorem command_of_context {n B : ℕ} {Q : IntegralMixedHistory.SpatialSource n}
    (c : IntegralMixedFullHistoryScript.Command Q B)
    (hc : (IntegralMixedCommandHeaderBits.command c).context=1) :
    ∃r : IntegralMixedHistory.CriticalRule n,c=.critical r := by
  cases c with
  | integer=>exact False.elim (Nat.zero_ne_one hc)
  | critical r=>exact ⟨r,rfl⟩
  | cut r k=>cases k <;> simp [IntegralMixedCommandHeaderBits.command,IntegralMixedCommandHeaderBits.kindContext] at hc

theorem nonScalar_critical (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (ht : IntegralMixedFramedHeaderBits.Represents P D H T) (key : List Bool) (r : ℕ)
    (hr : r<fullArity P T (pair key (BinaryNatCode.encode r)))
    (hs : ¬IsScalar P T (pair key (BinaryNatCode.encode r))) :
    ∃v : IntegralMixedHistory.CriticalRule (P.ambient (pairFst key)),
      ((chronological (D.rules (pairFst key)) (rowBirth P T (pair key (BinaryNatCode.encode r)))).getD
        (defaultInstruction P D (pairFst key))).command=.critical v := by
  have HC:=nonScalar_context P T key r hr hs
  simp only [header,pairFst_pair] at HC
  rw [ht.commands,IntegralMixedFramedHeaderBits.lookup_words _
    (defaultInstruction P D (pairFst key)) (by rfl)] at HC
  exact command_of_context _ HC

end LeanCanny.Algebra.IntegralMixedFramedPhysicalRowOrigin
