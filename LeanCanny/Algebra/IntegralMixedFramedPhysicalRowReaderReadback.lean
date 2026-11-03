/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalRowReaderSpace
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalSelectorPullback
/-! # Exact source, query payload and caller-budget readback for full rows -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalRowReaderBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

 theorem datum_key (P : Parameters) (D : Plan P) (key : List Bool→List Bool) (q : List Bool) :
    pairFst (pairFst (datum P D key q))=liftedKey key q := by simp only [datum,pairFst_pair]

theorem datum_row (P : Parameters) (D : Plan P) (key : List Bool→List Bool) (q : List Bool) :
    pairSnd (pairFst (datum P D key q))=BinaryNatCode.encode (row P D key q) :=by
  simp only [datum,pairFst_pair,pairSnd_pair]

theorem datum_modulus (P : Parameters) (D : Plan P) (key : List Bool→List Bool) (q : List Bool) :
    pairSnd (datum P D key q)=SquareSampleInput.modulusWord q :=pairSnd_pair _ _

theorem liftedKey_root (key : List Bool→List Bool) (q : List Bool) :
    pairFst (liftedKey key q)=pair (pairFst (saved key q)) (SquareSampleInput.modulusWord q) :=pairFst_pair _ _

theorem liftedKey_prefix (P : Parameters) (key : List Bool→List Bool) (q : List Bool) :
    IntegralMixedFramedHistoryFamilyBits.prefixLength (lifted P) (liftedKey key q)=
      IntegralMixedFramedHistoryFamilyBits.prefixLength P (saved key q) :=by
  simp only [IntegralMixedFramedHistoryFamilyBits.prefixLength,IntegralMixedFullHistoryFamilyBits.prefixLength,
    lifted,liftedKey,IntegralMixedFramedRootPullback.parameters,Function.comp_apply,pairFst_pair,pairSnd_pair]

theorem projected_root (key : List Bool→List Bool) (q : List Bool) :
    pairFst (IntegralMixedFramedRootPullback.key pairFst (liftedKey key q))=pairFst (saved key q) :=by
  rw [IntegralMixedFramedRootPullback.key_root,liftedKey_root,pairFst_pair]

theorem projected_prefix (P : Parameters) (key : List Bool→List Bool) (q : List Bool) :
    IntegralMixedFramedHistoryFamilyBits.prefixLength P (IntegralMixedFramedRootPullback.key pairFst (liftedKey key q))=
      IntegralMixedFramedHistoryFamilyBits.prefixLength P (saved key q) :=by
  exact (IntegralMixedFramedRootPullback.key_prefix P pairFst IntegralMixedFramedModulusPacket.extra _).trans
    (liftedKey_prefix P key q)

theorem caller_budget (P : Parameters) (D : Plan P) (key : List Bool→List Bool) (q : List Bool) :
    Nat.fromBitsLE (pairSnd (datum P D key q))+1≤
      numericCap (lifted P) (pairFst (pairFst (pairFst (datum P D key q)))) :=by
  have H:=IntegralMixedFramedRootPullback.modulus_budget P pairFst IntegralMixedFramedModulusPacket.extra
    (pair (pairFst (saved key q)) (SquareSampleInput.modulusWord q))
  simpa only [datum_key,liftedKey_root,datum_modulus,IntegralMixedFramedModulusPacket.extra,pairSnd_pair] using H

theorem width_read (P : Parameters) (D : Plan P) (key : List Bool→List Bool) (q : List Bool) :
    (width∘origin) (datum P D key q)=width q :=by rw [Function.comp_apply,origin_datum]

theorem target_read (P : Parameters) (D : Plan P) (key : List Bool→List Bool) (q : List Bool) :
    (SquareSampleInput.rankWord∘origin) (datum P D key q)=SquareSampleInput.rankWord q :=by
  rw [Function.comp_apply,origin_datum]

theorem scalar_predicate (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hT : IntegralMixedFramedHeaderBits.Represents P D J T)
    (Jnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (U : IntegralMixedHeaderTablesBits.Tables)
    (hU : IntegralMixedFramedHeaderBits.Represents (lifted P) (liftedPlan P D) Jnew U)
    (key : List Bool→List Bool) (q : List Bool) :
    IntegralMixedFramedPhysicalRowSelector.IsScalar (lifted P) U
      (pair (liftedKey key q) (BinaryNatCode.encode (row P D key q)))↔
    IntegralMixedFramedPhysicalRowSelector.IsScalar P T
      (pair (saved key q) (BinaryNatCode.encode (row P D key q))) :=
  (IntegralMixedFramedPhysicalSelectorPullback.scalar_pull P D J pairFst IntegralMixedFramedModulusPacket.extra Jnew T U hT hU _ _).trans
    (IntegralMixedFramedPhysicalSelectorPullback.scalar_same P T _ _ _ (projected_root key q) (projected_prefix P key q))

theorem row_lt (P : Parameters) (D : Plan P) (key : List Bool→List Bool)
    (hpos : ∀q,0<count P D key q) (q : List Bool) : row P D key q<count P D key q :=by
  have H:=hpos q
  have R:=min_le_right (Nat.fromBitsLE (SquareSampleInput.indexWord q)) (count P D key q-1)
  unfold row
  omega

end LeanCanny.Algebra.IntegralMixedFramedPhysicalRowReaderBits
