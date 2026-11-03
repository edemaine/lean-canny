/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightMatrix
/-! # Current native affine packets are literal old-basis entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedOldHeightBits (state bankFamily)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedCurrentQNativeBits.machine

noncomputable def sourceEntry (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (affine : IntegralMixedHistory.AffineExpr) (r t : ℕ) : ℤ :=
  let x := (bankFamily P D J).state key
  if hv : r<count ((bankFamily P D J).birth key) ((bankFamily P D J).width key) ∧
      t<count ((bankFamily P D J).birth key) ((bankFamily P D J).width key) then
    Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis (IntegralMixedHistory.expression x affine)
      ⟨r,hv.1⟩ ⟨t,hv.2⟩ else 0

theorem family_matrix_source (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hq : Active P q)
    (r t : Fin (count ((family P D J).arity q) ((family P D J).width q))) :
    (family P D J).matrix q r t=sourceEntry P D J (IntegralMixedVirtualTaskBits.saved P q)
      (IntegralMixedFramedScalarCellsBits.affine P D J q) r.val t.val := by
  rw [matrix_active P D J q hq]
  unfold sourceEntry
  rw [dite_eq_left (show r.val<count ((bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q))
      ((bankFamily P D J).width (IntegralMixedVirtualTaskBits.saved P q)) ∧
      t.val<count ((bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q))
      ((bankFamily P D J).width (IntegralMixedVirtualTaskBits.saved P q)) from ⟨r.isLt,t.isLt⟩)]
  rfl

theorem affine_value_source (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (q : List Bool) (hq : Active P q) :
    IntegralMixedFramedPhysicalAffineBits.value P a D J c q=residueBits
      (sourceEntry P D J (IntegralMixedVirtualTaskBits.saved P q) (IntegralMixedFramedScalarCellsBits.affine P D J q)
        (IntegralMixedHeightTableQueryBits.oldRow P q) (IntegralMixedHeightTableQueryBits.oldCol P q) : ZMod (modulus P q)) := by
  rw [IntegralMixedFramedPhysicalAffineBits.value_matrix_at P a D J c q hq.1 (by rw [hq.2];omega)]
  unfold sourceEntry
  rw [dite_eq_left (show IntegralMixedHeightTableQueryBits.oldRow P q<count ((bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q))
      ((bankFamily P D J).width (IntegralMixedVirtualTaskBits.saved P q)) ∧
      IntegralMixedHeightTableQueryBits.oldCol P q<count ((bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q))
      ((bankFamily P D J).width (IntegralMixedVirtualTaskBits.saved P q)) from
    ⟨(IntegralMixedFramedHeightTableMatrixBits.row P D J q).isLt,(IntegralMixedFramedHeightTableMatrixBits.col P D J q).isLt⟩)]
  rfl

theorem entry_packet (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (q mw : List Bool) (r t : Fin (count ((family P D J).arity q) ((family P D J).width q))) :
    entry P a D J c (pair (pair q mw)
      (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))=
      residueBits ((family P D J).matrix q r t : ZMod (modulus P q)) := by
  let z:=pair (pair q mw)
    (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))
  have HP : parent z=q := by simp only [z,parent,pairFst_pair]
  by_cases hq : Active P q
  · rw [entry,HP,ite_eq_left hq,affine_value_source P a D J c (query P z) (query_active P z (HP.symm ▸ hq))]
    have HQ:=query_indices P D J q mw r t hq
    have HX : get P .slot15 (query P z)=1 := (query_active P z (HP.symm ▸ hq)).2
    have HD : count ((family P D J).arity q) ((family P D J).width q)=
        IntegralMixedOldHeightBits.dimension P (query P z) := by
      rw [arity_eq,width_eq]
      unfold IntegralMixedOldHeightBits.dimension
      simp only [query,z,parent,IntegralCriticalFlatMatrixQuery.writer_birth,IntegralCriticalFlatMatrixQuery.writer_root,pairFst_pair]
    have HR : IntegralMixedHeightTableQueryBits.oldRow P (query P z)=r.val := by
      rw [IntegralMixedHeightTableQueryBits.oldRow,HX,ite_eq_left rfl,HQ.1]
      exact Nat.mod_eq_of_lt (r.isLt.trans_eq HD)
    have HT : IntegralMixedHeightTableQueryBits.oldCol P (query P z)=t.val := by
      rw [IntegralMixedHeightTableQueryBits.oldCol,HX,ite_eq_left rfl,HQ.2]
      exact Nat.mod_eq_of_lt (t.isLt.trans_eq HD)
    have HM : modulus P (query P z)=modulus P q := by
      unfold query
      rw [IntegralCriticalFlatMatrixQuery.writer_modulus,pairFst_pair,HP]
    rw [HR,HT,query_saved,query_affine,HP,HM,←family_matrix_source P D J q hq]
  · rw [entry,HP,ite_eq_right hq,matrix_inactive P D J q hq]
    simp only [Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

end LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightBits
