/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSuppliedScalarSnapshot
/-! # Supplied-mask full-history affine and sweep cells from original source access -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSuppliedScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open FlatAffineFullSourceTower (Inputs)
open FlatAffineCompleteRootStages (next)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] modulus IntegralMixedHeightCellsBits.affine

theorem constant_cell_space (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    {F : Inputs} (hF : F.Access) (L : FlatAffineExceptionalSuppliedRecipe.Layout F) (hL : FlatAffineExceptionalSuppliedRecipe.Access L)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (pd vd : List Bool → Bool) (h : Snapshot P D L C pd vd) :
    SpaceFunction (fun z => residueBits (IntegralMixedAffineCoefficients.constantCoefficient (IntegralMixedHeightCellsBits.affine P D (pairFst z)) : ZMod (modulus P (pairFst z)))) := by
  have HS := (FlatAffineExceptionalSuppliedRecipe.syntax_space hF L hL).precompose pairFst pairFst_mem_FP
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  have H := IntegralMixedAffineCode.constant_space_fromSpace
    (fun z => IntegralMixedHeightCellsBits.affine P D (pairFst z))
    (fun z => FlatAffineExceptionalSuppliedRecipe.word L (pairFst z))
    (fun z => BinaryNatCode.encode (modulus P (pairFst z) - 1)) HS
    ((HM.sub (BinaryFn.const 1)).bits_mem_FP)
    (fun z => by rw [h.affine]; rfl)
  apply H.congr
  funext z
  exact congrArg (fun m => residueBits (IntegralMixedAffineCoefficients.constantCoefficient (IntegralMixedHeightCellsBits.affine P D (pairFst z)) : ZMod m)) (by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel (Nat.pos_of_ne_zero (modulus_ne_zero P (pairFst z)))])

theorem reference_cell_space (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    {F : Inputs} (hF : F.Access) (L : FlatAffineExceptionalSuppliedRecipe.Layout F) (hL : FlatAffineExceptionalSuppliedRecipe.Access L)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (pd vd : List Bool → Bool) (h : Snapshot P D L C pd vd) :
    SpaceFunction (fun z => residueBits (IntegralMixedAffineCoefficients.referenceCoefficient (IntegralMixedHeightCellsBits.affine P D (pairFst z))
      (Nat.fromBitsLE (pairSnd (pairSnd z))) : ZMod (modulus P (pairFst z)))) := by
  have HS := (FlatAffineExceptionalSuppliedRecipe.syntax_space hF L hL).precompose pairFst pairFst_mem_FP
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  have HJ : BinaryFn (fun z => Nat.fromBitsLE (pairSnd (pairSnd z))) := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have H := IntegralMixedAffineCode.reference_space_fromSpace
    (fun z => IntegralMixedHeightCellsBits.affine P D (pairFst z))
    (fun z => FlatAffineExceptionalSuppliedRecipe.word L (pairFst z))
    (fun z => BinaryNatCode.encode (modulus P (pairFst z) - 1)) (fun z => Nat.fromBitsLE (pairSnd (pairSnd z))) HS
    ((HM.sub (BinaryFn.const 1)).bits_mem_FP) HJ
    (fun z => by rw [h.affine]; rfl)
  apply H.congr
  funext z
  exact congrArg (fun m => residueBits (IntegralMixedAffineCoefficients.referenceCoefficient (IntegralMixedHeightCellsBits.affine P D (pairFst z))
    (Nat.fromBitsLE (pairSnd (pairSnd z))) : ZMod m)) (by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel (Nat.pos_of_ne_zero (modulus_ne_zero P (pairFst z)))])

def selectedDouble (P : Parameters) (pd vd : List Bool → Bool) (q : List Bool) : Bool :=
  if get P .slot15 q = 1 then pd q else vd q

theorem selectedDouble_FP (P : Parameters) (a : Access P) (pd vd : List Bool → Bool)
    (hp : (fun q => [pd q]) ∈ FP) (hv : (fun q => [vd q]) ∈ FP) : (fun q => [selectedDouble P pd vd q]) ∈ FP :=
  mem_FP_of_eq (((get_binary P a .slot15).eq (BinaryFn.const 1)).ite_mem_FP hp hv) (fun q => by unfold selectedDouble; split_ifs <;> rfl)

theorem scale_cell_eq (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    {F : Inputs} (L : FlatAffineExceptionalSuppliedRecipe.Layout F) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (pd vd : List Bool → Bool) (h : Snapshot P D L C pd vd) (q : List Bool) (i : ℕ) :
    IntegralMixedHeightCellsBits.cell P D q 2 i = literalScale P (selectedDouble P pd vd) q i := by
  change (if hi : i < IntegralMixedOriginalRuleBodyBits.arity P q then
    (IntegralMixedHeightCellsBits.rule P D (IntegralMixedVirtualTaskBits.saved P q)).scales ⟨i, hi⟩ else 1) = _
  unfold literalScale
  by_cases hi : i < IntegralMixedOriginalRuleBodyBits.arity P q
  · rw [dite_eq_left hi, ite_eq_left hi]
    by_cases hc : get P .slot15 q = 1
    · rw [IntegralMixedHeightCellsBits.rule_physical P D q hc]
      exact (h.physicalScales q ⟨i, hi⟩).trans (by simp only [selectedDouble, hc, ite_true])
    · rw [IntegralMixedHeightCellsBits.rule_virtual P D q hc]
      exact (h.virtualScales q ⟨i, hi⟩).trans (by simp only [selectedDouble, hc, ite_false])
  · rw [dite_eq_right hi, ite_eq_right hi]

theorem scale_cell_space (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    {F : Inputs} (L : FlatAffineExceptionalSuppliedRecipe.Layout F) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (pd vd : List Bool → Bool) (hp : (fun q => [pd q]) ∈ FP) (hv : (fun q => [vd q]) ∈ FP) (h : Snapshot P D L C pd vd) :
    SpaceFunction (fun z => residueBits (IntegralMixedHeightCellsBits.cell P D (pairFst z) 2 (Nat.fromBitsLE (pairSnd (pairSnd z))) : ZMod (modulus P (pairFst z)))) := by
  have H := (literal_scale_space P a (selectedDouble P pd vd) (selectedDouble_FP P a pd vd hp hv)).precompose
    IntegralMixedOriginalRuleBodyBits.indexPacket IntegralMixedOriginalRuleBodyBits.indexPacket_FP
  apply H.congr
  funext z
  change residueBits (literalScale P (selectedDouble P pd vd)
    (pairFst (pair (pairFst z) (pairSnd (pairSnd z))))
    (Nat.fromBitsLE (pairSnd (pair (pairFst z) (pairSnd (pairSnd z))))) : ZMod (modulus P (pairFst (pair (pairFst z) (pairSnd (pairSnd z)))))) = _
  exact (congrArg₂ (fun (q : List Bool) (i : ℕ) => residueBits (literalScale P (selectedDouble P pd vd) q i : ZMod (modulus P q)))
    (pairFst_pair _ _) (congrArg Nat.fromBitsLE (pairSnd_pair _ _))).trans
      (congrArg (fun x : ℤ => residueBits (x : ZMod (modulus P (pairFst z)))) (scale_cell_eq P D L C pd vd h _ _).symm)

theorem slope_cell_space (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    {F : Inputs} (hF : F.Access) (L : FlatAffineExceptionalSuppliedRecipe.Layout F) (hL : FlatAffineExceptionalSuppliedRecipe.Access L)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (pd vd : List Bool → Bool) (h : Snapshot P D L C pd vd) :
    SpaceFunction (fun z => residueBits (IntegralMixedHeightCellsBits.cell P D (pairFst z) 3 (Nat.fromBitsLE (pairSnd (pairSnd z))) : ZMod (modulus P (pairFst z)))) := by
  have H0 := FlatAffineExceptionalSuppliedRecipe.slope_space hF L hL C (get P .slot8) (get_binary P a .slot8)
    (fun q => BinaryNatCode.encode (modulus P q - 1)) ((modulus_binary P a).sub (BinaryFn.const 1)).bits_mem_FP
  have H1 : SpaceFunction (fun q => residueBits (FlatAffineExceptionalSuppliedRecipe.slope L C (get P .slot8) q : ZMod (modulus P q))) := by
    apply H0.congr
    funext q
    exact congrArg (fun m => residueBits (FlatAffineExceptionalSuppliedRecipe.slope L C (get P .slot8) q : ZMod m)) (by
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel (Nat.pos_of_ne_zero (modulus_ne_zero P q))])
  apply (H1.precompose pairFst pairFst_mem_FP).congr
  funext z
  exact congrArg (fun x : ℤ => residueBits (x : ZMod (modulus P (pairFst z)))) (slope_cell_eq P D L C pd vd h _ _).symm

theorem height_primitive (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    {F : Inputs} (hF : F.Access) (L : FlatAffineExceptionalSuppliedRecipe.Layout F) (hL : FlatAffineExceptionalSuppliedRecipe.Access L)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (pd vd : List Bool → Bool)
    (hp : (fun q => [pd q]) ∈ FP) (hv : (fun q => [vd q]) ∈ FP) (h : Snapshot P D L C pd vd) :
    IntegralMixedHeightCellsBits.Primitive P D := by
  let tag := fun z => Nat.fromBitsLE (pairFst (pairSnd z))
  have HT : BinaryFn tag := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have HZ := SpaceFunction.ofFP (fun _ : List Bool => []) (constFn_mem_FP [])
  have H3 := SpaceFunction.branch (fun z => decide (tag z = 3)) (HT.eq (BinaryFn.const 3)).flag_mem_FP (slope_cell_space P a D hF L hL C pd vd h) HZ
  have H2 := SpaceFunction.branch (fun z => decide (tag z = 2)) (HT.eq (BinaryFn.const 2)).flag_mem_FP (scale_cell_space P a D L C pd vd hp hv h) H3
  have H1 := SpaceFunction.branch (fun z => decide (tag z = 1)) (HT.eq (BinaryFn.const 1)).flag_mem_FP (reference_cell_space P a D hF L hL C pd vd h) H2
  have H0 := SpaceFunction.branch (fun z => decide (tag z = 0)) (HT.eq (BinaryFn.const 0)).flag_mem_FP (constant_cell_space P a D hF L hL C pd vd h) H1
  apply H0.congr
  funext z
  unfold IntegralMixedHeightCellsBits.reader
  dsimp only [tag]
  simp only [decide_eq_true_eq]
  split_ifs with h0 h1 h2 h3
  · rw [h0]; rfl
  · rw [h1]; rfl
  · rw [h2]
  · rw [h3]
  · simp only [IntegralMixedHeightCellsBits.cell, h0, h1, h2, h3, ite_false]
    simpa only [ArithmeticBits.zero, Int.cast_zero] using ArithmeticBits.zero_residueBits (modulus P (pairFst z))

theorem controls (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    {F : Inputs} (hF : F.Access) (L : FlatAffineExceptionalSuppliedRecipe.Layout F) (hL : FlatAffineExceptionalSuppliedRecipe.Access L)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (pd vd : List Bool → Bool)
    (hp : (fun q => [pd q]) ∈ FP) (hv : (fun q => [vd q]) ∈ FP) (h : Snapshot P D L C pd vd)
    (full : IntegralMixedFullHistoryFamilyBits.Metadata P D)
    (physical : IntegralMixedPhysicalQueryBits.InputMetadata (IntegralMixedFullScalarBits.physicalFamily P D)) :
    IntegralMixedFullScalarBits.Controls P D where
  full := full
  physical := physical
  leading := leading_primitive P a D L C pd vd h
  physicalScales := physical_scales_primitive P a D L C pd vd hp h
  virtualScales := virtual_scales_primitive P a D L C pd vd hv h
  height := height_primitive P a D hF L hL C pd vd hp hv h
end LeanCanny.Algebra.IntegralMixedSuppliedScalarBits
