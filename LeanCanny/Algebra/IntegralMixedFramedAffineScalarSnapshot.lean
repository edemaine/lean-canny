/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalScalarRecipe
public import LeanCanny.Algebra.IntegralMixedOriginalHeightCells
public import LeanCanny.Algebra.IntegralMixedFramedScalarCells
/-! # General affine snapshots for actual changing-source scalar cells

Literal original heights may be affine sums and midpoint numerators. Scales
may be two. Spatial leading coefficients remain unrestricted. Original header
access and leading residues are charged separately by the scalar controller.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedAffineScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
noncomputable abbrev physicalRule (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :=
  (IntegralMixedFramedScalarCellsBits.physicalFamily P D J).rule key
noncomputable abbrev virtualRule (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :=
  (IntegralMixedFramedScalarCellsBits.virtualFamily P D J).rule key
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Snapshot (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    {F : Inputs} (L : FlatAffineExceptionalScalarRecipe.Layout F)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (physicalDouble virtualDouble : List Bool → Bool) : Prop where
  physicalScales : ∀ q (i : Fin (IntegralMixedOriginalRuleBodyBits.arity P q)),
    (physicalRule P D J (IntegralMixedVirtualTaskBits.saved P q)).scales i = if physicalDouble q then 2 else 1
  virtualScales : ∀ q (i : Fin (IntegralMixedOriginalRuleBodyBits.arity P q)),
    (virtualRule P D J (IntegralMixedVirtualTaskBits.saved P q)).critical.scales i = if virtualDouble q then 2 else 1
  affine : ∀ q, IntegralMixedFramedScalarCellsBits.affine P D J q = FlatAffineExceptionalScalarRecipe.expression L q
  height : ∀ q, (virtualRule P D J (IntegralMixedVirtualTaskBits.saved P q)).height.val =
    if L.sweep q then ((FlatAffineExceptionalOrderedRule.order F (L.input q)).symm (L.height (L.input q))).val else 0
  slope : ∀ q, (virtualRule P D J (IntegralMixedVirtualTaskBits.saved P q)).slope =
    if L.sweep q then FlatAffineExceptionalBankSource.denominator F C L.height (L.input q) else 1

def literalScale (P : Parameters) (double : List Bool → Bool) (q : List Bool) (i : ℕ) : ℤ :=
  if i < IntegralMixedOriginalRuleBodyBits.arity P q then if double q then 2 else 1 else 1

def scaleCode (P : Parameters) (double : List Bool → Bool) (z : List Bool) :=
  SignStatisticBits.integerCode (literalScale P double (pairFst z) (Nat.fromBitsLE (pairSnd z)))

theorem scaleCode_FP (P : Parameters) (a : Access P) (double : List Bool → Bool)
    (hd : (fun q => [double q]) ∈ FP) : scaleCode P double ∈ FP := by
  have HP := FPPred.of_flag hd
  have HC := (HP.comp pairFst_mem_FP).ite_mem_FP
    (constFn_mem_FP (SignStatisticBits.integerCode 2)) (constFn_mem_FP (SignStatisticBits.integerCode 1))
  have HB := (BinaryFn.fromBits pairSnd_mem_FP).lt
    ((BinaryFn.ofUnary (IntegralMixedOriginalRuleBodyBits.arity_unary P a)).comp pairFst_mem_FP)
  have H := HB.ite_mem_FP HC (constFn_mem_FP (SignStatisticBits.integerCode 1))
  exact mem_FP_of_eq H (fun z => by simp only [scaleCode, literalScale, Function.comp_apply]; split_ifs <;> rfl)

attribute [local irreducible] modulus

theorem physical_scale_eq (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    {F : Inputs} (L : FlatAffineExceptionalScalarRecipe.Layout F) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (pd vd : List Bool → Bool) (h : Snapshot P D J L C pd vd) (q : List Bool) (i : ℕ) :
    IntegralMixedPhysicalDenominatorPostBits.scale P (IntegralMixedFramedScalarCellsBits.physicalFamily P D J) q i = literalScale P pd q i := by
  change (if hi : i < IntegralMixedOriginalRuleBodyBits.arity P q then
    (physicalRule P D J (IntegralMixedVirtualTaskBits.saved P q)).scales ⟨i, hi⟩ else 1) = _
  unfold literalScale
  by_cases hi : i < IntegralMixedOriginalRuleBodyBits.arity P q
  · rw [dite_eq_left hi, ite_eq_left hi]
    exact h.physicalScales q ⟨i, hi⟩
  · rw [dite_eq_right hi, ite_eq_right hi]

theorem virtual_scale_eq (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    {F : Inputs} (L : FlatAffineExceptionalScalarRecipe.Layout F) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (pd vd : List Bool → Bool) (h : Snapshot P D J L C pd vd) (q : List Bool) (i : ℕ) :
    IntegralMixedVirtualDenominatorPostBits.scale P (IntegralMixedFramedHistoryFamilyBits.family P D J) q i = literalScale P vd q i := by
  change (if hi : i < IntegralMixedOriginalRuleBodyBits.arity P q then
    (virtualRule P D J (IntegralMixedVirtualTaskBits.saved P q)).critical.scales ⟨i, hi⟩ else 1) = _
  unfold literalScale
  by_cases hi : i < IntegralMixedOriginalRuleBodyBits.arity P q
  · rw [dite_eq_left hi, ite_eq_left hi]
    exact h.virtualScales q ⟨i, hi⟩
  · rw [dite_eq_right hi, ite_eq_right hi]

theorem literal_scale_space (P : Parameters) (a : Access P) (double : List Bool → Bool)
    (hd : (fun q => [double q]) ∈ FP) :
    SpaceFunction (fun z => residueBits (literalScale P double (pairFst z) (Nat.fromBitsLE (pairSnd z)) : ZMod (modulus P (pairFst z)))) :=
  IntegralMixedOriginalRuleBodyBits.residue_space (scaleCode P double) (scaleCode_FP P a double hd) (fun _ => rfl)
    (fun z => modulus P (pairFst z)) ((modulus_binary P a).comp pairFst_mem_FP)
    (fun z => Nat.pos_of_ne_zero (modulus_ne_zero P (pairFst z)))

theorem physical_scales_primitive (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    {F : Inputs} (L : FlatAffineExceptionalScalarRecipe.Layout F) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (pd vd : List Bool → Bool) (hpd : (fun q => [pd q]) ∈ FP) (h : Snapshot P D J L C pd vd) :
    IntegralMixedPhysicalNativeDenominatorBits.Primitive P (IntegralMixedFramedScalarCellsBits.physicalFamily P D J) := by
  apply (literal_scale_space P a pd hpd).congr
  funext z
  change residueBits (_ : ZMod _) = residueBits ((IntegralMixedPhysicalDenominatorPostBits.scale P (IntegralMixedFramedScalarCellsBits.physicalFamily P D J) (pairFst z) (Nat.fromBitsLE (pairSnd z)) : ℤ) : ZMod (modulus P (pairFst z)))
  rw [physical_scale_eq P D J L C pd vd h]

theorem virtual_scales_primitive (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    {F : Inputs} (L : FlatAffineExceptionalScalarRecipe.Layout F) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (pd vd : List Bool → Bool) (hvd : (fun q => [vd q]) ∈ FP) (h : Snapshot P D J L C pd vd) :
    IntegralMixedVirtualContextDenominatorBits.Primitive P (IntegralMixedFramedHistoryFamilyBits.family P D J) := by
  apply (literal_scale_space P a vd hvd).congr
  funext z
  change residueBits (_ : ZMod _) = residueBits ((IntegralMixedVirtualDenominatorPostBits.scale P (IntegralMixedFramedHistoryFamilyBits.family P D J) (pairFst z) (Nat.fromBitsLE (pairSnd z)) : ℤ) : ZMod (modulus P (pairFst z)))
  rw [virtual_scale_eq P D J L C pd vd h]

theorem slope_cell_eq (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    {F : Inputs} (L : FlatAffineExceptionalScalarRecipe.Layout F) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (pd vd : List Bool → Bool) (h : Snapshot P D J L C pd vd) (q : List Bool) (i : ℕ) :
    IntegralMixedFramedScalarCellsBits.cell P D J q 3 i = FlatAffineExceptionalScalarRecipe.slope L C (get P .slot8) q := by
  change (if get P .slot8 q = (virtualRule P D J (IntegralMixedVirtualTaskBits.saved P q)).height.val then
    (virtualRule P D J (IntegralMixedVirtualTaskBits.saved P q)).slope else 0) = _
  rw [h.height, h.slope]
  unfold FlatAffineExceptionalScalarRecipe.slope
  cases L.sweep q <;> simp only [Bool.false_eq_true, ite_false, ite_true]
end LeanCanny.Algebra.IntegralMixedFramedAffineScalarBits
