/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedAffineCoefficientSpace
public import LeanCanny.Algebra.IntegralMixedFullScalarMachines
public import LeanCanny.Algebra.IntegralMixedCommandHeaderNative
public import LeanCanny.Algebra.SignedIntegerResidue
/-! # Literal immutable rule bodies behind the scalar cell interface

The body writer serializes original affine syntax and integer literals.
Its agreement contract never mentions the interpreted bank or a matrix value.
Constructing it from a concrete input frontend remains an explicit obligation.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedOriginalRuleBodyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def physicalRule (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) :=
  (IntegralMixedHeightCellsBits.physicalFamily P D).rule key
noncomputable def virtualRule (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) :=
  (IntegralMixedFullHistoryFamilyBits.family P D).rule key

noncomputable def encode (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) : List Bool :=
  WordList.encode [SignStatisticBits.integerCode (D.spatial (pairFst key)).leading,
    WordList.encode (List.ofFn (fun i => IntegralMixedAffineCode.encode ((physicalRule P D key).heights i))),
    WordList.encode (List.ofFn (fun i => SignStatisticBits.integerCode ((physicalRule P D key).scales i))),
    WordList.encode (List.ofFn (fun i => IntegralMixedAffineCode.encode ((virtualRule P D key).critical.heights i))),
    WordList.encode (List.ofFn (fun i => SignStatisticBits.integerCode ((virtualRule P D key).critical.scales i))),
    BinaryNatCode.encode (virtualRule P D key).height.val,
    SignStatisticBits.integerCode (virtualRule P D key).slope]

structure Access (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) where
  writer : List Bool → List Bool
  writer_FP : writer ∈ FP
  agrees : ∀ key, writer key = encode P D key

def field (body : List Bool → List Bool) (i : ℕ) (key : List Bool) := WordList.get (body key) i

theorem field_FP (body : List Bool → List Bool) (hb : body ∈ FP) (i : ℕ) : field body i ∈ FP :=
  mem_FP_comp (f := body) (g := fun w => WordList.get w i) hb (IntegralMixedCommandHeaderBits.get_FP i)

theorem leading_field (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (key : List Bool) :
    field h.writer 0 key = SignStatisticBits.integerCode (D.spatial (pairFst key)).leading := by
  simp only [field, h.agrees, encode, WordList.get_encode, List.getElem?_cons_zero, Option.getD_some]

theorem physical_heights (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (key : List Bool) :
    field h.writer 1 key = WordList.encode (List.ofFn (fun i => IntegralMixedAffineCode.encode ((physicalRule P D key).heights i))) := by
  simp only [field, h.agrees, encode, WordList.get_encode, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]

theorem physical_scales (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (key : List Bool) :
    field h.writer 2 key = WordList.encode (List.ofFn (fun i => SignStatisticBits.integerCode ((physicalRule P D key).scales i))) := by
  simp only [field, h.agrees, encode, WordList.get_encode, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]

theorem virtual_heights (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (key : List Bool) :
    field h.writer 3 key = WordList.encode (List.ofFn (fun i => IntegralMixedAffineCode.encode ((virtualRule P D key).critical.heights i))) := by
  simp only [field, h.agrees, encode, WordList.get_encode, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]

theorem virtual_scales (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (key : List Bool) :
    field h.writer 4 key = WordList.encode (List.ofFn (fun i => SignStatisticBits.integerCode ((virtualRule P D key).critical.scales i))) := by
  simp only [field, h.agrees, encode, WordList.get_encode, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]

theorem height_field (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (key : List Bool) :
    field h.writer 5 key = BinaryNatCode.encode (virtualRule P D key).height.val := by
  simp only [field, h.agrees, encode, WordList.get_encode, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]

theorem slope_field (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (key : List Bool) :
    field h.writer 6 key = SignStatisticBits.integerCode (virtualRule P D key).slope := by
  simp only [field, h.agrees, encode, WordList.get_encode, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
end LeanCanny.Algebra.IntegralMixedOriginalRuleBodyBits
