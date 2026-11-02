/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeSpace
public import LeanCanny.Algebra.IntegralMixedFramedNativeSyntax

/-! # Original literal scalar controls enter the current-Q controller

The current-Q mode is disabled for literal slopes. Their existing original
cell program supplies the multiplier, while the critical, normalization and
producer controls retain the same script. No bank quantity is serialized.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQFromOriginal
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedScalarCellsBits.reader IntegralMixedFramedScalarCellsBits.cell

noncomputable def height (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedScalarCellsBits.Primitive P D H) : IntegralMixedFramedCurrentQHeightBits.Controls P D H where
  low.read tag _:=IntegralMixedFramedHeightCellAccessBits.read_space P D H h tag
  current _:=false
  current_FP:=constFn_mem_FP [false]
  multiplier q:=IntegralMixedFramedScalarCellsBits.cell P D H q 3 0
  multiplier_space:=by
    have HQ : (fun q=>pair q (pair (BinaryNatCode.encode 3) (BinaryNatCode.encode 0)))∈FP :=
      mem_FP_pair id_mem_FP (constFn_mem_FP _)
    exact (h.precompose _ HQ).congr (funext fun q=>IntegralMixedFramedScalarCellsBits.reader_packet P D H q 3 0)
  slope _:=by simp only [Bool.false_eq_true,ite_false,one_mul]

noncomputable def scalar (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedFullScalarBits.Controls P D H) : IntegralMixedFramedCurrentQScalarBits.Controls P D H where
  tables:=h.tables
  native:=h.native
  represents:=h.represents
  leading:=h.leading
  physicalScales:=h.physicalScales
  virtualScales:=h.virtualScales
  height:=height P D H h.height

noncomputable def controls (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedNativeBits.Controls P D H) : IntegralMixedFramedCurrentQNativeBits.Controls P D H where
  scalar:=scalar P D H h.scalar
  critical:=h.critical
  normalization:=h.normalization
  producer:=h.producer

theorem bounds (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedNativeBits.Controls P D H) (hb : IntegralMixedFramedNativeBits.Bounds P D H h) :
    IntegralMixedFramedCurrentQNativeBits.Bounds P D H (controls P D H h) :=
  ⟨hb.original,hb.factor,hb.fallback,hb.modulus⟩

noncomputable def ofSyntax (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : IntegralMixedFramedNativeBits.Syntax P D H) :=
  controls P D H (IntegralMixedFramedNativeBits.Controls.ofSyntax P a D H s)

theorem syntax_bounds (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hb : IntegralMixedFramedNativeBits.Bounds P D H (IntegralMixedFramedNativeBits.Controls.ofSyntax P a D H s)) :
    IntegralMixedFramedCurrentQNativeBits.Bounds P D H (ofSyntax P a D H s) :=
  bounds P D H _ hb

end LeanCanny.Algebra.IntegralMixedFramedCurrentQFromOriginal
