/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockLayout
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightAtSpace
public import LeanCanny.Algebra.FixedWidthEmbeddingSpace
/-! # Ancestral affine heights occupy exactly the old full columns -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FixedWidthRowBits.value MvPolynomial.rename

noncomputable def heightPolynomial (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (base : List Bool→List Bool) (q : List Bool) :=
  MvPolynomial.rename (oldIndex P D J base q) (IntegralMixedFramedPhysicalHeightBits.fullPolynomial P D J T hr (base q))

theorem oldReader_packet (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (base : List Bool→List Bool) (q : List Bool) (i : Fin (oldCount P D base q)) :
    oldReader (pair q (BinaryNatCode.encode i.val))=BinaryNatCode.encode (oldIndex P D J base q i).val := by
  simp only [oldReader,oldIndex,pairSnd_pair]

theorem height_evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (hc : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c)
    (base : List Bool→List Bool) (hb : base∈FP) (V : List Bool→ℕ) (hV : UnaryFn V)
    (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fullCount P D J base) V
      (heightPolynomial P D J c.critical.tables c.critical.represents base) target
      (IntegralMixedFramedPhysicalHeightBits.modulusWord P∘base)) := by
  have HO:=oldCount_unary P a D J c base hb
  have HN:=fullCount_unary P a D J c base hb
  exact FixedWidthEmbeddingBits.evaluator (oldCount P D base) (fullCount P D J base) V target oldReader
    (fun q=>IntegralMixedFramedPhysicalHeightBits.fullPolynomial P D J c.critical.tables c.critical.represents (base q))
    (oldIndex P D J base) (oldIndex_injective P D J base) (oldReader_packet P D J base)
    _ HO HN hV ht pairSnd_mem_FP (IntegralMixedFramedPhysicalHeightAtBits.full_evaluator P a D J c hc base hb V hV _
      (FixedWidthEmbeddingBits.word_FP _ _ _ _ _ HO HN hV ht pairSnd_mem_FP))

end LeanCanny.Algebra.IntegralMixedFramedPhysicalBlockBits
