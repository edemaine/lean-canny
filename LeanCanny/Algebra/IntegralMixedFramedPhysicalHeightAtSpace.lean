/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightFullSpace
public import LeanCanny.Algebra.IntegralCoordinateFamilyPullSpace
/-! # Full physical heights retain arbitrary external exponent words

An FP base writer chooses the literal source task. Matrix ranks alone are
put in recursive fields; exponent-query blocks stay in the outer datum.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightAtBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedPhysicalHeightBits (family modulusWord arity_unary width_unary columns)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedPhysicalHeightBits.entry
  IntegralMixedFramedPhysicalHeightBits.family IntegralMixedFramedPhysicalAffineBits.value
  IntegralMixedFramedCurrentQNativeBits.machine

theorem entry_packet (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (q : List Bool) (r t : Fin (count ((family P D J).arity q) ((family P D J).width q))) :
    IntegralMixedFramedPhysicalHeightBits.entry P a D J c (pair (pair q (modulusWord P q))
      (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))=
      residueBits ((family P D J).matrix q r t : ZMod (Nat.fromBitsLE (modulusWord P q)+1)) := by
  have HE:=IntegralMixedFramedPhysicalHeightBits.entry_packet P a D J c q (modulusWord P q) r t
  exact HE.trans (congrArg₂ (fun (v : ℤ) (m : ℕ)=>residueBits (v : ZMod m)) rfl
    (IntegralMixedFramedPhysicalHeightBits.modulusWord_value P q).symm)

theorem powered_evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (hc : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c)
    (base : List Bool→List Bool) (hb : base∈FP) (V : List Bool→ℕ) (hV : UnaryFn V)
    (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value ((family P D J).pull base).arity V
      (((family P D J).pull base).poweredPolynomial (fun q=>P.cap (RankedHistoryTask.root (base q))+1))
      target (modulusWord P∘base)) :=
  IntegralCoordinateCoefficientBits.powered_pull_evaluator (family P D J) base hb
    (fun q=>P.cap (RankedHistoryTask.root q)+1) V target (modulusWord P)
    (IntegralMixedFramedPhysicalHeightBits.entry P a D J c) (arity_unary P a D J) (width_unary P a D J)
    ((a.cap.comp RankedHistoryTask.root_FP).add (UnaryFn.const 1)) hV ht
    (IntegralMixedFramedPhysicalHeightBits.modulusWord_FP P a)
    (IntegralMixedFramedPhysicalHeightBits.entry_space P a D J c hc) (entry_packet P a D J c)

 def index (P : Parameters) (T : IntegralMixedHeaderTablesBits.Tables) (base : List Bool→List Bool) (p : List Bool) :=
  IntegralMixedFramedFullScalarRowBits.columnReader P T (IntegralMixedVirtualTaskBits.saved P)
    (pair (base (pairFst p)) (pairSnd p))

attribute [local irreducible] index IntegralMixedFramedFullScalarRowBits.columnReader

theorem index_FP (P : Parameters) (a : Access P) (T : IntegralMixedHeaderTablesBits.Tables)
    (hT : IntegralMixedHeaderTablesBits.Access T) (base : List Bool→List Bool) (hb : base∈FP) : index P T base∈FP :=
  mem_FP_of_eq (mem_FP_comp (f:=fun p=>pair (base (pairFst p)) (pairSnd p))
    (g:=IntegralMixedFramedFullScalarRowBits.columnReader P T (IntegralMixedVirtualTaskBits.saved P))
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP hb) pairSnd_mem_FP)
    (IntegralMixedFramedFullScalarRowBits.columnReader_FP P a T hT _ (IntegralMixedVirtualTaskBits.saved_FP P a))) (fun _=>by unfold index; rfl)

theorem full_evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (hc : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c)
    (base : List Bool→List Bool) (hb : base∈FP) (V : List Bool→ℕ) (hV : UnaryFn V)
    (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value
      (IntegralMixedFramedFullScalarRowBits.fullCount P D (IntegralMixedVirtualTaskBits.saved P)∘base) V
      (fun q=>IntegralMixedFramedPhysicalHeightBits.fullPolynomial P D J c.critical.tables c.critical.represents (base q))
      target (modulusWord P∘base)) := by
  let A:=((family P D J).pull base).arity
  let N:=IntegralMixedFramedFullScalarRowBits.fullCount P D (IntegralMixedVirtualTaskBits.saved P)∘base
  have HA : UnaryFn A:=(arity_unary P a D J).comp hb
  have HN : UnaryFn N:=(IntegralMixedFramedFullScalarRowBits.fullCount_unary P a D J c.critical.tables
    c.critical.native c.critical.represents _ (IntegralMixedVirtualTaskBits.saved_FP P a)).comp hb
  have HI:=index_FP P a c.critical.tables c.critical.native base hb
  apply FixedWidthEmbeddingBits.evaluator A N V target (index P c.critical.tables base)
    (((family P D J).pull base).poweredPolynomial (fun q=>P.cap (RankedHistoryTask.root (base q))+1))
    (fun q=>columns P D J c.critical.tables c.critical.represents (base q))
    (fun q=>IntegralMixedFramedPhysicalHeightBits.columns_injective P D J _ _ (base q))
    (fun q i=>?_) (modulusWord P∘base) HA HN hV ht HI
    (powered_evaluator P a D J c hc base hb V hV _ (FixedWidthEmbeddingBits.word_FP _ _ _ _ _ HA HN hV ht HI))
  simp only [index,pairFst_pair,pairSnd_pair]
  exact IntegralMixedFramedPhysicalHeightBits.column_packet P D J _ _ (base q) i

end LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightAtBits
