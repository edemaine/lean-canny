/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightCoefficientSpace
public import LeanCanny.Algebra.IntegralMixedFramedFullScalarRowSpace
/-! # Physical affine height coefficients in the full oldest-first columns -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan commands)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def columns (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (q : List Bool) : Fin ((family P D J).arity q)→
      Fin (IntegralMixedFramedFullScalarRowBits.fullCount P D (IntegralMixedVirtualTaskBits.saved P) q) :=
  IntegralMixedFramedPhysicalIndex.nativeScalarColumn P D J T hr (IntegralMixedVirtualTaskBits.saved P q)

theorem columns_injective (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T) (q : List Bool) :
    Function.Injective (columns P D J T hr q) :=
  IntegralMixedFramedPhysicalIndex.nativeScalarColumn_injective P D J T hr _

theorem column_packet (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (q : List Bool) (i : Fin ((family P D J).arity q)) :
    IntegralMixedFramedFullScalarRowBits.columnReader P T (IntegralMixedVirtualTaskBits.saved P)
      (pair q (BinaryNatCode.encode i.val))=BinaryNatCode.encode (columns P D J T hr q i).val := by
  unfold IntegralMixedFramedFullScalarRowBits.columnReader columns IntegralMixedFramedPhysicalIndex.nativeScalarColumn
  simp only [pairFst_pair,pairSnd_pair]

noncomputable def fullPolynomial (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T) (q : List Bool) :=
  MvPolynomial.rename (columns P D J T hr q)
    ((family P D J).poweredPolynomial (fun q=>P.cap (RankedHistoryTask.root q)+1) q)

theorem columns_eq (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T) (q : List Bool) :
    columns P D J T hr q=(IntegralMixedFramedPhysicalIndex.enumerate (commands P D (IntegralMixedVirtualTaskBits.saved P q)))∘
      (IntegralMixedFramedOldHeightBits.state P D J q).sampler.scalar :=
  IntegralMixedFramedPhysicalIndex.nativeScalarColumn_eq P D J T hr _

theorem full_polynomial_height (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (q : List Bool) (hq : Active P q) :
    fullPolynomial P D J T hr q=MvPolynomial.rename
      (IntegralMixedFramedPhysicalIndex.enumerate (commands P D (IntegralMixedVirtualTaskBits.saved P q)))
      (IntegralHistorySampler.historyHeights (IntegralMixedFramedOldHeightBits.state P D J q).sampler
        (fun _ : Fin 1=>IntegralMixedHistory.expression (IntegralMixedFramedOldHeightBits.state P D J q)
          (IntegralMixedFramedScalarCellsBits.affine P D J q)) 0) := by
  rw [fullPolynomial,columns_eq,←MvPolynomial.rename_rename]
  apply congrArg (MvPolynomial.rename _)
  unfold IntegralHistorySampler.historyHeights
  apply congrArg (MvPolynomial.rename (IntegralMixedFramedOldHeightBits.state P D J q).sampler.scalar)
  have HC : (IntegralMixedFramedOldHeightBits.bankFamily P D J).cap (IntegralMixedVirtualTaskBits.saved P q)=P.cap (RankedHistoryTask.root q)+1 := by
    change P.cap (pairFst (IntegralMixedVirtualTaskBits.saved P q))+1=_
    rw [IntegralMixedFullHistoryFamilyBits.saved_root]
  change CoordinatePowerSubstitution.substitute _
    ((IntegralMixedFramedOldHeightBits.state P D J q).sampler.scalarPrefix.basis.representative
      (if Active P q then IntegralMixedHistory.expression (IntegralMixedFramedOldHeightBits.state P D J q)
        (IntegralMixedFramedScalarCellsBits.affine P D J q) else 0))=_
  rw [ite_eq_left hq]
  have HW:=congrArg (fun s=>UniformIntegralPowerSchedule.weights s
    (2^(IntegralMixedFramedOldHeightBits.bankFamily P D J).width (IntegralMixedVirtualTaskBits.saved P q))
    ((IntegralMixedFramedOldHeightBits.bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q))) HC.symm
  exact congrArg (fun w : Fin ((IntegralMixedFramedOldHeightBits.bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q))→ℕ=>
    CoordinatePowerSubstitution.substitute w
      ((IntegralMixedFramedOldHeightBits.state P D J q).sampler.scalarPrefix.basis.representative
        (IntegralMixedHistory.expression (IntegralMixedFramedOldHeightBits.state P D J q) (IntegralMixedFramedScalarCellsBits.affine P D J q)))) HW

theorem full_evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (IntegralMixedFramedFullScalarRowBits.fullCount P D (IntegralMixedVirtualTaskBits.saved P)) V
      (fullPolynomial P D J c.critical.tables c.critical.represents) target (modulusWord P)) := by
  have HK:=IntegralMixedVirtualTaskBits.saved_FP P a
  let N:=IntegralMixedFramedFullScalarRowBits.fullCount P D (IntegralMixedVirtualTaskBits.saved P)
  let index:=IntegralMixedFramedFullScalarRowBits.columnReader P c.critical.tables (IntegralMixedVirtualTaskBits.saved P)
  have HN : UnaryFn N:=IntegralMixedFramedFullScalarRowBits.fullCount_unary P a D J c.critical.tables
    c.critical.native c.critical.represents _ HK
  have HI : index∈FP:=IntegralMixedFramedFullScalarRowBits.columnReader_FP P a c.critical.tables c.critical.native _ HK
  exact FixedWidthEmbeddingBits.evaluator (family P D J).arity N V target index
    ((family P D J).poweredPolynomial (fun q=>P.cap (RankedHistoryTask.root q)+1))
    (columns P D J c.critical.tables c.critical.represents) (columns_injective P D J _ _)
    (column_packet P D J _ _) (modulusWord P) (arity_unary P a D J) HN hV ht HI
    (powered_evaluator P a D J c hb V hV _ (FixedWidthEmbeddingBits.word_FP _ _ _ _ _ (arity_unary P a D J) HN hV ht HI))

end LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightBits
