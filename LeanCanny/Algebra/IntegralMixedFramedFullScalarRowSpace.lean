/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedScalarColumnRows
public import LeanCanny.Algebra.IntegralMixedFramedRowSpace
public import LeanCanny.Algebra.FixedWidthEmbeddingSpace
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQCompanionSpace
/-! # Native full scalar-row coefficients include every critical physical block

The literal scalar-prefix equation is embedded by the native scalar-column
map. Non-scalar query exponents must vanish. The charged companion evaluator
remains the only algebraic computation used by the prefix-row kernel.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullScalarRowBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan commands family)
open IntegralMixedFramedPhysicalIndex
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def fullCount (P : Parameters) (D : Plan P) (key : List Bool→List Bool) (q : List Bool) := arity (commands P D (key q))

theorem count_eq (P : Parameters) (D : Plan P) (key : List Bool→List Bool) (q : List Bool) :
    IntegralMixedFramedRowBits.count P key q=(commands P D (key q)).length := by
  rw [commands,IntegralMixedFramedHistoryScript.paddedPast_length]
  rfl

theorem fullCount_unary (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : IntegralMixedHeaderTablesBits.Tables)
    (ht : IntegralMixedHeaderTablesBits.Access T) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (key : List Bool→List Bool) (hk : key∈FP) : UnaryFn (fullCount P D key) := by
  have HC:=IntegralMixedFramedRowBits.count_unary P a key hk
  have HE: (fun q=>pair (key q) (List.replicate (IntegralMixedFramedRowBits.count P key q) true))∈FP :=
    mem_FP_pair hk HC.mem_FP
  apply ((prefixArity_unary P a T ht).comp HE).of_eq
  intro q
  rw [prefixArity_packet P D J T hr]
  rw [count_eq P D key q]
  unfold fullCount commands
  rw [IntegralMixedFramedHistoryScript.paddedPast_length]

def columnReader (P : Parameters) (T : IntegralMixedHeaderTablesBits.Tables)
    (key : List Bool→List Bool) (p : List Bool) :=
  BinaryNatCode.encode (scalarColumn P T (pair (key (pairFst p)) (pairSnd p)))

theorem columnReader_FP (P : Parameters) (a : Access P) (T : IntegralMixedHeaderTablesBits.Tables)
    (ht : IntegralMixedHeaderTablesBits.Access T) (key : List Bool→List Bool) (hk : key∈FP) :
    columnReader P T key∈FP :=
  by
    have HI : BinaryFn (fun p=>scalarColumn P T (pair (key (pairFst p)) (pairSnd p))) :=
      (BinaryFn.ofUnary (scalarColumn_unary P a T ht)).comp
        (mem_FP_pair (mem_FP_comp pairFst_mem_FP hk) pairSnd_mem_FP)
    exact HI.bits_mem_FP

noncomputable def columns (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (key : List Bool→List Bool) (q : List Bool) : Fin (IntegralMixedFramedRowBits.count P key q)→Fin (fullCount P D key q) :=
  fun i=>nativeScalarColumn P D J T hr (key q) (Fin.cast (count_eq P D key q) i)

theorem columns_injective (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (key : List Bool→List Bool) (q : List Bool) : Function.Injective (columns P D J T hr key q) :=
  (nativeScalarColumn_injective P D J T hr (key q)).comp (Fin.cast_injective _)

theorem columnReader_packet (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (key : List Bool→List Bool) (q : List Bool) (i : Fin (IntegralMixedFramedRowBits.count P key q)) :
    columnReader P T key (pair q (BinaryNatCode.encode i.val))=BinaryNatCode.encode (columns P D J T hr key q i).val := by
  simp only [columnReader,pairFst_pair,pairSnd_pair,columns,nativeScalarColumn,Fin.val_cast]

noncomputable def polynomial (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (key index : List Bool→List Bool) (hpos : ∀q,0<IntegralMixedFramedRowBits.count P key q) (q : List Bool) :=
  MvPolynomial.rename (columns P D J T hr key q) (IntegralMixedFramedRowBits.polynomial P D J key index hpos q)

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P D J T) (key index target modulus : List Bool→List Bool)
    (hpos : ∀q,0<IntegralMixedFramedRowBits.count P key q) (V : List Bool→ℕ)
    (hk : key∈FP) (hi : index∈FP) (hV : UnaryFn V) (htarget : target∈FP) (hm : modulus∈FP)
    (E : SpaceFunction (PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D J))) :
    SpaceFunction (FixedWidthRowBits.value (fullCount P D key) V (polynomial P D J T hr key index hpos) target modulus) := by
  have HA:=IntegralMixedFramedRowBits.count_unary P a key hk
  have HN:=fullCount_unary P a D J T ht hr key hk
  have HC:=columnReader_FP P a T ht key hk
  have HW:=FixedWidthEmbeddingBits.word_FP (IntegralMixedFramedRowBits.count P key) (fullCount P D key) V target
    (columnReader P T key) HA HN hV htarget HC
  have EP:=IntegralMixedFramedRowBits.polynomial_evaluator P a D J key index _ modulus hpos V hk hi hV HW hm E
  exact FixedWidthEmbeddingBits.evaluator (IntegralMixedFramedRowBits.count P key) (fullCount P D key) V target
    (columnReader P T key) (IntegralMixedFramedRowBits.polynomial P D J key index hpos)
    (columns P D J T hr key) (columns_injective P D J T hr key) (columnReader_packet P D J T hr key)
    modulus HA HN hV htarget HC EP

private theorem rename_transport {a b N : ℕ} (h : a=b)
    (g : Fin b→Fin N) (p : MvPolynomial (Fin a) ℤ) (q : MvPolynomial (Fin b) ℤ)
    (hp : HEq p q) : MvPolynomial.rename (fun i=>g (Fin.cast h i)) p=MvPolynomial.rename g q := by
  cases h
  cases hp
  rfl

theorem polynomial_actual (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (key index : List Bool→List Bool) (hpos : ∀q,0<IntegralMixedFramedRowBits.count P key q) (q : List Bool) :
    polynomial P D J T hr key index hpos q=
      PolynomialSystemReindex.system (enumerate (commands P D (key q))) ((family P D J).state (key q)).sampler.rows
        (nativeScalarColumn P D J T hr (key q) (IntegralMixedFramedRowBits.selectedIndex P D J key index hpos q)) := by
  have HP:=IntegralMixedFramedRowBits.polynomial_actual P D J key index hpos q
  have HE:=rename_transport (count_eq P D key q) (nativeScalarColumn P D J T hr (key q))
    (IntegralMixedFramedRowBits.polynomial P D J key index hpos q)
    (((family P D J).state (key q)).sampler.scalarPrefix.rows
      (IntegralMixedFramedRowBits.selectedIndex P D J key index hpos q)) HP
  exact HE.trans (native_scalar_row P D J T hr (key q) (IntegralMixedFramedRowBits.selectedIndex P D J key index hpos q)).symm

theorem currentQ_evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P D J T) (key index target modulus : List Bool→List Bool)
    (hpos : ∀q,0<IntegralMixedFramedRowBits.count P key q) (V : List Bool→ℕ)
    (hk : key∈FP) (hi : index∈FP) (hV : UnaryFn V) (htarget : target∈FP) (hm : modulus∈FP)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCompanionUniformBits.lifted P)
      (IntegralMixedFramedCompanionUniformBits.liftedPlan P D) Hnew c) :
    SpaceFunction (FixedWidthRowBits.value (fullCount P D key) V (polynomial P D J T hr key index hpos) target modulus) :=
  evaluator P a D J T ht hr key index target modulus hpos V hk hi hV htarget hm
    (IntegralMixedFramedCurrentQCompanionBits.evaluator P a D J Hnew c hb)

end LeanCanny.Algebra.IntegralMixedFramedFullScalarRowBits
